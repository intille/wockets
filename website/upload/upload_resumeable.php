<?php
/**
 * This function provides a resumeable uploading function. 
 * 
 * Features:
 *  - Upload location and locking are handled by backend DB and getUUID() logic
 *  - Files are locked once the provided md5sum is reached
 *  - Uploads can resume any part of a file
 *  - Upload chunk sizes are controlled entirely by the user, you can upload 10k at a time or 100MB at a time
 *
 * Procedure:
 *  1) Initate an upload, specifying the required parameters and a target MD5sum
 *     - the UUID returned by this process is the key for accessing this file
 *  2) Query the UUID to see how much data has been uploaded
 *  3) Upload data starting from the next byte up until the end of the file
 *     - If this process is interrupted return to step 2 and repeat
 *     - Once a file reaches it's targe size. It's MD5 checksum is computed. If the file matches it is
 *       locked (it can no longer have data uploaded to it)
 *
 * Assumptions:
 *  - Uploads will likely be done in 1 shot or continuously interrupted. It is suggested to use increasingly
 *    larger upload chunks up to some ceiling
 *    i.e. start with 10k, then a 100k, 200k, 300k, 300k, etc.
 *         on EDGE this might be more like 1k, 3k, 10k, 50k, 100k, 100k, 100k
 *    This way you will usually make some progress with each attempt even if the upload is always interrupted
 *  - Once a file matches it's checksum it is locked to prevent malicious and accidental corruption/overwriting
 *
 * Specifying a file to upload:
 *  - Send a POST with: 
 *    - parameters getUUID() needs
 *    - 'sendfile: [filename]'
 *    - 'X-Upload-Content-Length: [fileLength]'
 *    - 'X-Upload-md5sum: [checksum]'
 *  - Server '308 Resume Incomplete' response header contains:
 *    - 'UUID: [uuid]'
 *    - 'Content-Length: 0'
 *    - 'Range: 0-0'
 *  - Server internal actions:
 *    - File is created at 'targetPath'
 *    - DB contains an entry for a partial file
 * 
 * Status checking:
 *  - Client sends a POST with:
 *    - 'UUID: [uuid]'
 *    - 'Content-Length: 0'
 *    - 'Content-Range: bytes *[/][filesize]'
 *      in place of '*[/]' send 'star slash' this messes up the PHP
 *  - INCOMPLETE FILE: Server respond with '308 Resume Incomplete' and the following header information:
 *    - 'UUID: [uuid]'
 *    - 'Content-Length: 0'
 *    - 'Range 0-[lastByteRecieved]'
 *  - COMPLETE FILE: Server respond with '200 OK' and the following header information:
 *    - 'UUID: [uuid]'
 *    - 'Content-Length: [length of file recieved]'
 *    - 'Range 0-[length of file]'
 *    - 'md5sum: [md5sum of server file recieved]'
 *    - 'fileIsLocked: true'
 *
 * Uploading a chunk of data:
 *  - Client sends a POST with:
 *    - 'UUID: [uuid]'
 *    - 'Content-Length: [uploadSize]'
 *    - 'Content-Range: bytes [firstByte]-[lastByte]/[filesize]'
 *    - A set of files seperated into chunks you should preferably name them
 *      uploadedfile.part.XXXX 
 *
 * On successful upload:
 *  - Server responds with '200 OK'
 *    - 'UUID: [uuid]'
 *    - 'md5sum: [md5sum of server file recieved]'
 *    - 'Content-Length: [length of file recieved]'
 *    - 'fileIsLocked: true'
 *
 *
 * This code implements a protocol similar to the one described in:
 * http://code.google.com/p/gears/wiki/ResumableHttpRequestsProposal
 *
 * Differences:
 *  - The Google setup assumes you send a request to a new location to specify your upload. Instead 
 *    we use the same upload_resumable.php page. And the user specified a UUID in the POST headers 
 *  - We do not use ETags or If-Match (the UUID is similar to If-Match... but not exactly)
 *  - Authorization/Google specifics aren't done, instead we do our own POST
 *  - MD5sum is used extensively to prevent corrupt (uploads are expected to be problematic over
 *    the cellular network)
 **/


//$requireSSL = true;
// If page requires SSL, and we're not in SSL mode, 
// redirect to the SSL version of the page
//if($requireSSL && $_SERVER['SERVER_PORT'] != 443) {
//   header("HTTP/1.1 301 Moved Permanently");
//   header("Location: https://".$_SERVER['HTTP_HOST'].$_SERVER['REQUEST_URI']);
//   exit("SSL required");
//}

// Connect to the DB
include_once($_SERVER['DOCUMENT_ROOT']."/initDB.php");
include_once($_SERVER['DOCUMENT_ROOT']."/settings.inc");
include_once("../dataupload/upload_functions.php");
$dbhandle = initDB();
register_shutdown_function('mysql_close',$dbhandle);


//------------------------------------------------------------
// Process the user request:
if( isset($_POST['X-Upload-Content-Length']) && isset($_POST['X-Upload-md5sum']) && isset($_POST['sendfile']) ) {
	// New file to upload:
	$fileMeta = getUUID(escapeshellcmd($_POST['sendfile']));
	$uuid = $fileMeta['uuid'];
	// Store the user specified size and checksum:
	$UploadContentLength = mysql_real_escape_string(escapeshellcmd($_POST['X-Upload-Content-Length']));
	$UploadMD5sum        = mysql_real_escape_string(escapeshellcmd($_POST['X-Upload-md5sum']));
	$updateQuery = "UPDATE uploaded_files SET length='$UploadContentLength', md5sum_expected='$UploadMD5sum' WHERE uuid = UNHEX('$uuid');";
	mysql_query($updateQuery) or die(mysql_error());

	$targetPath = $fileMeta['targetPath'];					// Location on the filesystem
	$targetPath_statusFile = $targetPath.".IS_UPLOADING";	// Indicator for the file being in progress
//	echo "<pre>";
//	print_r($targetPath);
//	printf("\n");
//	print_r($targetPath_statusFile);
	// Create the file if it doesn't exist
	if( !file_exists($targetPath) ) {
	    fclose(fopen($targetPath,"wb"));
	}
	// Create a status file to let us know the file is uploading
	if( !file_exists($targetPath_statusFile)) {
	    fclose(fopen($targetPath_statusFile,"wb"));
	}

	// Return the user info:
	header( "HTTP/1.1 308 Resume Incomplete" );
	header( "UUID: $uuid" );
	header( "Content-Length: 0" );
	header( "Range: 0-0");	
	exit();
}
else if( isset($_POST['Content-Length']) && isset($_POST['Content-Range']) && isset($_POST['uuid']) ){
	$uuid = escapeshellcmd($_POST['uuid']);
	$ContentRange  = escapeshellcmd($_POST['Content-Range'] );
	$ContentLength = escapeshellcmd($_POST['Content-Length']);

	// Get data from DB:
	$row = getUUID_data($uuid);
	$targetPath = $row['targetPath'];						// Location on the filesystem
	$targetPath_statusFile = $targetPath.".IS_UPLOADING";	// Indicator for the file being in progress
	
	
	// This is a status request checking to see how much of this file we have recieved:
	if( ((int)$ContentLength) == 0 && strpos($ContentRange,'*/') != false ) {
		send_fileStatus_response($targetPath,$row);
		exit();
	}
	// This must be an upload request:
	else {
		// Is the file locked?
		if( $row['locked'] ) {
			$msg = "Upload Attempt Ignored";
			$data= serialize($_FILES);
		   	$statusQuery = "INSERT INTO uploaded_files_log ".
		   				   "      (  uuid,   targetPath, timestamp, event,  rangeStart,   rangeEnd,   length,   data) ".
		   	   			   "VALUES('$uuid','$targetPath',NOW(),    '$msg','$rangeStart','$rangeEnd','$length','$data');";
		    mysql_query($statusQuery) or die(mysql_error());			
			exit( "ERROR: File is already complete, upload request ignored!" );
		}

		$results = sscanf( $ContentRange, "bytes %d-%d/%d" );
		$startByte = $results[0];
		$endByte   = $results[1];
		$length    = $results[2];
		
		// Create the file if it doesn't exist
		if( !file_exists($targetPath) ) {
		    fclose(fopen($targetPath,"wb"));
		}
		// Create a status file to let us know the file is uploading
		if( !file_exists($targetPath_statusFile)) {
		    fclose(fopen($targetPath_statusFile,"wb"));
		}
		
		if( $startByte > filesize($targetPath) ) 
		    exit( "Inavlid start length, received file isn't that long" );
		if( $endByte >= $length ) {
			print_r($_POST);
			printf( "%d versus %d\n", $endByte, $length);
		    exit( "Inavlid end length, exceeds file length" );
		}
		
		// Open the file to the new byte:
		$fileOut = fopen($targetPath, "r+b");
		fseek( $fileOut, $startByte, SEEK_SET );
		
		// Read data into the output until we run out of files or there's an error
		foreach($_FILES as $file) {
		    switch( $file['error'] ){
		    	case UPLOAD_ERR_OK:
		    		$sourceFile = fopen($file['tmp_name'], 'rb');
		    		if( $sourceFile == false )
		    			exit("Unable to open temporary file");
		    		$rangeStart = ftell($fileOut); 
		    		while( $sourceFile && !feof($sourceFile) ) {
		    			fwrite( $fileOut, fread($sourceFile,8192) );
		    		}
		    		fclose($sourceFile);
		    		$rangeEnd = ftell($fileOut);
		    		$length = $file['size'];
		    		
		    		$msg = "Partial Upload integrated";
		    		$statusQuery = "INSERT INTO uploaded_files_log ".
		    					   "      (  uuid,   targetPath, timestamp, event,  rangeStart,   rangeEnd,   length) ".
		    		   			   "VALUES('$uuid','$targetPath',NOW(),    '$msg','$rangeStart','$rangeEnd','$length');";
		    		mysql_query($statusQuery) or die(mysql_error());
		    		break;
		    	default:
		    		fclose($fileOut);
		    		$msg = "Incomplete upload error code: ".$file['error'];
		    		$statusQuery = "INSERT INTO uploaded_files_log ".
		    					   "      (  uuid,   targetPath, timestamp, event,  rangeStart,   rangeEnd,   length) ".
		    		   			   "VALUES('$uuid','$targetPath',NOW(),    '$msg','$rangeStart','$rangeEnd','$length');";
		    		mysql_query($statusQuery) or die(mysql_error());
		    		exit("Incomplete file encountered aborting");
		    		break;
		    }
		}
		// Truncate the file to the length specified by the user:
		// TODO: This is slightly dangerous... as someone malicious could erase data
		//       Then again someone could also upload new data and overwrite anything
		ftruncate( $fileOut, $row['length'] );
		fflush($fileOut);
		fclose($fileOut);
		
		send_fileStatus_response($targetPath,$row);
	}
	exit();
}
else {
	exit( "ERROR: Invalid Request" );
}


function send_fileStatus_response($targetPath,$row) {
//	print_r($row);
//	printf( "value is %s", $row['md5sum_expected'] );
	if( lockfile_if_done($targetPath,$row['locked'],$row['length'],$row['md5sum_expected'],$row['uuid']) ) {
	    // Done uploading
	    header( "HTTP/1.1 200 OK" );
	    header( "UUID: $uuid" );
	    header( sprintf("Content-Length: %d", $row['length']) );
	    header( sprintf("Range: 0-%d", $row['length']) );
	    header( sprintf("md5sum: %s", $row['md5sum_expected']) );
	    header( "fileIsLocked: true" );
	}
	else {
	    // Still in progress:
	    header( "HTTP/1.1 308 Resume Incomplete" );
	    header( "UUID: $uuid" );
	    header( "Content-Length: 0" );
	    $recvSize = filesize($targetPath);
	    header( sprintf("Range: 0-%d", $recvSize) );
	}
}


function lockfile_if_done($targetPath,$locked,$length,$md5sum_expected,$uuid) {
//printf("File exists: %d\n", file_exists($targetPath) );
//	if( !file_exists($targetPath) )
//		$recvSize = 0;
//	else
		$recvSize = filesize($targetPath);
//printf("File name  : %s\n", $targetPath );
//printf("File length: %s\n", $length );
//printf("File length: %d\n", $length );
//printf("File size:   %d\n", $recvSize );
//printf("File locked: %d\n", $locked );
	if( $locked ) {
		return true;
	}

	// Check if we should lock the file:	
//	if( $recvSize == $length ) {
		// File length appears done, check the checksum:
		$checksum = compute_checksum($targetPath);
//printf("File checksum:   %s\n", $md5sum_expected );
//printf("Server checksum: %s\n", $checksum );

		if( strcmp($md5sum_expected,$checksum)==0 ) {
			// File is done:
			$updateQuery = "UPDATE uploaded_files SET md5sum='$checksum',locked=1,status='Uploaded Successfully' WHERE uuid = UNHEX('$uuid');";
			mysql_query($updateQuery) or die(mysql_error());
			$msg = "Upload Complete";
		   	$statusQuery = "INSERT INTO uploaded_files_log ".
		   				   "      (  uuid,   targetPath, timestamp, event,  rangeStart,   rangeEnd,   length) ".
		   	   			   "VALUES('$uuid','$targetPath',NOW(),    '$msg','$rangeStart','$rangeEnd','$length');";
		    mysql_query($statusQuery) or die(mysql_error());			
			$targetPath_statusFile = $targetPath.".IS_UPLOADING";	// Indicator for the file being in progress
//printf("Lock file: %s\n", $targetPath_statusFile );
			unlink($targetPath_statusFile);
			return true;
		}
		else {
			$msg = "File size equals length, but checksum does not match";
			$data = $checksum;
		   	$statusQuery = "INSERT INTO uploaded_files_log ".
		   				   "      (  uuid,   targetPath, timestamp, event,  rangeStart,   rangeEnd,   length,   data) ".
		   	   			   "VALUES('$uuid','$targetPath',NOW(),    '$msg','$rangeStart','$rangeEnd','$length','$checksum');";
		    mysql_query($statusQuery) or die(mysql_error());			
			return false;
		}
//	}
	
//	return false;
}

?>
