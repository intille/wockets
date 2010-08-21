<?php

include_once("../dataupload/upload_functions.php");
set_time_limit(0);

// Using the POST parameters retrieve the UUID and targetPath
$fileMeta = getUUID( $_FILES['sendfile']['name'] );
$uuid = $fileMeta['uuid'];
$targetPath = $fileMeta['targetPath'];
$params = array( "rangeStart" => 0, 
					"rangeEnd"   => ((int)$_FILES['sendfile']['size'])-1, 
					"length"     => (int)$_FILES['sendfile']['size'], 
					"uuid" 		 => $uuid, 
					"targetPath" => $targetPath );


// Connecto the DB and process the uplxoaded file
$dbhandle = initDB();

// If corresponding file's UUID is already locked do nothing:
//if( upload_isFileLocked($uuid) )
//	exit( "Error file is already locked. Cannot upload!" );

// Process the uploaded file
if( empty($_FILES) ) 
	pushStatsToDB($params, "ERROR: FILES variable is empty, POST too large?" );
else {
	switch( $_FILES['sendfile']['error']) {
		case UPLOAD_ERR_OK:
			// Check if we're going to overwrite a file:
			//if( file_exists($fileMeta['targetPath']) )
			//	exit( "ERROR: Filename already exists cannot upload!" );
			
			// This is the only success case, so long as this move works the file was uploaded OK
			if( move_uploaded_file($_FILES['sendfile']['tmp_name'], $fileMeta['targetPath']) ) {
				// Store the upload time and lock the file
				$updateQuery = "UPDATE uploaded_files SET uploadedTimestamp=NOW(), status='Uploaded Successfully', locked=1 WHERE uuid = UNHEX('$uuid');";
				if($updateQuery != "")	
					mysql_query($updateQuery) or die(mysql_error());

				// Make a note in the log				
				pushStatsToDB($params, "Upload Complete", "" );
				
				// Compute the hash table:
				$checksum = compute_checksum($targetPath);
				$updateQuery = "UPDATE uploaded_files SET md5sum='$checksum' WHERE uuid = UNHEX('$uuid');";
				mysql_query($updateQuery) or die(mysql_error());
				
				// Return the status:
				header("HTTP/1.1 200 OK");
				echo $checksum;
			} else{
				header("HTTP/1.1 500 Internal Server Error");
				$errorString = serialize(error_get_last());
				$statusQuery = "INSERT INTO uploaded_files_log (uuid,targetPath,timestamp,event,ranges,data) ".
							   "VALUES('$uuid','$targetPath',NOW(),'Move File Failed','$rangeString','Error: $errorString');";
				mysql_query($statusQuery) or die(mysql_error());
			    echo "ERROR: There was an error uploading the file, please try again!";
			}
			break;
		case UPLOAD_ERR_INI_SIZE:
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "Uploaded file exceeds upload_max_filesize" );
			break;
		case UPLOAD_ERR_FORM_SIZE:
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "Uploaded file exceeds max_file_size" );
			break;
		case UPLOAD_ERR_PARTIAL:
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "Partial file upload", "ERROR: Partial file upload - $rangeString" );
		    break;
		case UPLOAD_ERR_NO_FILE:
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "No file sent" );
		    break;
		case UPLOAD_ERR_NO_TMP_DIR:
			// This is a system error (/tmp is full or missing?)
			// TODO: This error should trigger an admin e-mail
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "No temporary directory available" );
		    break;
		case UPLOAD_ERR_CANT_WRITE:
			// This is a system error (disk full?)
			// TODO: This error should trigger an admin e-mail
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "Disk failure while writing" );
		    break;
		case UPLOAD_ERR_EXTENSION:
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "Extension stopped upload" );
		    break;
		default:
			header("HTTP/1.1 500 Internal Server Error");
			pushStatsToDB($params, "Unknown upload error" );
			break;
	}
}

mysql_close($dbhandle);

function pushStatsToDB($params,$msg, $msgPrint=".") {
	$uuid = $params['uuid'];
	$targetPath = $params['targetPath'];
	$rangeStart = $params['rangeStart'];
	$rangeEnd = $params['rangeEnd'];
	$length = $params['length'];

	$statusQuery = "INSERT INTO uploaded_files_log ".
				   "      (  uuid,   targetPath, timestamp, event,  rangeStart,   rangeEnd,   length) ".
				   "VALUES('$uuid','$targetPath',NOW(),    '$msg','$rangeStart','$rangeEnd','$length');";
	mysql_query($statusQuery) or die(mysql_error());
	if( $msgPrint!="." )
		echo "$msgPrint";
	else
		echo "ERROR: $msg";	
}


?>