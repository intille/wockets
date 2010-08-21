<?php
function getUUID_data($uuid) {
	$uuid = mysql_real_escape_string($uuid);
	$selectQuery = "SELECT targetPath,status,md5sum,md5sum_expected,length,locked,HEX(uuid) AS uuid FROM uploaded_files WHERE uuid = UNHEX('$uuid');";
	$result = mysql_query($selectQuery);
	if( $result == false )
		exit( "Invalid UUID" );
	$row = mysql_fetch_assoc($result);
	return $row;
}

// TODO: Overwrite behavior (should check for file exists before adding a SQL row)
//      
function getUUID($uploadedFilename) {
	set_time_limit(0);
	include_once($_SERVER['DOCUMENT_ROOT']."/initDB.php");
	require_once($_SERVER['DOCUMENT_ROOT']."/settings.inc");
	
	
	
	//------------------------------------------------------------
	// Retrieve POST variables:
	$project 	  = escapeshellcmd($_POST['project']);
	$subjectID 	  = escapeshellcmd($_POST['subject_id']);
	$dataType 	  = escapeshellcmd($_POST['data_type']);
	$dateString   = escapeshellcmd($_POST['date_string']);
	$appID 		  = escapeshellcmd($_POST['app_id']);
	$recvUnixTime = escapeshellcmd($_POST['unix_time']);
	$debugMode 	  = escapeshellcmd($_POST['debug']);
	$notes 		  = escapeshellcmd($_POST['notes']);
	
	
	
	//------------------------------------------------------------
	// Error checking
	global $data_store;
	if( !file_exists( $data_store."/".$project ) )
		exit( "Error: Unknown project: $project ($data_store./.$project)" );
	
	if( !isset($_POST['subject_id']) || $subjectID == "" )
		exit( "Error: Subject ID cannot be blank!" );
	
	if( (strlen($recvUnixTime)!=13) && !is_numeric($$recvUnixTime) )
		exit( "Error: Unix time must be a 13 digit integer number, unix time * 1000 + milliseonds" );
	
	switch( $dataType ) {
		case "client_log":
		case "raw_data":
			break;
		default:
			exit( "Error: Unknown data type: $dataType" );
			break;
	}
	
	if( !isset($_POST['notes']) )
		$notes = "";
	
	if( strlen($dateString) != 29 )
		exit( sprintf( "Error: date_string must be a 29 character string of the form (a la ISO_8601 format): [YYYY]-[MM]-[DD] [hh]:[mm].[ss].[FFF]+ZZ:ZZ, current length: %d", strlen($dateString))  );
	
	
	
	//------------------------------------------------------------
	// Process the date, unix time is stored with the GMT offset applied
	$unixTime_UTC = $recvUnixTime;
	$gmt = sscanf(substr($dateString,-6), "%d:%d" );
	$gmtOffset = $gmt[0]*60*60*1000 + $gmt[1]*60*1000;
	//print_r($gmt);
	//printf("\nGMT Offset: %d\n", $gmtOffset );
	$unixTime_deviceLocal = $recvUnixTime + $gmtOffset;
	$unixTime_deviceLocal_year  = date("Y", $unixTime_deviceLocal/1000);
	$unixTime_deviceLocal_month = date("m", $unixTime_deviceLocal/1000);
	$unixTime_deviceLocal_day   = date("d", $unixTime_deviceLocal/1000);
	
	
	
	//------------------------------------------------------------
	// Determine the destination for the file:
	$target_path = $data_store."/".$project."/subject_data/".$subjectID;
	if( file_exists($targetPath) )
		exit( "ERROR: File exists" );
	$date_path   = sprintf("%s/%s/%s",$unixTime_deviceLocal_year, $unixTime_deviceLocal_month, $unixTime_deviceLocal_day );
	if( $appID == "")
		$date_path = sprintf( "%s", $date_path );
	else
		$date_path = sprintf( "%s/%s", $date_path, $appID );
	switch($dataType){
		case "raw_data":
			$dataTypeString = $dataType;
			break;
		case "client_log":
			$dataTypeString = "summary_data";
			break;
		default:
			exit("Error: Data type unknown.");
			break;
	}
	$target_path = sprintf("%s/%s/%s", $target_path, $dataTypeString, $date_path );
	//echo "<pre>";
	//printf("Data will be stored in: %s\n\n", $target_path );
	
	
	
	
	//------------------------------------------------------------
	// Process the uploaded files:
	if($debugMode == 1)
		echo $target_path. "<br>";
	
	// create path
	if (!mkdir_recursive($target_path, 0644)) {
	    die('Error: Failed to create folders...');
	}
	
	$target_path = $target_path . "/" . $uploadedFilename; 

	// Connect to the DB and select the table, make sure you close connection when done
	$dbhandle = initDB();
	// Escape everyone to prevent any obvious SQL POST injection attacks
	$project      = mysql_real_escape_string($project     );
    $subjectID    = mysql_real_escape_string($subjectID   );
    $dataType     = mysql_real_escape_string($dataType    );
    $appID        = mysql_real_escape_string($appID       );
    $dateString   = mysql_real_escape_string($dateString  );
    $recvUnixTime = mysql_real_escape_string($recvUnixTime);
    $gmtOffset    = mysql_real_escape_string($gmtOffset   );
    $notes        = mysql_real_escape_string($notes       );
	$existQuery = "SELECT id FROM uploaded_files WHERE 
					project      = '$project'       AND 
					subjectID    = '$subjectID'     AND
					dataType     = '$dataType'      AND
					appID        = '$appID'         AND
					dateString   = '$dateString'    AND
					recvUnixTime = '$recvUnixTime'  AND
					gmtOffset    = '$gmtOffset'     AND
					notes        = '$notes';";
	$result = mysql_query($existQuery);
	$row = mysql_fetch_assoc($result);
	if( empty($row) ) {
		// This combination doesn't exist so add a row into the database:
		$insertQuery = "INSERT INTO uploaded_files ".
			            "(project,   subjectID,   dataType,   appID,   dateString,   recvUnixTime,   gmtOffset,   notes,   targetPath,                uuid,           serverTimestamp ) ".
	    		"VALUES('$project','$subjectID','$dataType','$appID','$dateString','$recvUnixTime','$gmtOffset','$notes','$target_path',UNHEX(REPLACE(UUID(),'-','')),NOW()           );";

		if($insertQuery != "")	
			mysql_query($insertQuery) or die(mysql_error());
			
		// Retrieve back the ID we just created:
		$sqlID = mysql_insert_id();
	}
	else {
		// Entry already exists so retrieve it's row ID
		$sqlID = $row['id'];
	}
	
	// Now get and print the UUID and stored targetPath
	$selectQuery = "SELECT targetPath, HEX(uuid) AS uuid FROM uploaded_files WHERE id = '$sqlID';";
	$result = mysql_query($selectQuery);
	$row = mysql_fetch_assoc($result);

	$returnVar = array('uuid' => $row['uuid'], 'targetPath' => $row['targetPath'] );

	if( false ) {
		echo "<pre>";
		printf("\n");
		printf( "UUID: %s\n", $row['uuid'] );
		printf( "targetPath: %s\n", $row['targetPath']);
	}

    return $returnVar;
}


/**
 * Check if a UUID is locked (locked is greater than 0). Requires an exsisting DB connection
 *
 * @param string $uuid Unique Identifier for a uploaded_files row
 * @return boolean returns TRUE when the UUID is valid and the file is locked FALSE when the file is not locked or the UUID is invalid
 */
function upload_isFileLocked( $uuid ) {
	// If corresponding file's UUID is already locked do nothing:
	$statusQuery = "SELECT locked FROM uploaded_files WHERE uuid = UNHEX('$uuid');";
	if($statusQuery != "")	
		$result = mysql_query($statusQuery) or die(mysql_error());
	if( $result == false )
		return false;
	$row = mysql_fetch_assoc($result);
	if( $row['locked'] >= 1 )
		return true;
	else
		return false;
}


function compute_checksum($targetPath) {
	$md5sum = hash_init('md5');	
	$file = fopen($targetPath,'rb');
	while( $file && !feof($file) ) {
	    $data = fread( $file, 8192 );
	    hash_update($md5sum,$data);
	}
	$checksum = hash_final($md5sum);
	return $checksum;
}

/**
 * Makes directory, returns TRUE if exists or made
 *
 * @param string $pathname The directory path.
 * @return boolean returns TRUE if exists or made or FALSE on failure.
 */
function mkdir_recursive($pathname, $mode)
{
    is_dir(dirname($pathname)) || mkdir_recursive(dirname($pathname), $mode);
    return is_dir($pathname) || @mkdir($pathname, $mode);
}

?>