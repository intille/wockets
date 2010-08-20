<?php

include("initDB.php");

//connect to DB, those who opened it has to be responsible closing it using the returned dbhandle.
$dbhandle = initializeDB("wockets+wockets");

/*
$start_unixtime = "1277640459011";
$end_unixtime = "1279221344000";
$reqRange = 0;
$currentSubject = 1;
$showScores = "true";
$showAnnotation = "true";
$showUsageData = "true";
*/

// request range data

$start_unixtime = $_GET['start_unixtime'];
$end_unixtime = $_GET['end_unixtime'];
$reqRange = $_GET['reqRange'];

$currentSubject = $_GET['subjectid'];


// request param list

$showScores = $_GET['score'];
$showAnnotation = $_GET['annotation'];
$showUsageData = $_GET['usageData'];


// activity, when no activity provide 
$scoresData = array();

if($showScores == "true")
{
	$scoresData = getScoresData($start_unixtime, $end_unixtime, $reqRange, $currentSubject);
}else
{
	// dummy activity to host labels
	$outputArray[0] = array($start_unixtime, 0);
	$outputArray[1] = array($end_unixtime, 0);
	
	$scoresData = $outputArray;
}


// simple food tracking
$annotationData = array();

if($showAnnotation == "true"){
	//$annotationData = getAnnotationData($start_unixtime, $end_unixtime, $reqRange, $currentSubject);
}

// reviewer on plot notes
$usageData = array();

if($showUsageData == "true"){
	$usageData = getUsageData($start_unixtime, $end_unixtime, $reqRange, $currentSubject);
}



$jsonToReturn = array("meta"=>array("checkedTime"=>"1272772814000", "uploadedTime"=>"1272427243000"),"numeric" => $scoresData, "annotation"=> array($annotationData), "onplotnotes"=> array($usageData));

//$jsonToReturn = array("meta"=>array("checkedTime"=>"1272772814000", "uploadedTime"=>"1272427243000"),"numeric" => array($scoresData), "annotation"=> array(array ("label"=>"FRU","data"=>array(array(1231558980000, "One fruit"), array(1231858980000, "Two fruits"), array(1230908980000, "Three fruits"), array(1230958980000, "Four Fruits"))), array ("label"=>"JUI","data"=>array(array(1232558980000, "One juice"), array(1231218980000, "Two juice"), array(1241158980000, "Three juice"), array(1232558980000, "Four juice")))));

echo json_encode($jsonToReturn);

closeDB($dbhandle);


function getScoresData($start_unixtime, $end_unixtime, $reqRange, $currentSubject)
{
	/*
	switch($reqRange)
	{
		case 0:
			$query = "SELECT * FROM stepLively_activity WHERE subject_id = '".$currentSubject."' and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." order by date_time";
			break;
		case 1:
			$query = "Select subject_id, unix_time, avg(score) from stepLively_activity where subject_id = '". $currentSubject ."' and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." group by subject_id, HOUR(date_time), DATE(date_time) order by date_time";
			//$query = "SELECT * FROM activity_hour_view WHERE subject_id = '".$currentSubject."' and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." order by date_time";
			break;
		case 2:
			$query = "Select subject_id, unix_time, avg(score) from stepLively_activity where subject_id = '". $currentSubject ."' and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." group by subject_id, DATE(date_time) order by date_time";
			//$query = "SELECT * FROM activity_day_view WHERE subject_id = '".$currentSubject."' and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." order by date_time";
			break;
	}
	*/
	
	$query = "SELECT * FROM wockets_transmission_log WHERE subject_id = '".$currentSubject."' and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." order by date_time";
	
	//execute the SQL query and return records
	$result = mysql_query($query) or die(mysql_error());
	
	$numRows = mysql_num_rows($result);
	
	// adjust unix time
	$unix_time = $row["unix_time"];
	
	$arrayIndex = 1;
	
	$outputArray[] = null;	
	$outputArray2[] = null;

	
	//insert dummy to diplay timeline properly
	$outputArray[0] = array($start_unixtime, '0');
	$outputArray2[0] = array($start_unixtime, '0');
	
	$first_entry = true;
	
	//display the activityresults
	while($row = mysql_fetch_array($result))
	{
		/*
		if($reqRange == 0)
		{
			$outputArray[$arrayIndex] = array($row["unix_time"], $row["score"]);
		}else
		{
			$outputArray[$arrayIndex] = array($row["unix_time"], $row["avg(score)"]);
		}
		*/
		
		//received_bytes
		
		if($first_entry){
			// pad a 0 before the first entry comes in.
			$outputArray[$arrayIndex] = array(($row["unix_time"]-1), '0');
			$outputArray2[$arrayIndex] = array(($row["unix_time"]-1), '0');
			
			$arrayIndex++;
			$outputArray[$arrayIndex] = array(($row["unix_time"]), $row["transmitted_bytes"]);
			$outputArray2[$arrayIndex] = array(($row["unix_time"]), $row["received_bytes"]);
			
			$first_entry = false;
		}else{
			$outputArray[$arrayIndex] = array($row["unix_time"], $row["transmitted_bytes"]);
			$outputArray2[$arrayIndex] = array($row["unix_time"], $row["received_bytes"]);
			
			if($arrayIndex == ($numRows + 1)){ // indicating this is the last entry, add another dummry
				$outputArray[$arrayIndex] = array(($row["unix_time"]+1), '0');
				$outputArray2[$arrayIndex] = array(($row["unix_time"]+1), '0');
			}
		}
		$arrayIndex++;
	}
	
	$outputArray[$arrayIndex] = array($end_unixtime, '0');
	$outputArray2[$arrayIndex] = array($end_unixtime, '0');
	
	return array(array("label"=>"Transmitted Bytes", "data"=> $outputArray), array("label"=>"Received Bytes", "data"=> $outputArray2));
}

function getAnnotationData($start_unixtime, $end_unixtime, $reqRange, $currentSubject)
{
	/*
	$query = "Select subject_id, unix_time, annotation from stepLively_activity where subject_id = '". $currentSubject ."' 
	and unix_time >= ".$start_unixtime." and unix_time <= ".$end_unixtime." and annotation <> '' order by date_time";
	
	//execute the SQL query and return records
	$result = mysql_query($query) or die(mysql_error());
	
	$numRows = mysql_num_rows($result);
	
	$arrayIndex = 0;
	
	$outputArray[] = null;
	
	//display the activityresults
	while($row = mysql_fetch_array($result))
	{
		$outputArray[$arrayIndex] = array($row["unix_time"], $row["annotation"]);
		$arrayIndex++;
	}
	
	return array("label"=>"ANO", "data"=> $outputArray);
	*/
	
	return array();
}

function getUsageData($start_unixtime, $end_unixtime, $reqRange, $currentSubject)
{
	$query = "SELECT * FROM activity_annotation WHERE subject_id = '".$currentSubject."' and (start_unix_time >= ".$start_unixtime." or end_unix_time <= ".$end_unixtime." or (start_unix_time < ".$start_unixtime." and end_unix_time > ".$end_unixtime."))";
	
	
	//execute the SQL query and return records
	$result = mysql_query($query) or die(mysql_error());
	
	$numRows = mysql_num_rows($result);
	
	$arrayIndex = 0;
	
	$outputArray[] = null;
	
	//display the activityresults
	while($row = mysql_fetch_array($result))
	{
		$outputArray[$arrayIndex] = array($row["start_unix_time"], $row['end_unix_time'], $row['activity_name'], $row['id']);
		$arrayIndex++;
	}
	
	return array("label"=>"Activity", "data"=> $outputArray);
}

?>