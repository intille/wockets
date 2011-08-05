<?php require_once('Connections/Wockets.php'); ?>
<?php
	$server_date=date("Y-m-d H:m:s");
	$phone_status=0;
	$wocket_status=0;
	$event_status=0;	
	$qa_status=0;
if ((isset($_GET['imei'])) && (isset($_GET['phone_battery']))){
	// Get posted parameters
	$imei=$_GET['imei'];
	$sender_date=$_GET['sender_date'];
	$phone_battery=$_GET['phone_battery'];
	$mainmemory=$_GET['mainmemory'];
	$sdmemory=$_GET['sdmemory'];
	$battery1=$_GET['battery1'];
	$transmitted_bytes1=$_GET['transmitted_bytes1'];
	$received_bytes1=$_GET['received_bytes1'];
	$battery2=$_GET['battery2'];
	$transmitted_bytes2=$_GET['transmitted_bytes2'];
	$received_bytes2=$_GET['received_bytes2'];
	$phone_status=1;
}else if ((isset($_POST['imei'])) && (isset($_POST['phone_battery']))){
	$imei=$_POST['imei'];
	$sender_date=$_POST['sender_date'];
	$phone_battery=$_POST['phone_battery'];
	$mainmemory=$_POST['mainmemory'];
	$sdmemory=$_POST['sdmemory'];
	$battery1=$_POST['battery1'];
	$transmitted_bytes1=$_POST['transmitted_bytes1'];
	$received_bytes1=$_POST['received_bytes1'];
	$battery2=$_POST['battery2'];
	$transmitted_bytes2=$_POST['transmitted_bytes2'];
	$received_bytes2=$_POST['received_bytes2'];
	$phone_status=1;
}else if ((isset($_GET['imei'])) && (isset($_GET['wocket_id']))){
	// Get posted parameters
	$imei=$_GET['imei'];
	$sender_date=$_GET['sender_date'];
	$wocket_id=$_GET['wocket_id'];
	$mac_address=$_GET['mac_address'];
	$activity_count=$_GET['activity_count'];
	$wocket_status=1;
}else if ((isset($_POST['imei'])) && (isset($_POST['wocket_id']))){
	// Get posted parameters
	$imei=$_POST['imei'];
	$sender_date=$_POST['sender_date'];
	$wocket_id=$_POST['wocket_id'];
	$mac_address=$_POST['mac_address'];
	$activity_count=$_POST['activity_count'];
	$wocket_status=1;
}else if ((isset($_GET['imei'])) && (isset($_GET['swap_time']))){
	// Get posted parameters
	$imei=$_GET['imei'];
	$subject_id=$_GET['subject_id'];
	$swap_time=$_GET['swap_time'];
	$swap_event=$_GET['swap_event'];
	$restart_event= $_GET['restart_event'];
	$location_change_event = $_GET['location_change_event'];
	$sensor_set_id = $_GET['sensor_set_id'];
	$number_of_sensors = $_GET['number_of_sensors'];
	$sensor_id0 = $_GET['sensor_id0'];
	$sensor_placement0 = $_GET['sensor_placement0'];
	$sensor_label0 = $_GET['sensor_label0'];
	$sensor_id1 = $_GET['sensor_id1'];
	$sensor_placement1 = $_GET['sensor_placement1'];
	$sensor_label1 = $_GET['sensor_label1'];
	$sensor_id2 = $_GET['sensor_id2'];
	$sensor_placement2 = $_GET['sensor_placement2'];
	$sensor_label2 = $_GET['sensor_label2'];
	$event_status=1;
}else if ((isset($_POST['imei'])) && (isset($_POST['swap_time']))){
	$imei=$_POST['imei'];
	$subject_id=$_POST['subject_id'];
	$swap_time=$_POST['swap_time'];
	$swap_event=$_POST['swap_event'];
	$restart_event= $_POST['restart_event'];
	$location_change_event = $_POST['location_change_event'];
	$sensor_set_id = $_POST['sensor_set_id'];
	$number_of_sensors = $_POST['number_of_sensors'];
	$sensor_id0 = $_POST['sensor_id0'];
	$sensor_placement0 = $_POST['sensor_placement0'];
	$sensor_label0 = $_POST['sensor_label0'];
	$sensor_id1 = $_POST['sensor_id1'];
	$sensor_placement1 = $_POST['sensor_placement1'];
	$sensor_label1 = $_POST['sensor_label1'];
	$sensor_id2 = $_POST['sensor_id2'];
	$sensor_placement2 = $_POST['sensor_placement2'];
	$sensor_label2 = $_POST['sensor_label2'];
	$event_status=1;	
}else if ((isset($_GET['imei'])) && (isset($_GET['prompt_time']))){
	// Get posted parameters
	$imei=$_GET['imei'];
	$subject_id=$_GET['subject_id'];
	$prompt_time=$_GET['prompt_time'];
	$prompt_type=$_GET['prompt_type'];
	$response_time= $_GET['response_time'];
	$response_interval_start = $_GET['response_interval_start'];
	$response_interval_end = $_GET['response_interval_end'];
	$categories = $_GET['categories'];
	$primary_activity = $_GET['primary_activity'];
	$alternate_activities = $_GET['alternate_activities'];
	$qa_status=1;
}else if ((isset($_POST['imei'])) && (isset($_POST['prompt_time']))){
	$imei=$_POST['imei'];
	$subject_id=$_POST['subject_id'];
	$prompt_time=$_POST['prompt_time'];
	$prompt_type=$_POST['prompt_type'];
	$response_time= $_POST['response_time'];
	$response_interval_start = $_POST['response_interval_start'];
	$response_interval_end = $_POST['response_interval_end'];
	$categories = $_POST['categories'];
	$primary_activity = $_POST['primary_activity'];
	$alternate_activities = $_POST['alternate_activities'];
	$qa_status=1;
}

if ($phone_status==1){	
	$asender_date=explode(",",$sender_date);
	$aphone_battery=explode(",",$phone_battery);
	$amainmemory=explode(",",$mainmemory);
	$asdmemory=explode(",",$sdmemory);
	$abattery1=explode(",",$battery1);
	$atransmitted_bytes1=explode(",",$transmitted_bytes1);
	$areceived_bytes1=explode(",",$received_bytes1);
	$abattery2=explode(",",$battery2);
	$atransmitted_bytes2=explode(",",$transmitted_bytes2);
	$areceived_bytes2=explode(",",$received_bytes2);
	$size=count($asender_date);
	$changed=0;
	
	for($i=0; $i<($size-1); $i++) {
	
		//check if it exists
		$selectQuery="SELECT * from `wockets`.`PHONE_STATS` where imei='$imei' AND sender_date='".$asender_date[$i]."'";
		mysql_query($selectQuery) or die(mysql_error());
		if (mysql_affected_rows()==0){
			// Do the SQL Insert:
			$insertQuery = "INSERT INTO `wockets`.`PHONE_STATS`(`imei`,`server_date`,`sender_date`,`phone_battery`,`mainmemory`,`sdmemory`,`battery1`,`transmitted_bytes1`,`received_bytes1`,`battery2`,`transmitted_bytes2`,`received_bytes2`) VALUES ('$imei','$server_date','".$asender_date[$i]."','".$aphone_battery[$i]."','".$amainmemory[$i]."','".$asdmemory[$i]."','".$abattery1[$i]."','".$atransmitted_bytes1[$i]."','".$areceived_bytes1[$i]."','".$abattery2[$i]."','".$atransmitted_bytes2[$i]."','".$areceived_bytes2[$i]."')";
			mysql_query($insertQuery) or die(mysql_error());
			if (mysql_affected_rows()==1)
				$changed++;
		}else
			$changed++;
	}

//	if (mysql_affected_rows()==1)
	if ($changed==($size-1))
		echo "success";
	else
		echo "failed";
}else if ($wocket_status==1){
	$sender_date=explode(",",$sender_date);
	$wocket_id=explode(",",$wocket_id);
	$mac_address=explode(",",$mac_address);
	$activity_count=explode(",",$activity_count);
	$size=count($sender_date);
	$changed=0;
	for($i=0; $i<($size-1); $i++) {
		
		//check if it exists
		$selectQuery="SELECT * from `wockets`.`WOCKET_STATS` where mac='".$mac_address[$i]."' AND sender_date='".$sender_date[$i]."'";
		mysql_query($selectQuery) or die(mysql_error());                                             
		if (mysql_affected_rows()==0){
			// Do the SQL Insert:             
			$insertQuery = "INSERT INTO `wockets`.`WOCKET_STATS`(`imei`,`server_date`,`sender_date`,`mac`,`wocket_id`,`activity_count`) VALUES ('$imei','$server_date','".$sender_date[$i]."','".$mac_address[$i]."','".$wocket_id[$i]."','".$activity_count[$i]."')";
		mysql_query($insertQuery) or die(mysql_error());
		if (mysql_affected_rows()==1)
			$changed++;
		}else
			$changed++;
	}
	//if (mysql_affected_rows()==1)
	if ($changed==($size-1))
		echo "success";
	else
		echo "failed";
}
else if ($event_status==1){

	$aswap_time  = explode(",",$swap_time);
	$aswap_event = explode(",",$swap_event);
	$arestart_event = explode(",",$restart_event);
	$alocation_change_event = explode(",",$location_change_event);
	$asensor_set_id = explode(",",$sensor_set_id);
	$anumber_of_sensors = explode(",",$number_of_sensors);
	$asensor_id0 = explode(",", $sensor_id0);
	$asensor_placement0 = explode(",", $sensor_placement0);
	$asensor_label0 = explode(",", $sensor_label0);
	$asensor_id1 = explode(",", $sensor_id1);
	$asensor_placement1 = explode(",", $sensor_placement1);
	$asensor_label1 = explode(",", $sensor_label1);
	$asensor_id2 = explode(",", $sensor_id2);
	$asensor_placement2 = explode(",", $sensor_placement2);
	$asensor_label2 = explode(",", $sensor_label2);
	$size=count($aswap_time);
	$changed=0;

	for($i=0; $i<($size-1); $i++) {		
		//check if it exists
		$selectQuery="SELECT * from `wockets`.`SWAPPING` where imei='$imei' AND SwapTime='".$aswap_time[$i]."'";
		mysql_query($selectQuery) or die(mysql_error());
				
		if (mysql_affected_rows()==0)
		{
			// Do the SQL Insert:
			$insertQuery = "INSERT INTO `wockets`.`SWAPPING`(`imei`,`SubjectID`,`SwapTime`,`SendTime`,`SwapEvent`,`RestartedEvent`,`LocationChangedEvent`,`SensorSetID`,`NumberOfSensors`,`SensorID0`,`SensorPlacement0`,`SensorLabel0`,`SensorID1`,`SensorPlacement1`,`SensorLabel1`,`SensorID2`,`SensorPlacement2`,`SensorLabel2`) VALUES ('$imei','$subject_id','".$aswap_time[$i]."','".$aswap_time[$i]."','".$aswap_event[$i]."','".$arestart_event[$i]."','".$alocation_change_event[$i]."','".$asensor_set_id[$i]."','".$anumber_of_sensors[$i]."','".$asensor_id0[$i]."' ,'".$asensor_placement0[$i]."','".$asensor_label0[$i]."','".$asensor_id1[$i]."','".$asensor_placement1[$i]."','".$asensor_label1[$i]."','".$asensor_id2[$i]."','".$asensor_placement2[$i]."','".$asensor_label2[$i]."')";
	
			mysql_query($insertQuery) or die(mysql_error());
			if (mysql_affected_rows()==1)
				$changed++;		
		}
		else
		{
			$changed++;
		}
	}
	
	//if (mysql_affected_rows()==1)
	if ($changed==($size-1))
		echo "success";
	else
		echo "failed";
		
}
else if ($qa_status==1){

	$aprompt_time  = explode(",",$prompt_time);
	$aprompt_type  = explode(",",$prompt_type);
	$aresponse_time  = explode(",",$response_time);
	$aresponse_interval_start  = explode(",",$response_interval_start);
	$aresponse_interval_end  = explode(",",$response_interval_end);
	$acategories  = explode(",",$categories);
	$aprimary_activity  = explode(",",$primary_activity);
	$aalternate_activities  = explode(",",$alternate_activities);
	
	$size=count($aprompt_time);
	$changed=0;

	for($i=0; $i<($size-1); $i++) {	
		
		//check if it exists
		$selectQuery="SELECT * from `wockets`.`PROMPTING` where imei='$imei' AND PromptTime='".$aprompt_time[$i]."'";
		mysql_query($selectQuery) or die(mysql_error());
				
		if (mysql_affected_rows()==0)
		{
			// Do the SQL Insert:
			$insertQuery = "INSERT INTO `wockets`.`PROMPTING`(`imei`,`SubjectID`,`PromptTime`,`ResponseTime`,`PromptType`,`ResponseIntervalStart`,`ResponseIntervalEnd`,`Categories`,`PrimaryActivity`,`AlternateActivities`) VALUES ('$imei','$subject_id','".$aprompt_time[$i]."','".$aresponse_time[$i]."','".$aprompt_type[$i]."','".$aresponse_interval_start[$i]."','".$aresponse_interval_end[$i]."','".$acategories[$i]."','".$aprimary_activity[$i]."','".$aalternate_activities[$i]."')";
	
	
			mysql_query($insertQuery) or die(mysql_error());
			if (mysql_affected_rows()==1)
				$changed++;		
				
		}
		else
		{
			$changed++;
		}
	}
	
	//if (mysql_affected_rows()==1)
	if ($changed==($size-1))
		echo "success";
	else
		echo "failed";
		
}

?>