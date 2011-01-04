<?php require_once('Connections/Wockets.php'); ?>
<?php
	$server_date=date("Y-m-d H:m:s");
	$phone_status=0;
	$wocket_status=0;
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
?>