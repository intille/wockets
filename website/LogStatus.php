<?php require_once('Connections/Wockets.php'); ?>
<?php
	$server_date=date("Y-m-d H:m:s");
if (isset($_GET['imei'])){
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

}else{
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
}


// Do the SQL Insert:
$insertQuery = "INSERT INTO `wockets`.`PHONE_STATS`(`imei`,`server_date`,`sender_date`,`phone_battery`,`mainmemory`,`sdmemory`,`battery1`,`transmitted_bytes1`,`received_bytes1`,`battery2`,`transmitted_bytes2`,`received_bytes2`) VALUES ('$imei','$server_date','$sender_date','$phone_battery','$mainmemory','$sdmemory','$battery1','$transmitted_bytes1','$received_bytes1','$battery2','$transmitted_bytes2','$received_bytes2')";
mysql_query($insertQuery) or die(mysql_error());
if (mysql_affected_rows()==1)
	echo "success";
else
	echo "failed";
?>