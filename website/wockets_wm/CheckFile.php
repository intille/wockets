<?php require_once('Connections/Wockets.php'); ?>
<?php
		
	$filename="";
	if (isset($_GET['filename']))
		$filename=$_GET['filename'];
	else 	if (isset($_POST['filename']))
			$filename=$_POST['filename'];	

	$imei="";			
		if (isset($_GET['imei']))
		$imei=$_GET['imei'];
	else 	if (isset($_POST['imei']))
			$imei=$_POST['imei'];	

	$relative_path="";			
		if (isset($_GET['relative_path']))
		$relative_path=$_GET['relative_path'];
	else 	if (isset($_POST['relative_path']))
			$relative_path=$_POST['relative_path'];	

	mysql_select_db($database_Wockets, $Wockets);
	

	//echo $query_Recordset1;
	$query_Recordset2 = sprintf("SELECT * FROM PHONES,PARTICIPANTS_PHONE WHERE PHONES.imei ='".$imei."' AND PHONES.id=PARTICIPANTS_PHONE.phone_id");
	$Recordset2 = mysql_query($query_Recordset2, $Wockets) or die(mysql_error());
	$row_Recordset2 = mysql_fetch_assoc($Recordset2);
	$totalRows_Recordset2 = mysql_num_rows($Recordset2);

	if ($totalRows_Recordset2==1) 
	{
		$participant_id=$row_Recordset2['participant_id'];
		$relative_path="Subject".$participant_id. "/" . $relative_path;
		$absfilename=getcwd()."/WocketsData/".$relative_path."/".$filename;	 
	 	$query_Recordset1 = sprintf("SELECT * FROM FILE_UPLOAD WHERE imei ='".$imei."' AND filename='".$filename."' AND relative_path='".$relative_path."'");
	
		$Recordset1 = mysql_query($query_Recordset1, $Wockets) or die(mysql_error());
		$row_Recordset1 = mysql_fetch_assoc($Recordset1);
		$totalRows_Recordset1 = mysql_num_rows($Recordset1); 

		if (($totalRows_Recordset1>=1) && ($filename!="")&&(file_exists ($absfilename)))
		{	
			$md5=md5_file($absfilename);
			echo "true,".$md5.",".$row_Recordset1['sender_date'].",".$row_Recordset1['server_date'];		
		}else
			echo "false";		
			
	}else
		echo "false";		
			

		
?>