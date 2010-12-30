<?php require_once('Connections/Wockets.php'); ?>
<chart compactDataMode="1" dataSeparator="|" paletteThemeColor="5D57A5" divLineColor="5D57A5" divLineAlpha="40" vDivLineAlpha="40"
dynamicAxis="1"
>
<categories>
<?php	
	for ($hour=0;($hour<24);$hour++)
		for ($min=0;($min<60);$min++){
				echo sprintf("%02d:",$hour) . sprintf("%02d",$min)	;
				if (!(($hour==23) && ($min==59)))
					echo "|";
			}
?>
</categories>

<?php
	mysql_select_db($database_Wockets, $Wockets);
	$query_Recordset1 ="select sender_date,phone_battery,mainmemory,sdmemory,battery1,transmitted_bytes1,received_bytes1,battery2,
transmitted_bytes2,received_bytes2 FROM PHONE_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=PHONE_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id  ORDER BY sender_date";

	$Recordset1 = mysql_query($query_Recordset1, $Wockets) or die(mysql_error());
	$row_Recordset1 = mysql_fetch_assoc($Recordset1);
	$totalRows_Recordset1 = mysql_num_rows($Recordset1);
	$phone_battery_data="";
	$mainmemory_data="";
	$sdmemory_data="";
	
	$battery1="";
	$transmitted_bytes1="";	
	$received_bytes1="";
	
	$battery2="";
	$transmitted_bytes2="";	
	$received_bytes2="";
	
	
	$query_Recordset2 ="select sender_date,mac,activity_count FROM WOCKET_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=WOCKET_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id AND wocket_id=0  ORDER BY sender_date";
	$Recordset2 = mysql_query($query_Recordset2, $Wockets) or die(mysql_error());
	$row_Recordset2 = mysql_fetch_assoc($Recordset2);
	$totalRows_Recordset2 = mysql_num_rows($Recordset2);
	
	
	$query_Recordset3 ="select sender_date,mac,activity_count FROM WOCKET_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=WOCKET_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id AND wocket_id=1  ORDER BY sender_date";
	$Recordset3 = mysql_query($query_Recordset3, $Wockets) or die(mysql_error());
	$row_Recordset3 = mysql_fetch_assoc($Recordset3);
	$totalRows_Recordset3 = mysql_num_rows($Recordset3);	
	$activity_count0="";
	$activity_count1="";
	
	
	for ($hour=0;($hour<24);$hour++)
		for ($min=0;($min<60);$min++){
				$current_datetime=$_GET['date']." ".sprintf("%02d:",$hour) . sprintf("%02d",$min);

				if ($current_datetime==	substr($row_Recordset1['sender_date'],0,16)){				
						$phone_battery_data=$phone_battery_data. $row_Recordset1['phone_battery'];
						$mainmemory_data=$mainmemory_data.$row_Recordset1['mainmemory'];
						$sdmemory_data=$sdmemory_data.$row_Recordset1['sdmemory'];
					
						$battery1=$battery1.$row_Recordset1['battery1'];
						$transmitted_bytes1=$transmitted_bytes1.$row_Recordset1['transmitted_bytes1'];;	
						$received_bytes1=$received_bytes1.$row_Recordset1['received_bytes1'];;	
						
						$battery2=$battery2.$row_Recordset1['battery2'];
						$transmitted_bytes2=$transmitted_bytes2.$row_Recordset1['transmitted_bytes2'];;	
						$received_bytes2=$received_bytes2.$row_Recordset1['received_bytes2'];;	
						
						while($current_datetime==substr($row_Recordset1['sender_date'],0,16))
							$row_Recordset1 = mysql_fetch_assoc($Recordset1);
				}
				
				
				if ($current_datetime==	substr($row_Recordset2['sender_date'],0,16))
				{
						$activity_count0=$activity_count0. $row_Recordset2['activity_count'];
						while($current_datetime==substr($row_Recordset2['sender_date'],0,16))
							$row_Recordset2 = mysql_fetch_assoc($Recordset2);
				}else
					$activity_count0=$activity_count0. "0";
				
				if ($current_datetime==	substr($row_Recordset3['sender_date'],0,16))
				{
						$activity_count1=$activity_count1. $row_Recordset3['activity_count'];
						while($current_datetime==substr($row_Recordset3['sender_date'],0,16))
							$row_Recordset3 = mysql_fetch_assoc($Recordset3);
				}else
					$activity_count1=$activity_count1. "0";
			
				if (!(($hour==23) && ($min==59) && ($sec==59))){
					$phone_battery_data=$phone_battery_data."|";
					$transmitted_bytes1=$transmitted_bytes1."|";
					$mainmemory_data=$mainmemory_data."|";
					$sdmemory_data=$sdmemory_data."|";
					$battery1=$battery1."|";			
					$received_bytes1=$received_bytes1."|";	
						
					$battery2=$battery2."|";
					$transmitted_bytes2=$transmitted_bytes2."|";	
					$received_bytes2=$received_bytes2."|";	
					
					$activity_count0=$activity_count0."|";
					$activity_count1=$activity_count1."|";					
				}							
			
			}

	
?>

<dataset seriesName="Phone Battery">
<?php echo $phone_battery_data; ?>
</dataset>

<dataset seriesName="Free Main Memory (MB)">
<?php echo $mainmemory_data; ?>
</dataset>


<dataset seriesName="Free SD Memory (MB)">
<?php echo $sdmemory_data; ?>
</dataset>

<dataset seriesName="Wockets 1- Battery">
<?php echo $battery1; ?>
</dataset>

<dataset seriesName="Wockets 1- Sent Bytes">
<?php echo $transmitted_bytes1; ?>
</dataset>

<dataset seriesName="Wockets 1- Received Bytes">
<?php echo $received_bytes1; ?>
</dataset>


<dataset seriesName="Wockets 1- Activity Count">
<?php echo $activity_count0; ?>
</dataset>

<dataset seriesName="Wockets 2- Battery">
<?php echo $battery2; ?>
</dataset>

<dataset seriesName="Wockets 2- Sent Bytes">
<?php echo $transmitted_bytes2; ?>
</dataset>

<dataset seriesName="Wockets 2- Received Bytes">
<?php echo $received_bytes2; ?>
</dataset>

<dataset seriesName="Wockets 2- Activity Count">
<?php echo $activity_count1; ?>
</dataset>

</chart>
