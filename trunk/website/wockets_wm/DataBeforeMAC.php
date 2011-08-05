<?php require_once('Connections/Wockets.php'); ?>
<chart 
	compactDataMode="1" 
	dataSeparator="|" 
	paletteThemeColor="5D57A5" 
	divLineThickness="0" 
	divLineColor="5D57A5" 
	divLineAlpha="0" 
	vDivLineAlpha="0"
	dynamicAxis="0"
	lineThickness="2"
	pixelsPerPoint="4"
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
transmitted_bytes2,received_bytes2, swap_event FROM PHONE_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=PHONE_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id  ORDER BY sender_date";

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
	
	$query_Recordset4 ="select SubjectID,RawDataTime,RawDataSize FROM RAW_DATA_STATS WHERE DATE(RawDataTime)='".$_GET['date']."' AND SubjectID='".$_GET['participant_id']."' ORDER BY RawDataTime";
	$Recordset4 = mysql_query($query_Recordset4, $Wockets) or die(mysql_error());
	$row_Recordset4 = mysql_fetch_assoc($Recordset4);
	$totalRows_Recordset4 = mysql_num_rows($Recordset4);	
	$RawDataSize="";
	
	$query_PromptingRecordset ="select PromptTime,PromptType,PrimaryActivity,Categories,AlternateActivities FROM PROMPTING WHERE DATE(PromptTime)='".$_GET['date']."' AND PROMPTING.SubjectID='".$_GET['participant_id']."' ORDER BY PromptTime";
	$PromptingRecordset = mysql_query($query_PromptingRecordset, $Wockets) or die(mysql_error());
	

	$query_SMSRecordset ="select id,MessageTime,Message FROM SMS_MSGS WHERE DATE(MessageTime)='".$_GET['date']."' AND SMS_MSGS.SubjectID='".$_GET['participant_id']."' ORDER BY MessageTime";
	$SMSRecordset = mysql_query($query_SMSRecordset, $Wockets) or die(mysql_error());


	$query_SwappingRecordset ="select SwapTime,SwapEvent,RestartedEvent,LocationChangedEvent,SensorSetID,SensorPlacement0,SensorPlacement1 FROM SWAPPING WHERE DATE(SwapTime)='".$_GET['date']."' AND SWAPPING.SubjectID='".$_GET['participant_id']."' ORDER BY SwapTime";
	$SwappingRecordset = mysql_query($query_SwappingRecordset, $Wockets) or die(mysql_error());
	
	for ($hour=0;($hour<24);$hour++)
	{
		$rawDataValue = 0;
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
				

				if (substr($current_datetime,0,13)==substr($row_Recordset4['RawDataTime'],0,13))
				{
					while(substr($current_datetime,0,13)==substr($row_Recordset4['RawDataTime'],0,13))
					{
						$rawDataValue+=$row_Recordset4['RawDataSize'];
						$row_Recordset4 = mysql_fetch_assoc($Recordset4);
					}
					$RawDataSize=$RawDataSize. $rawDataValue;
				}
				else if (substr($current_datetime,11,2) > substr($row_Recordset4['RawDataTime'],11,2))
					$RawDataSize=$RawDataSize. 0;
				else 
					$RawDataSize=$RawDataSize. $rawDataValue;

				
				if ($current_datetime==	substr($row_Recordset2['sender_date'],0,16))
				{
						$activity_count0=$activity_count0. $row_Recordset2['activity_count'];
						$i0=0;
						while($current_datetime==substr($row_Recordset2['sender_date'],0,16)){
							$row_Recordset2 = mysql_fetch_assoc($Recordset2);
							if ($i0>0)
								$last0=$row_Recordset2['activity_count'];
							else
								$last0=-1;
							$i0++;
						}
				}else if ($last0!=-1)
					$activity_count0=$activity_count0. $last0;
				/*
				else
					$activity_count0=$activity_count0. "0";
				*/
				if ($current_datetime==	substr($row_Recordset3['sender_date'],0,16))
				{
						$activity_count1=$activity_count1. $row_Recordset3['activity_count'];
						$i1=1;
						while($current_datetime==substr($row_Recordset3['sender_date'],0,16)){
							$row_Recordset3 = mysql_fetch_assoc($Recordset3);
							if ($i1>0)
								$last1=$row_Recordset3['activity_count'];
							else
								$last1=-1;
							$i1++;
						}
				}else if ($last1!=-1)
					$activity_count1=$activity_count1. $last1;
				/*
				else
					$activity_count1=$activity_count1. "0";
				*/
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
					
					$RawDataSize=$RawDataSize."|";
				}							
			
			}
		}
?>

<vTrendlines>
<?php

	while ($row_SMSRecordset = mysql_fetch_assoc($SMSRecordset)) 
	{
		$messageTime = $row_SMSRecordset['MessageTime'];
		$timeSlot = substr($messageTime, 11, 2) * 60  + substr($messageTime, 14,2);
		$label = $row_SMSRecordset['id'];
		$color = 'CC33CC';
		echo "<line startIndex='", $timeSlot, "' displayValue='SMS #", $label, "' color='", $color, "' thickness='1'/>";
    } 
    
	while ($row_PromptingRecordset = mysql_fetch_assoc($PromptingRecordset)) {
		$promptTime = $row_PromptingRecordset['PromptTime'];
		$timeSlot = substr($promptTime, 11, 2) * 60  + substr($promptTime, 14,2);
		$primaryActivity = $row_PromptingRecordset['PrimaryActivity'];
		$alternateActivities = $row_PromptingRecordset['AlternateActivities'];
		$categories = $row_PromptingRecordset['Categories'];
		$promptType = $row_PromptingRecordset['PromptType'];
		$color = 'FF3300';
		if ($promptType == 'Automatic')
			$color = 'FF9900';
		if ($primaryActivity == '' || $primaryActivity == 'X')
		{
			if ($promptType == 'Automatic')
				$color = 'AAAAAA';
			else
				$color = '666666';
			echo "<line startIndex='", $timeSlot, "' displayValue='", $primaryActivity, "' color='", $color, "' thickness='1'/>";
		}
		else
		{
			$activities = '';
			if ($alternateActivities != ''){
				$aAlternateActivity = explode('|', $alternateActivities);
				$aCategory = explode('|', $categories);
				for($i=0; $i<count($aAlternateActivity); $i++){
					$activities .= $aAlternateActivity[$i];
					$activities .= ' (' . $aCategory[$i] .')' ;
					if ($i < count($aAlternateActivity) - 1)
						$activities .= ', ';}
				$activities = str_replace($primaryActivity, $primaryActivity . '*', $activities);}
			else{
				$activities = $primaryActivity;
 				$activities .= ' (' . str_replace('|', ', ', $categories) . ')';}
	 		$activity = str_replace(" " , "\n", $activities);
			echo "<line startIndex='", $timeSlot - 10, "' endIndex='", $timeSlot, "' displayValue='' color='", $color, "' thickness='1'/>"; 
			echo "<line startIndex='", $timeSlot, "' displayValue='", $activity, "' color='", $color, "' thickness='1'/>";
		}
    } 

	$placement0="Wocket 0";
	$placement1="Wocket 1";
	
	while ($row_SwappingRecordset = mysql_fetch_assoc($SwappingRecordset)) {
		$placement0 = $row_SwappingRecordset['SensorPlacement0'];
		$placement1 = $row_SwappingRecordset['SensorPlacement1'];
		$swapTime = $row_SwappingRecordset['SwapTime'];
		$timeSlot = substr($swapTime, 11, 2) * 60  + substr($swapTime, 14,2);
		$label = "";
		$color = '33AADD';
		if ($row_SwappingRecordset['RestartedEvent'] > 0)
			$label .= "Restarted\n";
		if ($row_SwappingRecordset['LocationChangedEvent'] > 0)
			$label .= "Repositioned\n";
		if ($row_SwappingRecordset['SwapEvent'] > 0){
			$label .= "Swapped\n";
			if ($row_SwappingRecordset['SensorSetID'] == "green"){
				$color = '00AA33'; 
				$label .= "Green Set\n";}
			if ($row_SwappingRecordset['SensorSetID'] == "red"){
				$color = 'DD3333'; 
				$label .= "Red Set\n";}}
		echo "<line startIndex='", $timeSlot, "' displayValue='", $label, "' color='", $color, "' thickness='1'/>";
    } 

?>
</vTrendlines>

<!--
<dataset seriesName="Phone Battery">
<?php echo $phone_battery_data; ?>
</dataset>
-->

<!--
<dataset seriesName="Free Main Memory (MB)">
<?php echo $mainmemory_data; ?>
</dataset>
-->

<!--
<dataset seriesName="Free SD Memory (MB)">
<?php echo $sdmemory_data; ?>
</dataset>
-->


<dataset color="BBBBFF" seriesName="<?php echo $placement0, ': Battery'; ?>">
<?php echo $battery1; ?>
</dataset>

<dataset color="FFCC66" seriesName="<?php echo $placement0, ': Sent Bytes'; ?>">
<?php echo $transmitted_bytes1; ?>
</dataset>

<dataset color="66CC33" seriesName="<?php echo $placement0, ': Rcvd Bytes'; ?>">
<?php echo $received_bytes1; ?>
</dataset>

<dataset color="9933CC" seriesName="<?php echo $placement0, ': Activity Count'; ?>">
<?php echo $activity_count0; ?>
</dataset>

<dataset color="FF66CC" seriesName="<?php echo $placement1, ': Battery'; ?>">
<?php echo $battery2; ?>
</dataset>

<dataset color="3399FF" seriesName="<?php echo $placement1, ': Sent Bytes'; ?>">
<?php echo $transmitted_bytes2; ?>
</dataset>

<dataset color="CC6600" seriesName="<?php echo $placement1, ': Rcvd Bytes'; ?>">
<?php echo $received_bytes2; ?>
</dataset>

<dataset color="339999" seriesName="<?php echo $placement1, ': Activity Count'; ?>">
<?php echo $activity_count1; ?>
</dataset>

<dataset thickness="1" color="333333" seriesName="Raw Data (KB/100)">
<?php echo $RawDataSize; ?>
</dataset>

</chart>
