<?php require_once('Connections/Wockets.php'); ?>

<!-- Set up chart preferences  -->

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

	// Set up timeline for x-axis

	for ($hour=0;($hour<24);$hour++)
	{
		for ($min=0;($min<60);$min++)
		{
			echo sprintf("%02d:",$hour) . sprintf("%02d",$min);
			if (!(($hour==23) && ($min==59)))
				echo "|";
		}
	}
?>

</categories>

<?php

	// Get display parameters

	$viewBy = $_GET['viewBy'];
	$showRawData = $_GET['showRawData'];
	$showBytesSent = $_GET['showBytesSent'];
	$showBytesReceived = $_GET['showBytesReceived'];
	$showBattery = $_GET['showBattery'];
	$showPhoneStats = $_GET['showPhoneStats'];
	$isPhoneDataLoaded = false;
	
	$BATTERY_SCALING = 120;
	$PHONE_BATTERY_SCALING = 100;


	// Open database connection
	
	mysql_select_db($database_Wockets, $Wockets);
	
	// Get phone stats
	
	if ($showBytesSent == "checked" || $showBytesReceived == "checked" || $showBattery == "checked" || $showPhoneStats == "checked")
	{	
		$query_PhoneRecordset ="select sender_date,phone_battery,mainmemory,sdmemory,battery1,transmitted_bytes1,received_bytes1,battery2,
	transmitted_bytes2,received_bytes2, swap_event FROM PHONE_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=PHONE_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id  ORDER BY sender_date";
		$PhoneRecordset = mysql_query($query_PhoneRecordset, $Wockets) or die(mysql_error());
		$row_PhoneRecordset = mysql_fetch_assoc($PhoneRecordset);
		$phone_battery_data="";
		$mainmemory_data="";
		$sdmemory_data="";
		$battery0="";
		$battery1="";
		$transmitted_bytes0="";	
		$transmitted_bytes1="";	
		$received_bytes0="";
		$received_bytes1="";
		$isPhoneDataLoaded = true;
	}
			 
 	if ($viewBy == "macAddress")
	{
	
		// Find all unique mac addresses for date/subject
		
		$query_MacRecordset ="select distinct mac,wocket_id FROM WOCKET_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=WOCKET_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id ORDER BY wocket_id, sender_date";
		$MacRecordset = mysql_query($query_MacRecordset, $Wockets) or die(mysql_error());
	
		// Find wockets data for each mac address
		
		while ($row_MacRecordset = mysql_fetch_assoc($MacRecordset)) 
		{
			$mac=$row_MacRecordset['mac'];
			$query_RecordsetWocket ="select sender_date,mac,activity_count,wocket_id FROM WOCKET_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=WOCKET_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id AND WOCKET_STATS.mac='".$mac."' ORDER BY sender_date";
			$RecordsetWocket = mysql_query($query_RecordsetWocket, $Wockets) or die(mysql_error());
			$row_RecordsetWocket = mysql_fetch_assoc($RecordsetWocket);
			$wid=$row_RecordsetWocket['wocket_id'];
			$activity_count="";
		
			for ($hour=0;($hour<24);$hour++)
			{
				for ($min=0;($min<60);$min++)
				{
					$current_datetime=$_GET['date']." ".sprintf("%02d:",$hour) . sprintf("%02d",$min);
					if ($current_datetime==substr($row_RecordsetWocket['sender_date'],0,16))
					{
						$activity_count=$activity_count. $row_RecordsetWocket['activity_count'];
						while($current_datetime==substr($row_RecordsetWocket['sender_date'],0,16))
							$row_RecordsetWocket = mysql_fetch_assoc($RecordsetWocket);
					}
					if (!(($hour==23) && ($min==59) && ($sec==59)))
						$activity_count=$activity_count."|";
				}
			}
			
			// Add this sensor's series to the plot
			echo "<dataset seriesName='Wck", $wid, " (", substr($mac,8,4), ")", " A.C.'>";
			echo $activity_count, "</dataset>";
		}
	}
	
	// Load activity counts according to sensorID (ultimately used to derive placement)

	if ($viewBy == "placement")
	{
		$query_Wocket0Recordset ="select sender_date,mac,activity_count FROM WOCKET_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=WOCKET_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id AND wocket_id=0  ORDER BY sender_date";
		$Wocket0Recordset = mysql_query($query_Wocket0Recordset, $Wockets) or die(mysql_error());
		$row_Wocket0Recordset = mysql_fetch_assoc($Wocket0Recordset);
		$totalRows_Wocket0Recordset = mysql_num_rows($Wocket0Recordset);
		$activity_count0="";

		$query_Wocket1Recordset ="select sender_date,mac,activity_count FROM WOCKET_STATS,PARTICIPANTS_PHONE,PHONES WHERE DATE(sender_date)='".$_GET['date']."' AND PARTICIPANTS_PHONE.participant_id='".$_GET['participant_id']."' AND PHONES.imei=WOCKET_STATS.imei AND PHONES.id=PARTICIPANTS_PHONE.phone_id AND wocket_id=1  ORDER BY sender_date";
		$Wocket1Recordset = mysql_query($query_Wocket1Recordset, $Wockets) or die(mysql_error());
		$row_Wocket1Recordset = mysql_fetch_assoc($Wocket1Recordset);
		$totalRows_Wocket1Recordset = mysql_num_rows($Wocket1Recordset);	
		$activity_count1="";
	}
	
	// Load raw data stats
	
	if ($showRawData == "checked")
	{
		$query_RawDataRecordset ="select SubjectID,RawDataTime,RawDataSize FROM RAW_DATA_STATS WHERE DATE(RawDataTime)='".$_GET['date']."' AND SubjectID='".$_GET['participant_id']."' ORDER BY RawDataTime";
		$RawDataRecordset = mysql_query($query_RawDataRecordset, $Wockets) or die(mysql_error());
		$row_RawDataRecordset = mysql_fetch_assoc($RawDataRecordset);
		$totalRows_RawDataRecordset = mysql_num_rows($RawDataRecordset);	
		$RawDataSize="";
	}
	
	// Load prompting data for labels
	
	$query_PromptingRecordset ="select PromptTime,PromptType,PrimaryActivity,Categories,AlternateActivities FROM PROMPTING WHERE DATE(PromptTime)='".$_GET['date']."' AND PROMPTING.SubjectID='".$_GET['participant_id']."' ORDER BY PromptTime";
	$PromptingRecordset = mysql_query($query_PromptingRecordset, $Wockets) or die(mysql_error());

	// Load sms data for labels
	
	$query_SMSRecordset ="select id,MessageTime,Message FROM SMS_MSGS WHERE DATE(MessageTime)='".$_GET['date']."' AND SMS_MSGS.SubjectID='".$_GET['participant_id']."' ORDER BY MessageTime";
	$SMSRecordset = mysql_query($query_SMSRecordset, $Wockets) or die(mysql_error());

	// Load swap data for labels
	
	$query_SwappingRecordset ="select SwapTime,SwapEvent,RestartedEvent,LocationChangedEvent,SensorSetID,SensorID0,SensorID1,SensorPlacement0,SensorPlacement1 FROM SWAPPING WHERE DATE(SwapTime)='".$_GET['date']."' AND SWAPPING.SubjectID='".$_GET['participant_id']."' ORDER BY SwapTime";
	$SwappingRecordset = mysql_query($query_SwappingRecordset, $Wockets) or die(mysql_error());
	
	// Populate chart
	
	for ($hour=0;($hour<24);$hour++)
	{
		$rawDataValue = 0;
		for ($min=0;($min<60);$min++)
		{
			$current_datetime=$_GET['date']." ".sprintf("%02d:",$hour) . sprintf("%02d",$min);

			// Seed phone data series data
			 
			if ($isPhoneDataLoaded == true)
			{
				if ($current_datetime == substr($row_PhoneRecordset['sender_date'],0,16))
				{				
					if ($showPhoneStats == "checked" )
					{	
						$phone_battery_data=$phone_battery_data. ($row_PhoneRecordset['phone_battery'] * $PHONE_BATTERY_SCALING);
						$mainmemory_data=$mainmemory_data.$row_PhoneRecordset['mainmemory'];
						$sdmemory_data=$sdmemory_data.$row_PhoneRecordset['sdmemory'];
					}	
					if ($showBattery == "checked" )
					{	
						$thisBattery1 = ($row_PhoneRecordset['battery1'] - 560);
						if ($thisBattery1 < 0)
							$thisBattery1 = 0;
						$thisBattery2 = ($row_PhoneRecordset['battery2'] - 560);
						if ($thisBattery2 < 0)
							$thisBattery2 = 0;
						$battery0=$battery0.($thisBattery1 * $BATTERY_SCALING);
						$battery1=$battery1.($thisBattery2 * $BATTERY_SCALING);
					}
					if ($showBytesSent == "checked" )
					{
						$transmitted_bytes0=$transmitted_bytes0.$row_PhoneRecordset['transmitted_bytes1'];	
						$transmitted_bytes1=$transmitted_bytes1.$row_PhoneRecordset['transmitted_bytes2'];
					}
					if ($showBytesReceived == "checked" )
					{					
						$received_bytes0=$received_bytes0.$row_PhoneRecordset['received_bytes1'];	
						$received_bytes1=$received_bytes1.$row_PhoneRecordset['received_bytes2'];	
					}
					while($current_datetime==substr($row_PhoneRecordset['sender_date'],0,16))
					{
						$row_PhoneRecordset = mysql_fetch_assoc($PhoneRecordset);
					}
				}
			}
			
			// Seed raw data series
			
			if ($showRawData == "checked")
			{
				if (substr($current_datetime,0,13)==substr($row_RawDataRecordset['RawDataTime'],0,13))
				{
					while(substr($current_datetime,0,13)==substr($row_RawDataRecordset['RawDataTime'],0,13))
					{
						$rawDataValue+=$row_RawDataRecordset['RawDataSize'];
						$row_RawDataRecordset = mysql_fetch_assoc($RawDataRecordset);
					}
					$RawDataSize=$RawDataSize. $rawDataValue;
				}
				else if (substr($current_datetime,11,2) > substr($row_RawDataRecordset['RawDataTime'],11,2))
					$RawDataSize=$RawDataSize. 0;
				else 
					$RawDataSize=$RawDataSize. $rawDataValue;
			}
				
			if ($viewBy == "placement")
			{
				if ($current_datetime==substr($row_Wocket0Recordset['sender_date'],0,16))
				{
					$activity_count0=$activity_count0. $row_Wocket0Recordset['activity_count'];
					while($current_datetime==substr($row_Wocket0Recordset['sender_date'],0,16))
						$row_Wocket0Recordset = mysql_fetch_assoc($Wocket0Recordset);
				}
				if ($current_datetime==substr($row_Wocket1Recordset['sender_date'],0,16))
				{
					$activity_count1=$activity_count1. $row_Wocket1Recordset['activity_count'];
					while($current_datetime==substr($row_Wocket1Recordset['sender_date'],0,16))
						$row_Wocket1Recordset = mysql_fetch_assoc($Wocket1Recordset);
				}
			}
				
			// Add pipe to separate values in each string array

			if (!(($hour==23) && ($min==59) && ($sec==59)))
			{
				$phone_battery_data=$phone_battery_data."|";
				$mainmemory_data=$mainmemory_data."|";
				$sdmemory_data=$sdmemory_data."|";
				$battery0=$battery0."|";			
				$battery1=$battery1."|";
				$received_bytes0=$received_bytes0."|";			
				$received_bytes1=$received_bytes1."|";	
				$transmitted_bytes0=$transmitted_bytes0."|";
				$transmitted_bytes1=$transmitted_bytes1."|";	
				$activity_count0=$activity_count0."|";
				$activity_count1=$activity_count1."|";
				$RawDataSize=$RawDataSize."|";
			}			
		}
	}
?>

<vTrendlines>
<?php

	// Add labels for SMS messages
	while ($row_SMSRecordset = mysql_fetch_assoc($SMSRecordset)) 
	{
		$messageTime = $row_SMSRecordset['MessageTime'];
		$timeSlot = substr($messageTime, 11, 2) * 60  + substr($messageTime, 14,2);
		$label = $row_SMSRecordset['id'];
		$color = 'CC33CC';
		echo "<line startIndex='", $timeSlot, "' displayValue='SMS #", $label, "' color='", $color, "' thickness='1'/>";
    } 
    
    // Add labels for Prompt responses
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
			else
			{
				$activities = $primaryActivity;
 				$activities .= ' (' . str_replace('|', ', ', $categories) . ')';
 			}
	 		$activity = str_replace(" " , "\n", $activities);
			echo "<line startIndex='", $timeSlot - 10, "' endIndex='", $timeSlot, "' displayValue='' color='", $color, "' thickness='1'/>"; 
			echo "<line startIndex='", $timeSlot, "' displayValue='", $activity, "' color='", $color, "' thickness='1'/>";
		}
    } 


	// By default placement labels will be wocket 1 and wocket 0
	$placement0="Wck0";
	$placement1="Wck1";
	$swapPlacement0="Wck0";
	$swapPlacement1="Wck1";
		
	// Add labels for swap/start events
	while ($row_SwappingRecordset = mysql_fetch_assoc($SwappingRecordset))
	{
		if ($viewBy == "macAddress")
		{
			$swapPlacement0 = $placement . " (" . $row_SwappingRecordset['SensorPlacement0'] . ")";
			$swapPlacement1 = $placement . " (" . $row_SwappingRecordset['SensorPlacement1'] . ")";
		}
		else
		{
			$swapPlacement0 = $placement0 = $row_SwappingRecordset['SensorPlacement0'];
			$swapPlacement1 = $placement1 = $row_SwappingRecordset['SensorPlacement1'];
		}
		$ID0 = substr($row_SwappingRecordset['SensorID0'], 8, 4);
		$ID1 = substr($row_SwappingRecordset['SensorID1'], 8, 4);
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
		$label .= $ID0 . ": " . $swapPlacement0 . "\n";
		$label .= $ID1 . ": " . $swapPlacement1 . "\n";
		echo "<line startIndex='", $timeSlot, "' displayValue='", $label, "' color='", $color, "' thickness='1'/>";
    } 

?>
</vTrendlines>


<?php 
		
	if ($viewBy == "placement")
	{
		echo "<dataset seriesName='" . $placement0 . ": Activity Counts'>" . $activity_count0 . "</dataset>";
		echo "<dataset seriesName='" . $placement1 . ": Activity Counts'>" . $activity_count1 . "</dataset>";
	}

	if ($showBattery == "checked")
	{
		echo "<dataset seriesName='" . $placement0 . ": Battery'>" . $battery0 . "</dataset>";
		echo "<dataset seriesName='" . $placement1 . ": Battery'>" . $battery1 . "</dataset>";
	}

	if ($showBytesSent == "checked")
	{
		echo "<dataset seriesName='" . $placement0 . ": Sent Bytes'>" . $transmitted_bytes0 . "</dataset>";
		echo "<dataset seriesName='" . $placement1 . ": Sent Bytes'>" . $transmitted_bytes1 . "</dataset>";
	}
	
	if ($showBytesReceived == "checked")
	{
		echo "<dataset seriesName='" . $placement0 . ": Rcvd Bytes'>" . $received_bytes0 . "</dataset>";
		echo "<dataset seriesName='" . $placement1 . ": Rcvd Bytes'>" . $received_bytes1 . "</dataset>";
	}
	
	// Show phone stats if requested
	if ($showPhoneStats == "checked" )
	{
		echo "<dataset seriesName='Phone Battery'>" . $phone_battery_data .	"</dataset>";
		echo "<dataset seriesName='Free Main Memory (MB)'>" . $mainmemory_data . "</dataset>";
		echo "<dataset seriesName='Free SD Memory (MB)'>" . $sdmemory_data . "</dataset>";
	}
		
	// Show raw data if requested
	if ($showRawData == "checked" )
	{
		echo "<dataset thickness='1' color='333333' seriesName='Raw Data (KB/100)'>" . $RawDataSize . "</dataset>";
	}		
?>

</chart>
