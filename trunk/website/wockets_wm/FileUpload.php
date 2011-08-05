<?php require_once('Connections/Wockets.php'); ?>
<?php
set_time_limit (600);
$participant_id=-1;
if ($_POST['KT_Insert1'])
{	
	$colname_Recordset1 = "-1";
	if (isset($_POST['imei'])) {
  	$colname_Recordset1 = (get_magic_quotes_gpc()) ? $_POST['imei'] : addslashes($_POST['imei']);
	}
	mysql_select_db($database_Wockets, $Wockets);
	
	$query_Recordset1 = sprintf("SELECT * FROM PHONES,PARTICIPANTS_PHONE WHERE PHONES.imei = ".$_POST['imei']." AND PHONES.id=PARTICIPANTS_PHONE.phone_id");
	$Recordset1 = mysql_query($query_Recordset1, $Wockets) or die(mysql_error());
	$row_Recordset1 = mysql_fetch_assoc($Recordset1);
	$totalRows_Recordset1 = mysql_num_rows($Recordset1);

	if (($totalRows_Recordset1==1) && (isset($_POST['root_path'])) && ($_POST['root_path']=="none"))
	{
		$participant_id=$row_Recordset1['participant_id'];
		$_POST['relative_path']="Subject".$participant_id. "/" . $_POST['relative_path'];	
	}
}
?>
<?php
// Load the common classes
require_once('includes/common/KT_common.php');

// Load the tNG classes
require_once('includes/tng/tNG.inc.php');

// Make a transaction dispatcher instance
$tNGs = new tNG_dispatcher("");

// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);

// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("filename", true, "", "", "", "", "");
$formValidation->addField("relative_path", true, "text", "", "", "", "");
$formValidation->addField("sender_date", true, "text", "", "", "", "");
$formValidation->addField("server_date", true, "text", "", "", "", "");
$formValidation->addField("imei", true, "text", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

if (!function_exists("GetSQLValueString")) {
function GetSQLValueString($theValue, $theType, $theDefinedValue = "", $theNotDefinedValue = "") 
{
  $theValue = get_magic_quotes_gpc() ? stripslashes($theValue) : $theValue;

  $theValue = function_exists("mysql_real_escape_string") ? mysql_real_escape_string($theValue) : mysql_escape_string($theValue);

  switch ($theType) {
    case "text":
      $theValue = ($theValue != "") ? "'" . $theValue . "'" : "NULL";
      break;    
    case "long":
    case "int":
      $theValue = ($theValue != "") ? intval($theValue) : "NULL";
      break;
    case "double":
      $theValue = ($theValue != "") ? "'" . doubleval($theValue) . "'" : "NULL";
      break;
    case "date":
      $theValue = ($theValue != "") ? "'" . $theValue . "'" : "NULL";
      break;
    case "defined":
      $theValue = ($theValue != "") ? $theDefinedValue : $theNotDefinedValue;
      break;
  }
  return $theValue;
}
}

//$sdirectory="";
//start Trigger_FileUpload trigger
function Trigger_FileUpload(&$tNG) {
  $uploadObj = new tNG_FileUpload($tNG);
  $uploadObj->setFormFieldName("filename");
  $uploadObj->setDbFieldName("filename");
  $uploadObj->setFolder("WocketsData\\{relative_path}\\");
  $uploadObj->setMaxSize(5000);
  $uploadObj->setAllowedExtensions("txt, xml, PLFormat, csv, wockets");
  $uploadObj->setRename("auto");
  return $uploadObj->Execute();
}
//end Trigger_FileUpload trigger

$_POST['server_date']=date("Y-m-d H:m:s");
// Make an insert transaction instance
$ins_FILE_UPLOAD = new tNG_insert($conn_Wockets);
$tNGs->addTransaction($ins_FILE_UPLOAD);
// Register triggers
$ins_FILE_UPLOAD->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_FILE_UPLOAD->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_FILE_UPLOAD->registerTrigger("AFTER", "Trigger_FileUpload", 97);
// Add columns
$ins_FILE_UPLOAD->setTable("FILE_UPLOAD");
$ins_FILE_UPLOAD->addColumn("filename", "FILE_TYPE", "FILES", "filename");
$ins_FILE_UPLOAD->addColumn("relative_path", "STRING_TYPE", "POST", "relative_path");
$ins_FILE_UPLOAD->addColumn("sender_date", "STRING_TYPE", "POST", "sender_date");
$ins_FILE_UPLOAD->addColumn("server_date", "STRING_TYPE", "POST", "server_date");
$ins_FILE_UPLOAD->addColumn("imei", "STRING_TYPE", "POST", "imei");
$ins_FILE_UPLOAD->setPrimaryKey("id", "NUMERIC_TYPE");

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsFILE_UPLOAD = $tNGs->getRecordset("FILE_UPLOAD");
$row_rsFILE_UPLOAD = mysql_fetch_assoc($rsFILE_UPLOAD);
$totalRows_rsFILE_UPLOAD = mysql_num_rows($rsFILE_UPLOAD);
?>
<?php
if ($_POST['KT_Insert1'])
	$file =  getcwd()."/WocketsData/".$_POST['relative_path']."/".$_FILES['filename']['name'];
?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<?php
if (!$_POST['KT_Insert1'])
{
?>
<link href="includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="includes/common/js/base.js" type="text/javascript"></script>
<script src="includes/common/js/utility.js" type="text/javascript"></script>
<script src="includes/skins/style.js" type="text/javascript"></script>
<?php echo $tNGs->displayValidationRules();?>

<?php } ?>
</head>

<body>

<?php
if (!$_POST['KT_Insert1'])
{
?>

<?php
	echo $tNGs->getErrorMsg();
?>
<form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>" enctype="multipart/form-data">
  <table cellpadding="2" cellspacing="0" class="KT_tngtable">
    <tr>
      <td class="KT_th"><label for="filename">Filename:</label></td>
      <td><input type="file" name="filename" id="filename" size="32" />
          <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "filename"); ?> </td>
    </tr>
    <tr>
      <td class="KT_th"><label for="relative_path">Relative Path:</label></td>
      <td><input type="text" name="relative_path" id="relative_path" value="<?php echo KT_escapeAttribute($row_rsFILE_UPLOAD['relative_path']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("relative_path");?> <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "relative_path"); ?> </td>
    </tr>
    <tr>
      <td class="KT_th"><label for="sender_date">Sender Date:</label></td>
      <td><input type="text" name="sender_date" id="sender_date" value="<?php echo KT_formatDate($row_rsFILE_UPLOAD['sender_date']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("sender_date");?> <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "sender_date"); ?> </td>
    </tr>
    <tr>
      <td class="KT_th"><label for="imei">IMEI:</label></td>
      <td><input type="text" name="imei" id="imei" value="<?php echo KT_escapeAttribute($row_rsFILE_UPLOAD['imei']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("imei");?> <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "imei"); ?> </td>
    </tr>
    <tr class="KT_buttons">
      <td colspan="2"><input type="submit" name="KT_Insert1" id="KT_Insert1" value="Insert record" />
      </td>
    </tr>
  </table>
  <input type="hidden" name="server_date" id="server_date" value="<?php  echo date("Y-m-d H:m:s");?>" />
</form>
<p>&nbsp;</p>

<?php }else{ 

	//File successfully uploaded
	echo "<filemd5>".md5_file($file)."</filemd5>\n";
	if (strrpos($file,"SummaryAC-",0)>0)
	{
			$filenameWithoutExt = explode(".", basename($file));
			$splittedFile = explode("-", $filenameWithoutExt[0]);
			$wocketNum = $splittedFile[2];
			$wornLocation = $splittedFile[1];
					
			if (($handle = fopen("$file", "r")) !== FALSE) 
			{
    			while (($data = fgetcsv($handle, 1000, ",")) !== FALSE) 
				{
	        		if (count($data)==6)
					{
						$datetime = $data[3];
	        			$unixtime = $data[4];
        				$activity = $data[5];
						
						mysql_select_db($database_Wockets, $Wockets);	
						$query_Recordset3 = "INSERT INTO activity (subject_id, date_time, unix_time, activity, device_num) VALUES (".$participant_id.",'".$datetime."', '".$unixtime."','".$activity."', ".$wocketNum.")";
						//echo "$query_Recordset3";
//						$Recordset3 = mysql_query($query_Recordset3, $Wockets) or die(mysql_error());
												        		
					}
				}
			}		
	}else if (strrpos($file,"log.csv",0)>0)
	{
		if (($handle = fopen("$file", "r")) !== FALSE) 
			{
    			while (($data = fgetcsv($handle, 1000, ",")) !== FALSE) 
				{
	        		if (count($data)==18)
					{
						$unixtime = $data[0];
        				$datetime = $data[3];
        				$batteryLife = $data[4];
        				$currentConsumptionChange = $data[6];
        				$receivedSample1 = $data[8];
        				$receivedSample2 = $data[13];
						
						mysql_select_db($database_Wockets, $Wockets);	
						$query_Recordset4 = "INSERT INTO phone_battery_tracking (subject_id, date_time, unix_time, battery, current_change) VALUES (".$participant_id.",'".$datetime."', '".$unixtime."','".$batteryLife."',".$currentConsumptionChange.")";
		//				$Recordset4 = mysql_query($query_Recordset4, $Wockets) or die(mysql_error());
						
						
						$query_Recordset5 = "INSERT INTO received_samples (subject_id, date_time, unix_time, wocket1_received, wocket2_received) VALUES (".$participant_id.",'".$datetime."', '".$unixtime."',".$receivedSample1.",".$receivedSample2.")";
	//					$Recordset5 = mysql_query($query_Recordset5, $Wockets) or die(mysql_error());
												        		
					}
				}
			}		
	}

?>

<?php } ?>
</body>
</html>
<?php
mysql_free_result($Recordset1);
mysql_free_result($Recordset3);
mysql_free_result($Recordset4);
mysql_free_result($Recordset5);
flush();
?>
