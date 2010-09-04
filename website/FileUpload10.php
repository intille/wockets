<?php require_once('Connections/Wockets.php'); ?>
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
$tNGs->prepareValidation($formValidation);
// End trigger

//start Trigger_FileUpload trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileUpload(&$tNG) {
  $uploadObj = new tNG_FileUpload($tNG);
  $uploadObj->setFormFieldName("filename");
  $uploadObj->setDbFieldName("filename");
  $uploadObj->setFolder("WocketsData\{relative_path}/");
  $uploadObj->setMaxSize(2000);
  $uploadObj->setAllowedExtensions("PLFormat");
  $uploadObj->setRename("auto");
  return $uploadObj->Execute();
}
//end Trigger_FileUpload trigger

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
$ins_FILE_UPLOAD->setPrimaryKey("id", "NUMERIC_TYPE");

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsFILE_UPLOAD = $tNGs->getRecordset("FILE_UPLOAD");
$row_rsFILE_UPLOAD = mysql_fetch_assoc($rsFILE_UPLOAD);
$totalRows_rsFILE_UPLOAD = mysql_num_rows($rsFILE_UPLOAD);
?><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<link href="includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="includes/common/js/base.js" type="text/javascript"></script>
<script src="includes/common/js/utility.js" type="text/javascript"></script>
<script src="includes/skins/style.js" type="text/javascript"></script>
<?php echo $tNGs->displayValidationRules();?>
</head>

<body>
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
      <td class="KT_th"><label for="relative_path">Relative_path:</label></td>
      <td><input type="text" name="relative_path" id="relative_path" value="<?php echo KT_escapeAttribute($row_rsFILE_UPLOAD['relative_path']); ?>" size="32" />
          <?php echo $tNGs->displayFieldHint("relative_path");?> <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "relative_path"); ?> </td>
    </tr>
    <tr class="KT_buttons">
      <td colspan="2"><input type="submit" name="KT_Insert1" id="KT_Insert1" value="Insert record" />
      </td>
    </tr>
  </table>
</form>
<p>&nbsp;</p>
</body>
</html>
