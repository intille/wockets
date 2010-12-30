<?php require_once('../Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('../includes/common/KT_common.php');

// Load the tNG classes
require_once('../includes/tng/tNG.inc.php');

// Load the KT_back class
require_once('../includes/nxt/KT_back.php');

// Make a transaction dispatcher instance
$tNGs = new tNG_dispatcher("../");

// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);

//Start Restrict Access To Page
$restrict = new tNG_RestrictAccess($conn_Wockets, "../");
//Grand Levels: Any
$restrict->Execute();
//End Restrict Access To Page

// Start trigger
$formValidation = new tNG_FormValidation();
$formValidation->addField("mac", true, "text", "", "", "", "");
$formValidation->addField("hardware", true, "text", "", "", "", "");
$formValidation->addField("firmware", true, "text", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

//start Trigger_FileDelete2 trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileDelete2(&$tNG) {
  $deleteObj = new tNG_FileDelete($tNG);
  $deleteObj->setFolder("../Data/Wockets/Configuration/{mac}/");
  $deleteObj->setDbFieldName("teststatusfile");
  return $deleteObj->Execute();
}
//end Trigger_FileDelete2 trigger

//start Trigger_FileUpload2 trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileUpload2(&$tNG) {
  $uploadObj = new tNG_FileUpload($tNG);
  $uploadObj->setFormFieldName("teststatusfile");
  $uploadObj->setDbFieldName("teststatusfile");
  $uploadObj->setFolder("../Data/Wockets/Configuration/{mac}/");
  $uploadObj->setMaxSize(1500);
  $uploadObj->setAllowedExtensions("txt");
  $uploadObj->setRename("auto");
  return $uploadObj->Execute();
}
//end Trigger_FileUpload2 trigger

//start Trigger_FileDelete1 trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileDelete1(&$tNG) {
  $deleteObj = new tNG_FileDelete($tNG);
  $deleteObj->setFolder("../Data/Wockets/Configuration/{mac}/");
  $deleteObj->setDbFieldName("batteryfile");
  return $deleteObj->Execute();
}
//end Trigger_FileDelete1 trigger

//start Trigger_FileUpload1 trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileUpload1(&$tNG) {
  $uploadObj = new tNG_FileUpload($tNG);
  $uploadObj->setFormFieldName("batteryfile");
  $uploadObj->setDbFieldName("batteryfile");
  $uploadObj->setFolder("../Data/Wockets/Configuration/{mac}/");
  $uploadObj->setMaxSize(1500);
  $uploadObj->setAllowedExtensions("txt");
  $uploadObj->setRename("auto");
  return $uploadObj->Execute();
}
//end Trigger_FileUpload1 trigger

//start Trigger_FileDelete trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileDelete(&$tNG) {
  $deleteObj = new tNG_FileDelete($tNG);
  $deleteObj->setFolder("../Data/Wockets/Configuration/{mac}/");
  $deleteObj->setDbFieldName("xmlfile");
  return $deleteObj->Execute();
}
//end Trigger_FileDelete trigger

//start Trigger_FileUpload trigger
//remove this line if you want to edit the code by hand 
function Trigger_FileUpload(&$tNG) {
  $uploadObj = new tNG_FileUpload($tNG);
  $uploadObj->setFormFieldName("xmlfile");
  $uploadObj->setDbFieldName("xmlfile");
  $uploadObj->setFolder("../Data/Wockets/Configuration/{mac}/");
  $uploadObj->setMaxSize(1500);
  $uploadObj->setAllowedExtensions("xml");
  $uploadObj->setRename("auto");
  return $uploadObj->Execute();
}
//end Trigger_FileUpload trigger

// Make an insert transaction instance
$ins_WOCKETS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_WOCKETS);
// Register triggers
$ins_WOCKETS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_WOCKETS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_WOCKETS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
$ins_WOCKETS->registerTrigger("AFTER", "Trigger_FileUpload", 97);
$ins_WOCKETS->registerTrigger("AFTER", "Trigger_FileUpload1", 97);
$ins_WOCKETS->registerTrigger("AFTER", "Trigger_FileUpload2", 97);
// Add columns
$ins_WOCKETS->setTable("WOCKETS");
$ins_WOCKETS->addColumn("mac", "STRING_TYPE", "POST", "mac", "0006660");
$ins_WOCKETS->addColumn("color", "STRING_TYPE", "POST", "color");
$ins_WOCKETS->addColumn("hardware", "STRING_TYPE", "POST", "hardware");
$ins_WOCKETS->addColumn("firmware", "STRING_TYPE", "POST", "firmware");
$ins_WOCKETS->addColumn("xmlfile", "FILE_TYPE", "FILES", "xmlfile");
$ins_WOCKETS->addColumn("batteryfile", "FILE_TYPE", "FILES", "batteryfile");
$ins_WOCKETS->addColumn("teststatusfile", "FILE_TYPE", "FILES", "teststatusfile");
$ins_WOCKETS->addColumn("notes", "STRING_TYPE", "POST", "notes");
$ins_WOCKETS->setPrimaryKey("id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_WOCKETS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_WOCKETS);
// Register triggers
$upd_WOCKETS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_WOCKETS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_WOCKETS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
$upd_WOCKETS->registerTrigger("AFTER", "Trigger_FileUpload", 97);
$upd_WOCKETS->registerTrigger("AFTER", "Trigger_FileUpload1", 97);
$upd_WOCKETS->registerTrigger("AFTER", "Trigger_FileUpload2", 97);
// Add columns
$upd_WOCKETS->setTable("WOCKETS");
$upd_WOCKETS->addColumn("mac", "STRING_TYPE", "POST", "mac");
$upd_WOCKETS->addColumn("color", "STRING_TYPE", "POST", "color");
$upd_WOCKETS->addColumn("hardware", "STRING_TYPE", "POST", "hardware");
$upd_WOCKETS->addColumn("firmware", "STRING_TYPE", "POST", "firmware");
$upd_WOCKETS->addColumn("xmlfile", "FILE_TYPE", "FILES", "xmlfile");
$upd_WOCKETS->addColumn("batteryfile", "FILE_TYPE", "FILES", "batteryfile");
$upd_WOCKETS->addColumn("teststatusfile", "FILE_TYPE", "FILES", "teststatusfile");
$upd_WOCKETS->addColumn("notes", "STRING_TYPE", "POST", "notes");
$upd_WOCKETS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make an instance of the transaction object
$del_WOCKETS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_WOCKETS);
// Register triggers
$del_WOCKETS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_WOCKETS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
$del_WOCKETS->registerTrigger("AFTER", "Trigger_FileDelete", 98);
$del_WOCKETS->registerTrigger("AFTER", "Trigger_FileDelete1", 98);
$del_WOCKETS->registerTrigger("AFTER", "Trigger_FileDelete2", 98);
// Add columns
$del_WOCKETS->setTable("WOCKETS");
$del_WOCKETS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make a logout transaction instance
$logoutTransaction = new tNG_logoutTransaction($conn_Wockets);
$tNGs->addTransaction($logoutTransaction);
// Register triggers
$logoutTransaction->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "GET", "KT_logout_now");
$logoutTransaction->registerTrigger("END", "Trigger_Default_Redirect", 99, "../index.php");
// Add columns
// End of logout transaction instance

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rsWOCKETS = $tNGs->getRecordset("WOCKETS");
$row_rsWOCKETS = mysql_fetch_assoc($rsWOCKETS);
$totalRows_rsWOCKETS = mysql_num_rows($rsWOCKETS);

// Get the transaction recordset
$rscustom = $tNGs->getRecordset("custom");
$row_rscustom = mysql_fetch_assoc($rscustom);
$totalRows_rscustom = mysql_num_rows($rscustom);
?><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<script src="../includes/cssmenus2/js/cssmenus.js" type="text/javascript"></script>
<link href="../includes/cssmenus2/skins/interakt_blue/horizontal.css" rel="stylesheet" type="text/css" />
<script src="../includes/common/js/base.js" type="text/javascript"></script>
<script src="../includes/common/js/utility.js" type="text/javascript"></script>

<link href="../includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="../includes/common/js/base.js" type="text/javascript"></script>
<script src="../includes/common/js/utility.js" type="text/javascript"></script>
<script src="../includes/skins/style.js" type="text/javascript"></script>
<?php echo $tNGs->displayValidationRules();?>
<script src="../includes/nxt/scripts/form.js" type="text/javascript"></script>
<script src="../includes/nxt/scripts/form.js.php" type="text/javascript"></script>
<script type="text/javascript">
$NXT_FORM_SETTINGS = {
  duplicate_buttons: true,
  show_as_grid: true,
  merge_down_value: true
}
</script>
</head>

<body>


<p> </p>
<div id="cssMenu1" class="horizontal" >
  <ul class="interakt_blue">
    <li> <a href="../main.php" title="Logout">Home</a> </li>
    <li> <a href="#" title="Study">Study</a>
        <ul>
          <li> <a href="phones.php" title="Phones">Phones</a> </li>
          <li> <a href="wockets.php" title="Wockets">Wockets</a> </li>
          <li> <a href="participants.php" title="Participants">Participants</a> </li>
      </ul>
    </li>
    <li> <a href="#" title="Export">Actions</a>
        <ul>
          <li> <a href="participant_phone.php" title="Assign phone to participant">Assign Phone</a> </li>
          <li> <a href="participant_wocket.php" title="Assign Wocket">Assign Wocket</a> </li>
          <li> <a href="ExportData.php" title="Export Data">Export Data</a> </li>
      </ul>
    </li>
    <li> <a href="#" title="Advanced">Advanced</a>
        <ul>
          <li> <a href="accounts.php" title="User Accounts">User Accounts</a> </li>
          <li> <a href="Files.php" title="Files">Files</a> </li>
          <li> <a href="phone_stats.php" title="Phone Statistics">Phone Statistics</a> </li>
          <li> <a href="wocket_stats.php" title="Wockets Statistics">Wockets Statistics</a> </li>
      </ul>
    </li>
    <li> <a href="<?php echo $logoutTransaction->getLogoutLink(); ?>" title="">Logout</a> </li>
  </ul>
  <br />
  <script type="text/javascript">
	<!--
    var obj_cssMenu1 = new CSSMenu("cssMenu1");
    obj_cssMenu1.setTimeouts(400, 200, 800);
    obj_cssMenu1.setSubMenuOffset(0, 0, 0, 0);
    obj_cssMenu1.setHighliteCurrent(true);
    obj_cssMenu1.show();
   //-->
  </script>
</div>
<p>&nbsp;</p>

<div class="KT_tng">
  <h1>
    <?php 
// Show IF Conditional region1 
if (@$_GET['id'] == "") {
?>
      <?php echo NXT_getResource("Insert_FH"); ?>
      <?php 
// else Conditional region1
} else { ?>
      <?php echo NXT_getResource("Update_FH"); ?>
      <?php } 
// endif Conditional region1
?>
    WOCKETS </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>" enctype="multipart/form-data">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsWOCKETS > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="mac_<?php echo $cnt1; ?>">MAC:</label></td>
            <td><input type="text" name="mac_<?php echo $cnt1; ?>" id="mac_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsWOCKETS['mac']); ?>" size="32" maxlength="45" />
                <?php echo $tNGs->displayFieldHint("mac");?> <?php echo $tNGs->displayFieldError("WOCKETS", "mac", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="color_<?php echo $cnt1; ?>">Color:</label></td>
            <td><select name="color_<?php echo $cnt1; ?>" id="color_<?php echo $cnt1; ?>">
              <option value="blue" <?php if (!(strcmp("blue", KT_escapeAttribute($row_rsWOCKETS['color'])))) {echo "SELECTED";} ?>>Blue</option>
              <option value="orange" <?php if (!(strcmp("orange", KT_escapeAttribute($row_rsWOCKETS['color'])))) {echo "SELECTED";} ?>>Orange</option>
              <option value="green" <?php if (!(strcmp("green", KT_escapeAttribute($row_rsWOCKETS['color'])))) {echo "SELECTED";} ?>>Green</option>
              <option value="red" <?php if (!(strcmp("red", KT_escapeAttribute($row_rsWOCKETS['color'])))) {echo "SELECTED";} ?>>Red</option>
            </select>
                <?php echo $tNGs->displayFieldError("WOCKETS", "color", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="hardware_<?php echo $cnt1; ?>">Hardware Version:</label></td>
            <td><select name="hardware_<?php echo $cnt1; ?>" id="hardware_<?php echo $cnt1; ?>">
              <option value="V1.1" <?php if (!(strcmp("V1.1", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V1.1</option>
              <option value="V1.2" <?php if (!(strcmp("V1.2", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V1.2</option>
              <option value="V2.0" <?php if (!(strcmp("V2.0", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V2.0</option>
              <option value="V2.1" <?php if (!(strcmp("V2.1", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V2.1</option>
              <option value="V2.2" <?php if (!(strcmp("V2.2", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V2.2</option>
              <option value="V3.0" <?php if (!(strcmp("V3.0", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V3.0</option>
              <option value="V3.1" <?php if (!(strcmp("V3.1", KT_escapeAttribute($row_rsWOCKETS['hardware'])))) {echo "SELECTED";} ?>>V3.1</option>
            </select>
                <?php echo $tNGs->displayFieldError("WOCKETS", "hardware", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="firmware_<?php echo $cnt1; ?>">Firmware:</label></td>
            <td><select name="firmware_<?php echo $cnt1; ?>" id="firmware_<?php echo $cnt1; ?>">
              <option value="V1" <?php if (!(strcmp("V1", KT_escapeAttribute($row_rsWOCKETS['firmware'])))) {echo "SELECTED";} ?>>V1</option>
              <option value="V2" <?php if (!(strcmp("V2", KT_escapeAttribute($row_rsWOCKETS['firmware'])))) {echo "SELECTED";} ?>>V2</option>
              <option value="V3" <?php if (!(strcmp("V3", KT_escapeAttribute($row_rsWOCKETS['firmware'])))) {echo "SELECTED";} ?>>V3</option>
            </select>
                <?php echo $tNGs->displayFieldError("WOCKETS", "firmware", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="xmlfile_<?php echo $cnt1; ?>">Xmlfile:</label></td>
            <td><input type="file" name="xmlfile_<?php echo $cnt1; ?>" id="xmlfile_<?php echo $cnt1; ?>" size="32" />
                <?php echo $tNGs->displayFieldError("WOCKETS", "xmlfile", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="batteryfile_<?php echo $cnt1; ?>">Batteryfile:</label></td>
            <td><input type="file" name="batteryfile_<?php echo $cnt1; ?>" id="batteryfile_<?php echo $cnt1; ?>" size="32" />
                <?php echo $tNGs->displayFieldError("WOCKETS", "batteryfile", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="teststatusfile_<?php echo $cnt1; ?>">Teststatusfile:</label></td>
            <td><input type="file" name="teststatusfile_<?php echo $cnt1; ?>" id="teststatusfile_<?php echo $cnt1; ?>" size="32" />
                <?php echo $tNGs->displayFieldError("WOCKETS", "teststatusfile", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="notes_<?php echo $cnt1; ?>">Notes:</label></td>
            <td><textarea name="notes_<?php echo $cnt1; ?>" id="notes_<?php echo $cnt1; ?>" cols="50" rows="5"><?php echo KT_escapeAttribute($row_rsWOCKETS['notes']); ?></textarea>
                <?php echo $tNGs->displayFieldHint("notes");?> <?php echo $tNGs->displayFieldError("WOCKETS", "notes", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_WOCKETS_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsWOCKETS['kt_pk_WOCKETS']); ?>" />
        <?php } while ($row_rsWOCKETS = mysql_fetch_assoc($rsWOCKETS)); ?>
      <div class="KT_bottombuttons">
        <div>
          <?php 
      // Show IF Conditional region1
      if (@$_GET['id'] == "") {
      ?>
            <input type="submit" name="KT_Insert1" id="KT_Insert1" value="<?php echo NXT_getResource("Insert_FB"); ?>" />
            <?php 
      // else Conditional region1
      } else { ?>
            <div class="KT_operations">
              <input type="submit" name="KT_Insert1" value="<?php echo NXT_getResource("Insert as new_FB"); ?>" onclick="nxt_form_insertasnew(this, 'id')" />
            </div>
            <input type="submit" name="KT_Update1" value="<?php echo NXT_getResource("Update_FB"); ?>" />
            <input type="submit" name="KT_Delete1" value="<?php echo NXT_getResource("Delete_FB"); ?>" onclick="return confirm('<?php echo NXT_getResource("Are you sure?"); ?>');" />
            <?php }
      // endif Conditional region1
      ?>
          <input type="button" name="KT_Cancel1" value="<?php echo NXT_getResource("Cancel_FB"); ?>" onclick="return UNI_navigateCancel(event, '../includes/nxt/back.php')" />
        </div>
      </div>
    </form>
  </div>
  <br class="clearfixplain" />
</div>
<p>&nbsp;</p>
</body>
</html>
