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
$formValidation->addField("filename", true, "numeric", "", "", "", "");
$formValidation->addField("relative_path", true, "text", "", "", "", "");
$tNGs->prepareValidation($formValidation);
// End trigger

// Make an insert transaction instance
$ins_FILE_UPLOAD = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_FILE_UPLOAD);
// Register triggers
$ins_FILE_UPLOAD->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_FILE_UPLOAD->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_FILE_UPLOAD->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_FILE_UPLOAD->setTable("FILE_UPLOAD");
$ins_FILE_UPLOAD->addColumn("filename", "NUMERIC_TYPE", "POST", "filename");
$ins_FILE_UPLOAD->addColumn("relative_path", "STRING_TYPE", "POST", "relative_path");
$ins_FILE_UPLOAD->setPrimaryKey("id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_FILE_UPLOAD = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_FILE_UPLOAD);
// Register triggers
$upd_FILE_UPLOAD->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_FILE_UPLOAD->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_FILE_UPLOAD->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_FILE_UPLOAD->setTable("FILE_UPLOAD");
$upd_FILE_UPLOAD->addColumn("filename", "NUMERIC_TYPE", "POST", "filename");
$upd_FILE_UPLOAD->addColumn("relative_path", "STRING_TYPE", "POST", "relative_path");
$upd_FILE_UPLOAD->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make an instance of the transaction object
$del_FILE_UPLOAD = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_FILE_UPLOAD);
// Register triggers
$del_FILE_UPLOAD->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_FILE_UPLOAD->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_FILE_UPLOAD->setTable("FILE_UPLOAD");
$del_FILE_UPLOAD->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

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
$rsFILE_UPLOAD = $tNGs->getRecordset("FILE_UPLOAD");
$row_rsFILE_UPLOAD = mysql_fetch_assoc($rsFILE_UPLOAD);
$totalRows_rsFILE_UPLOAD = mysql_num_rows($rsFILE_UPLOAD);

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



<?php
	echo $tNGs->getErrorMsg();
?>
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
    FILE_UPLOAD </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsFILE_UPLOAD > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="filename_<?php echo $cnt1; ?>">Filename:</label></td>
            <td><input type="text" name="filename_<?php echo $cnt1; ?>" id="filename_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsFILE_UPLOAD['filename']); ?>" size="32" maxlength="45" />
                <?php echo $tNGs->displayFieldHint("filename");?> <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "filename", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="relative_path_<?php echo $cnt1; ?>">Relative_path:</label></td>
            <td><input type="text" name="relative_path_<?php echo $cnt1; ?>" id="relative_path_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsFILE_UPLOAD['relative_path']); ?>" size="32" />
                <?php echo $tNGs->displayFieldHint("relative_path");?> <?php echo $tNGs->displayFieldError("FILE_UPLOAD", "relative_path", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_FILE_UPLOAD_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsFILE_UPLOAD['kt_pk_FILE_UPLOAD']); ?>" />
        <?php } while ($row_rsFILE_UPLOAD = mysql_fetch_assoc($rsFILE_UPLOAD)); ?>
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
