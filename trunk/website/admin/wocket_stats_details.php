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
$tNGs->prepareValidation($formValidation);
// End trigger

// Make an insert transaction instance
$ins_WOCKET_STATS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_WOCKET_STATS);
// Register triggers
$ins_WOCKET_STATS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_WOCKET_STATS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_WOCKET_STATS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_WOCKET_STATS->setTable("WOCKET_STATS");
$ins_WOCKET_STATS->addColumn("imei", "STRING_TYPE", "POST", "imei");
$ins_WOCKET_STATS->addColumn("server_date", "DATE_TYPE", "POST", "server_date");
$ins_WOCKET_STATS->addColumn("sender_date", "DATE_TYPE", "POST", "sender_date");
$ins_WOCKET_STATS->addColumn("mac", "STRING_TYPE", "POST", "mac");
$ins_WOCKET_STATS->addColumn("wocket_id", "NUMERIC_TYPE", "POST", "wocket_id");
$ins_WOCKET_STATS->addColumn("activity_count", "NUMERIC_TYPE", "POST", "activity_count");
$ins_WOCKET_STATS->setPrimaryKey("id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_WOCKET_STATS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_WOCKET_STATS);
// Register triggers
$upd_WOCKET_STATS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_WOCKET_STATS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_WOCKET_STATS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_WOCKET_STATS->setTable("WOCKET_STATS");
$upd_WOCKET_STATS->addColumn("imei", "STRING_TYPE", "POST", "imei");
$upd_WOCKET_STATS->addColumn("server_date", "DATE_TYPE", "POST", "server_date");
$upd_WOCKET_STATS->addColumn("sender_date", "DATE_TYPE", "POST", "sender_date");
$upd_WOCKET_STATS->addColumn("mac", "STRING_TYPE", "POST", "mac");
$upd_WOCKET_STATS->addColumn("wocket_id", "NUMERIC_TYPE", "POST", "wocket_id");
$upd_WOCKET_STATS->addColumn("activity_count", "NUMERIC_TYPE", "POST", "activity_count");
$upd_WOCKET_STATS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make an instance of the transaction object
$del_WOCKET_STATS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_WOCKET_STATS);
// Register triggers
$del_WOCKET_STATS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_WOCKET_STATS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_WOCKET_STATS->setTable("WOCKET_STATS");
$del_WOCKET_STATS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

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
$rsWOCKET_STATS = $tNGs->getRecordset("WOCKET_STATS");
$row_rsWOCKET_STATS = mysql_fetch_assoc($rsWOCKET_STATS);
$totalRows_rsWOCKET_STATS = mysql_num_rows($rsWOCKET_STATS);

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
    WOCKET_STATS </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsWOCKET_STATS > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="imei_<?php echo $cnt1; ?>">Imei:</label></td>
            <td><input type="text" name="imei_<?php echo $cnt1; ?>" id="imei_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsWOCKET_STATS['imei']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("imei");?> <?php echo $tNGs->displayFieldError("WOCKET_STATS", "imei", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="server_date_<?php echo $cnt1; ?>">Server_date:</label></td>
            <td><input type="text" name="server_date_<?php echo $cnt1; ?>" id="server_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsWOCKET_STATS['server_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("server_date");?> <?php echo $tNGs->displayFieldError("WOCKET_STATS", "server_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="sender_date_<?php echo $cnt1; ?>">Sender_date:</label></td>
            <td><input type="text" name="sender_date_<?php echo $cnt1; ?>" id="sender_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsWOCKET_STATS['sender_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("sender_date");?> <?php echo $tNGs->displayFieldError("WOCKET_STATS", "sender_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="mac_<?php echo $cnt1; ?>">Mac:</label></td>
            <td><input type="text" name="mac_<?php echo $cnt1; ?>" id="mac_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsWOCKET_STATS['mac']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("mac");?> <?php echo $tNGs->displayFieldError("WOCKET_STATS", "mac", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="wocket_id_<?php echo $cnt1; ?>">Wocket_id:</label></td>
            <td><input type="text" name="wocket_id_<?php echo $cnt1; ?>" id="wocket_id_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsWOCKET_STATS['wocket_id']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("wocket_id");?> <?php echo $tNGs->displayFieldError("WOCKET_STATS", "wocket_id", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="activity_count_<?php echo $cnt1; ?>">Activity_count:</label></td>
            <td><input type="text" name="activity_count_<?php echo $cnt1; ?>" id="activity_count_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsWOCKET_STATS['activity_count']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("activity_count");?> <?php echo $tNGs->displayFieldError("WOCKET_STATS", "activity_count", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_WOCKET_STATS_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsWOCKET_STATS['kt_pk_WOCKET_STATS']); ?>" />
        <?php } while ($row_rsWOCKET_STATS = mysql_fetch_assoc($rsWOCKET_STATS)); ?>
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
