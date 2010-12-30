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
$ins_PHONE_STATS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_PHONE_STATS);
// Register triggers
$ins_PHONE_STATS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_PHONE_STATS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_PHONE_STATS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_PHONE_STATS->setTable("PHONE_STATS");
$ins_PHONE_STATS->addColumn("imei", "STRING_TYPE", "POST", "imei");
$ins_PHONE_STATS->addColumn("server_date", "DATE_TYPE", "POST", "server_date");
$ins_PHONE_STATS->addColumn("sender_date", "DATE_TYPE", "POST", "sender_date");
$ins_PHONE_STATS->addColumn("phone_battery", "NUMERIC_TYPE", "POST", "phone_battery");
$ins_PHONE_STATS->addColumn("mainmemory", "NUMERIC_TYPE", "POST", "mainmemory");
$ins_PHONE_STATS->addColumn("sdmemory", "NUMERIC_TYPE", "POST", "sdmemory");
$ins_PHONE_STATS->addColumn("battery1", "NUMERIC_TYPE", "POST", "battery1");
$ins_PHONE_STATS->addColumn("transmitted_bytes1", "NUMERIC_TYPE", "POST", "transmitted_bytes1");
$ins_PHONE_STATS->addColumn("received_bytes1", "NUMERIC_TYPE", "POST", "received_bytes1");
$ins_PHONE_STATS->addColumn("battery2", "NUMERIC_TYPE", "POST", "battery2");
$ins_PHONE_STATS->addColumn("transmitted_bytes2", "NUMERIC_TYPE", "POST", "transmitted_bytes2");
$ins_PHONE_STATS->addColumn("received_bytes2", "NUMERIC_TYPE", "POST", "received_bytes2");
$ins_PHONE_STATS->setPrimaryKey("id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_PHONE_STATS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_PHONE_STATS);
// Register triggers
$upd_PHONE_STATS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_PHONE_STATS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_PHONE_STATS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_PHONE_STATS->setTable("PHONE_STATS");
$upd_PHONE_STATS->addColumn("imei", "STRING_TYPE", "POST", "imei");
$upd_PHONE_STATS->addColumn("server_date", "DATE_TYPE", "POST", "server_date");
$upd_PHONE_STATS->addColumn("sender_date", "DATE_TYPE", "POST", "sender_date");
$upd_PHONE_STATS->addColumn("phone_battery", "NUMERIC_TYPE", "POST", "phone_battery");
$upd_PHONE_STATS->addColumn("mainmemory", "NUMERIC_TYPE", "POST", "mainmemory");
$upd_PHONE_STATS->addColumn("sdmemory", "NUMERIC_TYPE", "POST", "sdmemory");
$upd_PHONE_STATS->addColumn("battery1", "NUMERIC_TYPE", "POST", "battery1");
$upd_PHONE_STATS->addColumn("transmitted_bytes1", "NUMERIC_TYPE", "POST", "transmitted_bytes1");
$upd_PHONE_STATS->addColumn("received_bytes1", "NUMERIC_TYPE", "POST", "received_bytes1");
$upd_PHONE_STATS->addColumn("battery2", "NUMERIC_TYPE", "POST", "battery2");
$upd_PHONE_STATS->addColumn("transmitted_bytes2", "NUMERIC_TYPE", "POST", "transmitted_bytes2");
$upd_PHONE_STATS->addColumn("received_bytes2", "NUMERIC_TYPE", "POST", "received_bytes2");
$upd_PHONE_STATS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

// Make an instance of the transaction object
$del_PHONE_STATS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_PHONE_STATS);
// Register triggers
$del_PHONE_STATS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_PHONE_STATS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_PHONE_STATS->setTable("PHONE_STATS");
$del_PHONE_STATS->setPrimaryKey("id", "NUMERIC_TYPE", "GET", "id");

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
$rsPHONE_STATS = $tNGs->getRecordset("PHONE_STATS");
$row_rsPHONE_STATS = mysql_fetch_assoc($rsPHONE_STATS);
$totalRows_rsPHONE_STATS = mysql_num_rows($rsPHONE_STATS);

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
    PHONE_STATS </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsPHONE_STATS > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="imei_<?php echo $cnt1; ?>">Imei:</label></td>
            <td><input type="text" name="imei_<?php echo $cnt1; ?>" id="imei_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['imei']); ?>" size="32" maxlength="100" />
                <?php echo $tNGs->displayFieldHint("imei");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "imei", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="server_date_<?php echo $cnt1; ?>">Server_date:</label></td>
            <td><input type="text" name="server_date_<?php echo $cnt1; ?>" id="server_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsPHONE_STATS['server_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("server_date");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "server_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="sender_date_<?php echo $cnt1; ?>">Sender_date:</label></td>
            <td><input type="text" name="sender_date_<?php echo $cnt1; ?>" id="sender_date_<?php echo $cnt1; ?>" value="<?php echo KT_formatDate($row_rsPHONE_STATS['sender_date']); ?>" size="10" maxlength="22" />
                <?php echo $tNGs->displayFieldHint("sender_date");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "sender_date", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="phone_battery_<?php echo $cnt1; ?>">Phone_battery:</label></td>
            <td><input type="text" name="phone_battery_<?php echo $cnt1; ?>" id="phone_battery_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['phone_battery']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("phone_battery");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "phone_battery", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="mainmemory_<?php echo $cnt1; ?>">Mainmemory:</label></td>
            <td><input type="text" name="mainmemory_<?php echo $cnt1; ?>" id="mainmemory_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['mainmemory']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("mainmemory");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "mainmemory", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="sdmemory_<?php echo $cnt1; ?>">Sdmemory:</label></td>
            <td><input type="text" name="sdmemory_<?php echo $cnt1; ?>" id="sdmemory_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['sdmemory']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("sdmemory");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "sdmemory", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="battery1_<?php echo $cnt1; ?>">Battery1:</label></td>
            <td><input type="text" name="battery1_<?php echo $cnt1; ?>" id="battery1_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['battery1']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("battery1");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "battery1", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="transmitted_bytes1_<?php echo $cnt1; ?>">Transmitted_bytes1:</label></td>
            <td><input type="text" name="transmitted_bytes1_<?php echo $cnt1; ?>" id="transmitted_bytes1_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['transmitted_bytes1']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("transmitted_bytes1");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "transmitted_bytes1", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="received_bytes1_<?php echo $cnt1; ?>">Received_bytes1:</label></td>
            <td><input type="text" name="received_bytes1_<?php echo $cnt1; ?>" id="received_bytes1_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['received_bytes1']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("received_bytes1");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "received_bytes1", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="battery2_<?php echo $cnt1; ?>">Battery2:</label></td>
            <td><input type="text" name="battery2_<?php echo $cnt1; ?>" id="battery2_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['battery2']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("battery2");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "battery2", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="transmitted_bytes2_<?php echo $cnt1; ?>">Transmitted_bytes2:</label></td>
            <td><input type="text" name="transmitted_bytes2_<?php echo $cnt1; ?>" id="transmitted_bytes2_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['transmitted_bytes2']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("transmitted_bytes2");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "transmitted_bytes2", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="received_bytes2_<?php echo $cnt1; ?>">Received_bytes2:</label></td>
            <td><input type="text" name="received_bytes2_<?php echo $cnt1; ?>" id="received_bytes2_<?php echo $cnt1; ?>" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['received_bytes2']); ?>" size="7" />
                <?php echo $tNGs->displayFieldHint("received_bytes2");?> <?php echo $tNGs->displayFieldError("PHONE_STATS", "received_bytes2", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_PHONE_STATS_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsPHONE_STATS['kt_pk_PHONE_STATS']); ?>" />
        <?php } while ($row_rsPHONE_STATS = mysql_fetch_assoc($rsPHONE_STATS)); ?>
      <div class="KT_bottombuttons">
        <div>
          <?php 
      // Show IF Conditional region1
      if (@$_GET['id'] == "") {
      ?>
            <?php 
      // else Conditional region1
      } else { ?>
            <div class="KT_operations"></div>
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
