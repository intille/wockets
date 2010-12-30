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
$formValidation->addField("participant_id", true, "numeric", "", "", "", "");
$formValidation->addField("wocket_id", true, "numeric", "", "", "", "");
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

mysql_select_db($database_Wockets, $Wockets);
$query_Recordset1 = "SELECT * FROM PARTICIPANTS ORDER BY last_name ASC";
$Recordset1 = mysql_query($query_Recordset1, $Wockets) or die(mysql_error());
$row_Recordset1 = mysql_fetch_assoc($Recordset1);
$totalRows_Recordset1 = mysql_num_rows($Recordset1);

mysql_select_db($database_Wockets, $Wockets);
$query_Recordset2 = "SELECT * FROM WOCKETS ORDER BY mac ASC";
$Recordset2 = mysql_query($query_Recordset2, $Wockets) or die(mysql_error());
$row_Recordset2 = mysql_fetch_assoc($Recordset2);
$totalRows_Recordset2 = mysql_num_rows($Recordset2);

mysql_select_db($database_Wockets, $Wockets);
$query_Recordset3 = "SELECT last_name, id FROM PARTICIPANTS ORDER BY last_name";
$Recordset3 = mysql_query($query_Recordset3, $Wockets) or die(mysql_error());
$row_Recordset3 = mysql_fetch_assoc($Recordset3);
$totalRows_Recordset3 = mysql_num_rows($Recordset3);

mysql_select_db($database_Wockets, $Wockets);
$query_Recordset4 = "SELECT mac, id FROM WOCKETS ORDER BY mac";
$Recordset4 = mysql_query($query_Recordset4, $Wockets) or die(mysql_error());
$row_Recordset4 = mysql_fetch_assoc($Recordset4);
$totalRows_Recordset4 = mysql_num_rows($Recordset4);

// Make an insert transaction instance
$ins_PARTICIPANT_WOCKETS = new tNG_multipleInsert($conn_Wockets);
$tNGs->addTransaction($ins_PARTICIPANT_WOCKETS);
// Register triggers
$ins_PARTICIPANT_WOCKETS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Insert1");
$ins_PARTICIPANT_WOCKETS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$ins_PARTICIPANT_WOCKETS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$ins_PARTICIPANT_WOCKETS->setTable("PARTICIPANT_WOCKETS");
$ins_PARTICIPANT_WOCKETS->addColumn("participant_id", "NUMERIC_TYPE", "POST", "participant_id");
$ins_PARTICIPANT_WOCKETS->addColumn("wocket_id", "NUMERIC_TYPE", "POST", "wocket_id");
$ins_PARTICIPANT_WOCKETS->setPrimaryKey("participant_id", "NUMERIC_TYPE");

// Make an update transaction instance
$upd_PARTICIPANT_WOCKETS = new tNG_multipleUpdate($conn_Wockets);
$tNGs->addTransaction($upd_PARTICIPANT_WOCKETS);
// Register triggers
$upd_PARTICIPANT_WOCKETS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Update1");
$upd_PARTICIPANT_WOCKETS->registerTrigger("BEFORE", "Trigger_Default_FormValidation", 10, $formValidation);
$upd_PARTICIPANT_WOCKETS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$upd_PARTICIPANT_WOCKETS->setTable("PARTICIPANT_WOCKETS");
$upd_PARTICIPANT_WOCKETS->addColumn("participant_id", "NUMERIC_TYPE", "POST", "participant_id");
$upd_PARTICIPANT_WOCKETS->addColumn("wocket_id", "NUMERIC_TYPE", "POST", "wocket_id");
$upd_PARTICIPANT_WOCKETS->setPrimaryKey("participant_id", "NUMERIC_TYPE", "GET", "participant_id");

// Make an instance of the transaction object
$del_PARTICIPANT_WOCKETS = new tNG_multipleDelete($conn_Wockets);
$tNGs->addTransaction($del_PARTICIPANT_WOCKETS);
// Register triggers
$del_PARTICIPANT_WOCKETS->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "POST", "KT_Delete1");
$del_PARTICIPANT_WOCKETS->registerTrigger("END", "Trigger_Default_Redirect", 99, "../includes/nxt/back.php");
// Add columns
$del_PARTICIPANT_WOCKETS->setTable("PARTICIPANT_WOCKETS");
$del_PARTICIPANT_WOCKETS->setPrimaryKey("participant_id", "NUMERIC_TYPE", "GET", "participant_id");

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
$rsPARTICIPANT_WOCKETS = $tNGs->getRecordset("PARTICIPANT_WOCKETS");
$row_rsPARTICIPANT_WOCKETS = mysql_fetch_assoc($rsPARTICIPANT_WOCKETS);
$totalRows_rsPARTICIPANT_WOCKETS = mysql_num_rows($rsPARTICIPANT_WOCKETS);

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
if (@$_GET['participant_id'] == "") {
?>
      <?php echo NXT_getResource("Insert_FH"); ?>
      <?php 
// else Conditional region1
} else { ?>
      <?php echo NXT_getResource("Update_FH"); ?>
      <?php } 
// endif Conditional region1
?>
    PARTICIPANT_WOCKETS </h1>
  <div class="KT_tngform">
    <form method="post" id="form1" action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>">
      <?php $cnt1 = 0; ?>
      <?php do { ?>
        <?php $cnt1++; ?>
        <?php 
// Show IF Conditional region1 
if (@$totalRows_rsPARTICIPANT_WOCKETS > 1) {
?>
          <h2><?php echo NXT_getResource("Record_FH"); ?> <?php echo $cnt1; ?></h2>
          <?php } 
// endif Conditional region1
?>
        <table cellpadding="2" cellspacing="0" class="KT_tngtable">
          <tr>
            <td class="KT_th"><label for="participant_id_<?php echo $cnt1; ?>">Participant:</label></td>
            <td><select name="participant_id_<?php echo $cnt1; ?>" id="participant_id_<?php echo $cnt1; ?>">
              <option value=""><?php echo NXT_getResource("Select one..."); ?></option>
              <?php 
do {  
?>
              <option value="<?php echo $row_Recordset1['id']?>"<?php if (!(strcmp($row_Recordset1['id'], $row_rsPARTICIPANT_WOCKETS['participant_id']))) {echo "SELECTED";} ?>><?php echo $row_Recordset1['last_name']?></option>
              <?php
} while ($row_Recordset1 = mysql_fetch_assoc($Recordset1));
  $rows = mysql_num_rows($Recordset1);
  if($rows > 0) {
      mysql_data_seek($Recordset1, 0);
	  $row_Recordset1 = mysql_fetch_assoc($Recordset1);
  }
?>
            </select>
                <?php echo $tNGs->displayFieldError("PARTICIPANT_WOCKETS", "participant_id", $cnt1); ?> </td>
          </tr>
          <tr>
            <td class="KT_th"><label for="wocket_id_<?php echo $cnt1; ?>">Wocket:</label></td>
            <td><select name="wocket_id_<?php echo $cnt1; ?>" id="wocket_id_<?php echo $cnt1; ?>">
              <option value=""><?php echo NXT_getResource("Select one..."); ?></option>
              <?php 
do {  
?>
              <option value="<?php echo $row_Recordset2['id']?>"<?php if (!(strcmp($row_Recordset2['id'], $row_rsPARTICIPANT_WOCKETS['wocket_id']))) {echo "SELECTED";} ?>><?php echo $row_Recordset2['mac']?></option>
              <?php
} while ($row_Recordset2 = mysql_fetch_assoc($Recordset2));
  $rows = mysql_num_rows($Recordset2);
  if($rows > 0) {
      mysql_data_seek($Recordset2, 0);
	  $row_Recordset2 = mysql_fetch_assoc($Recordset2);
  }
?>
            </select>
                <?php echo $tNGs->displayFieldError("PARTICIPANT_WOCKETS", "wocket_id", $cnt1); ?> </td>
          </tr>
        </table>
        <input type="hidden" name="kt_pk_PARTICIPANT_WOCKETS_<?php echo $cnt1; ?>" class="id_field" value="<?php echo KT_escapeAttribute($row_rsPARTICIPANT_WOCKETS['kt_pk_PARTICIPANT_WOCKETS']); ?>" />
        <?php } while ($row_rsPARTICIPANT_WOCKETS = mysql_fetch_assoc($rsPARTICIPANT_WOCKETS)); ?>
      <div class="KT_bottombuttons">
        <div>
          <?php 
      // Show IF Conditional region1
      if (@$_GET['participant_id'] == "") {
      ?>
            <input type="submit" name="KT_Insert1" id="KT_Insert1" value="<?php echo NXT_getResource("Insert_FB"); ?>" />
            <?php 
      // else Conditional region1
      } else { ?>
            <div class="KT_operations">
              <input type="submit" name="KT_Insert1" value="<?php echo NXT_getResource("Insert as new_FB"); ?>" onclick="nxt_form_insertasnew(this, 'participant_id')" />
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
<?php
mysql_free_result($Recordset1);

mysql_free_result($Recordset2);

mysql_free_result($Recordset3);

mysql_free_result($Recordset4);
?>
