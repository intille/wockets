<?php require_once('../Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('../includes/common/KT_common.php');

// Load the required classes
require_once('../includes/tfi/TFI.php');
require_once('../includes/tso/TSO.php');
require_once('../includes/nav/NAV.php');

// Make unified connection variable
$conn_Wockets = new KT_connection($Wockets, $database_Wockets);

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

// Filter
$tfi_listPHONES2 = new TFI_TableFilter($conn_Wockets, "tfi_listPHONES2");
$tfi_listPHONES2->addColumn("PHONES.id", "NUMERIC_TYPE", "id", "=");
$tfi_listPHONES2->addColumn("PHONES.imei", "STRING_TYPE", "imei", "%");
$tfi_listPHONES2->addColumn("PHONES.model", "STRING_TYPE", "model", "%");
$tfi_listPHONES2->addColumn("PHONES.notes", "STRING_TYPE", "notes", "%");
$tfi_listPHONES2->Execute();

// Sorter
$tso_listPHONES2 = new TSO_TableSorter("rsPHONES1", "tso_listPHONES2");
$tso_listPHONES2->addColumn("PHONES.id");
$tso_listPHONES2->addColumn("PHONES.imei");
$tso_listPHONES2->addColumn("PHONES.model");
$tso_listPHONES2->addColumn("PHONES.notes");
$tso_listPHONES2->setDefault("PHONES.id");
$tso_listPHONES2->Execute();

// Navigation
$nav_listPHONES2 = new NAV_Regular("nav_listPHONES2", "rsPHONES1", "../", $_SERVER['PHP_SELF'], 10);

//NeXTenesio3 Special List Recordset
$maxRows_rsPHONES1 = $_SESSION['max_rows_nav_listPHONES2'];
$pageNum_rsPHONES1 = 0;
if (isset($_GET['pageNum_rsPHONES1'])) {
  $pageNum_rsPHONES1 = $_GET['pageNum_rsPHONES1'];
}
$startRow_rsPHONES1 = $pageNum_rsPHONES1 * $maxRows_rsPHONES1;

// Defining List Recordset variable
$NXTFilter_rsPHONES1 = "1=1";
if (isset($_SESSION['filter_tfi_listPHONES2'])) {
  $NXTFilter_rsPHONES1 = $_SESSION['filter_tfi_listPHONES2'];
}
// Defining List Recordset variable
$NXTSort_rsPHONES1 = "PHONES.id";
if (isset($_SESSION['sorter_tso_listPHONES2'])) {
  $NXTSort_rsPHONES1 = $_SESSION['sorter_tso_listPHONES2'];
}
mysql_select_db($database_Wockets, $Wockets);

$query_rsPHONES1 = "SELECT PHONES.id, PHONES.imei, PHONES.model, PHONES.notes FROM PHONES WHERE {$NXTFilter_rsPHONES1} ORDER BY {$NXTSort_rsPHONES1}";
$query_limit_rsPHONES1 = sprintf("%s LIMIT %d, %d", $query_rsPHONES1, $startRow_rsPHONES1, $maxRows_rsPHONES1);
$rsPHONES1 = mysql_query($query_limit_rsPHONES1, $Wockets) or die(mysql_error());
$row_rsPHONES1 = mysql_fetch_assoc($rsPHONES1);

if (isset($_GET['totalRows_rsPHONES1'])) {
  $totalRows_rsPHONES1 = $_GET['totalRows_rsPHONES1'];
} else {
  $all_rsPHONES1 = mysql_query($query_rsPHONES1);
  $totalRows_rsPHONES1 = mysql_num_rows($all_rsPHONES1);
}
$totalPages_rsPHONES1 = ceil($totalRows_rsPHONES1/$maxRows_rsPHONES1)-1;
//End NeXTenesio3 Special List Recordset

$nav_listPHONES2->checkBoundries();
?><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<link href="../includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="../includes/common/js/base.js" type="text/javascript"></script>
<script src="../includes/common/js/utility.js" type="text/javascript"></script>
<script src="../includes/skins/style.js" type="text/javascript"></script>
<script src="../includes/nxt/scripts/list.js" type="text/javascript"></script>
<script src="../includes/nxt/scripts/list.js.php" type="text/javascript"></script>
<script type="text/javascript">
$NXT_LIST_SETTINGS = {
  duplicate_buttons: true,
  duplicate_navigation: true,
  row_effects: true,
  show_as_buttons: true,
  record_counter: true
}
</script>
<style type="text/css">
  /* NeXTensio3 List row settings */
  .KT_col_id {width:140px; overflow:hidden;}
  .KT_col_imei {width:140px; overflow:hidden;}
  .KT_col_model {width:140px; overflow:hidden;}
  .KT_col_notes {width:140px; overflow:hidden;}
</style>
</head>

<body>

<div class="KT_tng" id="listPHONES2">
  <h1> PHONES
    <?php
  $nav_listPHONES2->Prepare();
  require("../includes/nav/NAV_Text_Statistics.inc.php");
?>
  </h1>
  <div class="KT_tnglist">
    <form action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>" method="post" id="form1">
      <div class="KT_options"> <a href="<?php echo $nav_listPHONES2->getShowAllLink(); ?>"><?php echo NXT_getResource("Show"); ?>
            <?php 
  // Show IF Conditional region1
  if (@$_GET['show_all_nav_listPHONES2'] == 1) {
?>
              <?php echo $_SESSION['default_max_rows_nav_listPHONES2']; ?>
              <?php 
  // else Conditional region1
  } else { ?>
              <?php echo NXT_getResource("all"); ?>
              <?php } 
  // endif Conditional region1
?>
            <?php echo NXT_getResource("records"); ?></a> &nbsp;
        &nbsp;
                            <?php 
  // Show IF Conditional region2
  if (@$_SESSION['has_filter_tfi_listPHONES2'] == 1) {
?>
                              <a href="<?php echo $tfi_listPHONES2->getResetFilterLink(); ?>"><?php echo NXT_getResource("Reset filter"); ?></a>
                              <?php 
  // else Conditional region2
  } else { ?>
                              <a href="<?php echo $tfi_listPHONES2->getShowFilterLink(); ?>"><?php echo NXT_getResource("Show filter"); ?></a>
                              <?php } 
  // endif Conditional region2
?>
      </div>
      <table cellpadding="2" cellspacing="0" class="KT_tngtable">
        <thead>
          <tr class="KT_row_order">
            <th> <input type="checkbox" name="KT_selAll" id="KT_selAll"/>
            </th>
            <th id="id" class="KT_sorter KT_col_id <?php echo $tso_listPHONES2->getSortIcon('PHONES.id'); ?>"> <a href="<?php echo $tso_listPHONES2->getSortLink('PHONES.id'); ?>">ID</a> </th>
            <th id="imei" class="KT_sorter KT_col_imei <?php echo $tso_listPHONES2->getSortIcon('PHONES.imei'); ?>"> <a href="<?php echo $tso_listPHONES2->getSortLink('PHONES.imei'); ?>">Imei</a> </th>
            <th id="model" class="KT_sorter KT_col_model <?php echo $tso_listPHONES2->getSortIcon('PHONES.model'); ?>"> <a href="<?php echo $tso_listPHONES2->getSortLink('PHONES.model'); ?>">Model</a> </th>
            <th id="notes" class="KT_sorter KT_col_notes <?php echo $tso_listPHONES2->getSortIcon('PHONES.notes'); ?>"> <a href="<?php echo $tso_listPHONES2->getSortLink('PHONES.notes'); ?>">Notes</a> </th>
            <th>&nbsp;</th>
          </tr>
          <?php 
  // Show IF Conditional region3
  if (@$_SESSION['has_filter_tfi_listPHONES2'] == 1) {
?>
            <tr class="KT_row_filter">
              <td>&nbsp;</td>
              <td><input type="text" name="tfi_listPHONES2_id" id="tfi_listPHONES2_id" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listPHONES2_id']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listPHONES2_imei" id="tfi_listPHONES2_imei" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listPHONES2_imei']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listPHONES2_model" id="tfi_listPHONES2_model" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listPHONES2_model']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listPHONES2_notes" id="tfi_listPHONES2_notes" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listPHONES2_notes']); ?>" size="20" maxlength="100" /></td>
              <td><input type="submit" name="tfi_listPHONES2" value="<?php echo NXT_getResource("Filter"); ?>" /></td>
            </tr>
            <?php } 
  // endif Conditional region3
?>
        </thead>
        <tbody>
          <?php if ($totalRows_rsPHONES1 == 0) { // Show if recordset empty ?>
            <tr>
              <td colspan="6"><?php echo NXT_getResource("The table is empty or the filter you've selected is too restrictive."); ?></td>
            </tr>
            <?php } // Show if recordset empty ?>
          <?php if ($totalRows_rsPHONES1 > 0) { // Show if recordset not empty ?>
            <?php do { ?>
              <tr class="<?php echo @$cnt1++%2==0 ? "" : "KT_even"; ?>">
                <td><input type="checkbox" name="kt_pk_PHONES" class="id_checkbox" value="<?php echo $row_rsPHONES1['id']; ?>" />
                    <input type="hidden" name="id" class="id_field" value="<?php echo $row_rsPHONES1['id']; ?>" />
                </td>
                <td><div class="KT_col_id"><?php echo KT_FormatForList($row_rsPHONES1['id'], 20); ?></div></td>
                <td><div class="KT_col_imei"><?php echo KT_FormatForList($row_rsPHONES1['imei'], 20); ?></div></td>
                <td><div class="KT_col_model"><?php echo KT_FormatForList($row_rsPHONES1['model'], 20); ?></div></td>
                <td><div class="KT_col_notes"><?php echo KT_FormatForList($row_rsPHONES1['notes'], 20); ?></div></td>
                <td><a class="KT_edit_link" href="testdetails.php?id=<?php echo $row_rsPHONES1['id']; ?>&amp;KT_back=1"><?php echo NXT_getResource("edit_one"); ?></a> <a class="KT_delete_link" href="#delete"><?php echo NXT_getResource("delete_one"); ?></a> </td>
              </tr>
              <?php } while ($row_rsPHONES1 = mysql_fetch_assoc($rsPHONES1)); ?>
            <?php } // Show if recordset not empty ?>
        </tbody>
      </table>
      <div class="KT_bottomnav">
        <div>
          <?php
            $nav_listPHONES2->Prepare();
            require("../includes/nav/NAV_Text_Navigation.inc.php");
          ?>
        </div>
      </div>
      <div class="KT_bottombuttons">
        <div class="KT_operations"> <a class="KT_edit_op_link" href="#" onclick="nxt_list_edit_link_form(this); return false;"><?php echo NXT_getResource("edit_all"); ?></a> <a class="KT_delete_op_link" href="#" onclick="nxt_list_delete_link_form(this); return false;"><?php echo NXT_getResource("delete_all"); ?></a> </div>
        <span>&nbsp;</span>
        <select name="no_new" id="no_new">
          <option value="1">1</option>
          <option value="3">3</option>
          <option value="6">6</option>
        </select>
        <a class="KT_additem_op_link" href="testdetails.php?KT_back=1" onclick="return nxt_list_additem(this)"><?php echo NXT_getResource("add new"); ?></a> </div>
    </form>
  </div>
  <br class="clearfixplain" />
</div>
<p>&nbsp;</p>
</body>
</html>
<?php
mysql_free_result($rsPHONES1);
?>
