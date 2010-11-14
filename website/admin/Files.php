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
$tfi_listFILE_UPLOAD2 = new TFI_TableFilter($conn_Wockets, "tfi_listFILE_UPLOAD2");
$tfi_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.filename", "NUMERIC_TYPE", "filename", "=");
$tfi_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.relative_path", "STRING_TYPE", "relative_path", "%");
$tfi_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.server_date", "DATE_TYPE", "server_date", "=");
$tfi_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.sender_date", "DATE_TYPE", "sender_date", "=");
$tfi_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.imei", "STRING_TYPE", "imei", "%");
$tfi_listFILE_UPLOAD2->Execute();

// Sorter
$tso_listFILE_UPLOAD2 = new TSO_TableSorter("rsFILE_UPLOAD1", "tso_listFILE_UPLOAD2");
$tso_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.filename");
$tso_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.relative_path");
$tso_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.server_date");
$tso_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.sender_date");
$tso_listFILE_UPLOAD2->addColumn("FILE_UPLOAD.imei");
$tso_listFILE_UPLOAD2->setDefault("FILE_UPLOAD.filename");
$tso_listFILE_UPLOAD2->Execute();

// Navigation
$nav_listFILE_UPLOAD2 = new NAV_Regular("nav_listFILE_UPLOAD2", "rsFILE_UPLOAD1", "../", $_SERVER['PHP_SELF'], 10);

//NeXTenesio3 Special List Recordset
$maxRows_rsFILE_UPLOAD1 = $_SESSION['max_rows_nav_listFILE_UPLOAD2'];
$pageNum_rsFILE_UPLOAD1 = 0;
if (isset($_GET['pageNum_rsFILE_UPLOAD1'])) {
  $pageNum_rsFILE_UPLOAD1 = $_GET['pageNum_rsFILE_UPLOAD1'];
}
$startRow_rsFILE_UPLOAD1 = $pageNum_rsFILE_UPLOAD1 * $maxRows_rsFILE_UPLOAD1;

// Defining List Recordset variable
$NXTFilter_rsFILE_UPLOAD1 = "1=1";
if (isset($_SESSION['filter_tfi_listFILE_UPLOAD2'])) {
  $NXTFilter_rsFILE_UPLOAD1 = $_SESSION['filter_tfi_listFILE_UPLOAD2'];
}
// Defining List Recordset variable
$NXTSort_rsFILE_UPLOAD1 = "FILE_UPLOAD.filename";
if (isset($_SESSION['sorter_tso_listFILE_UPLOAD2'])) {
  $NXTSort_rsFILE_UPLOAD1 = $_SESSION['sorter_tso_listFILE_UPLOAD2'];
}
mysql_select_db($database_Wockets, $Wockets);

$query_rsFILE_UPLOAD1 = "SELECT FILE_UPLOAD.filename, FILE_UPLOAD.relative_path, FILE_UPLOAD.server_date, FILE_UPLOAD.sender_date, FILE_UPLOAD.imei, FILE_UPLOAD.id FROM FILE_UPLOAD WHERE {$NXTFilter_rsFILE_UPLOAD1} ORDER BY {$NXTSort_rsFILE_UPLOAD1}";
$query_limit_rsFILE_UPLOAD1 = sprintf("%s LIMIT %d, %d", $query_rsFILE_UPLOAD1, $startRow_rsFILE_UPLOAD1, $maxRows_rsFILE_UPLOAD1);
$rsFILE_UPLOAD1 = mysql_query($query_limit_rsFILE_UPLOAD1, $Wockets) or die(mysql_error());
$row_rsFILE_UPLOAD1 = mysql_fetch_assoc($rsFILE_UPLOAD1);

if (isset($_GET['totalRows_rsFILE_UPLOAD1'])) {
  $totalRows_rsFILE_UPLOAD1 = $_GET['totalRows_rsFILE_UPLOAD1'];
} else {
  $all_rsFILE_UPLOAD1 = mysql_query($query_rsFILE_UPLOAD1);
  $totalRows_rsFILE_UPLOAD1 = mysql_num_rows($all_rsFILE_UPLOAD1);
}
$totalPages_rsFILE_UPLOAD1 = ceil($totalRows_rsFILE_UPLOAD1/$maxRows_rsFILE_UPLOAD1)-1;
//End NeXTenesio3 Special List Recordset

$nav_listFILE_UPLOAD2->checkBoundries();
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
  .KT_col_filename {width:140px; overflow:hidden;}
  .KT_col_relative_path {width:140px; overflow:hidden;}
  .KT_col_server_date {width:140px; overflow:hidden;}
  .KT_col_sender_date {width:140px; overflow:hidden;}
  .KT_col_imei {width:140px; overflow:hidden;}
</style>
</head>

<body>
<a href="index.php">Admin Home</a>
<div class="KT_tng" id="listFILE_UPLOAD2">
  <h1> FILE_UPLOAD
    <?php
  $nav_listFILE_UPLOAD2->Prepare();
  require("../includes/nav/NAV_Text_Statistics.inc.php");
?>
  </h1>
  <div class="KT_tnglist">
    <form action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>" method="post" id="form1">
      <div class="KT_options"> <a href="<?php echo $nav_listFILE_UPLOAD2->getShowAllLink(); ?>"><?php echo NXT_getResource("Show"); ?>
            <?php 
  // Show IF Conditional region1
  if (@$_GET['show_all_nav_listFILE_UPLOAD2'] == 1) {
?>
              <?php echo $_SESSION['default_max_rows_nav_listFILE_UPLOAD2']; ?>
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
  if (@$_SESSION['has_filter_tfi_listFILE_UPLOAD2'] == 1) {
?>
                              <a href="<?php echo $tfi_listFILE_UPLOAD2->getResetFilterLink(); ?>"><?php echo NXT_getResource("Reset filter"); ?></a>
                              <?php 
  // else Conditional region2
  } else { ?>
                              <a href="<?php echo $tfi_listFILE_UPLOAD2->getShowFilterLink(); ?>"><?php echo NXT_getResource("Show filter"); ?></a>
                              <?php } 
  // endif Conditional region2
?>
      </div>
      <table cellpadding="2" cellspacing="0" class="KT_tngtable">
        <thead>
          <tr class="KT_row_order">
            <th> <input type="checkbox" name="KT_selAll" id="KT_selAll"/>
            </th>
            <th id="filename" class="KT_sorter KT_col_filename <?php echo $tso_listFILE_UPLOAD2->getSortIcon('FILE_UPLOAD.filename'); ?>"> <a href="<?php echo $tso_listFILE_UPLOAD2->getSortLink('FILE_UPLOAD.filename'); ?>">Filename</a> </th>
            <th id="relative_path" class="KT_sorter KT_col_relative_path <?php echo $tso_listFILE_UPLOAD2->getSortIcon('FILE_UPLOAD.relative_path'); ?>"> <a href="<?php echo $tso_listFILE_UPLOAD2->getSortLink('FILE_UPLOAD.relative_path'); ?>">Relative_path</a> </th>
            <th id="server_date" class="KT_sorter KT_col_server_date <?php echo $tso_listFILE_UPLOAD2->getSortIcon('FILE_UPLOAD.server_date'); ?>"> <a href="<?php echo $tso_listFILE_UPLOAD2->getSortLink('FILE_UPLOAD.server_date'); ?>">Server_date</a> </th>
            <th id="sender_date" class="KT_sorter KT_col_sender_date <?php echo $tso_listFILE_UPLOAD2->getSortIcon('FILE_UPLOAD.sender_date'); ?>"> <a href="<?php echo $tso_listFILE_UPLOAD2->getSortLink('FILE_UPLOAD.sender_date'); ?>">Sender Date</a> </th>
            <th id="imei" class="KT_sorter KT_col_imei <?php echo $tso_listFILE_UPLOAD2->getSortIcon('FILE_UPLOAD.imei'); ?>"> <a href="<?php echo $tso_listFILE_UPLOAD2->getSortLink('FILE_UPLOAD.imei'); ?>">Imei</a> </th>
            <th>&nbsp;</th>
          </tr>
          <?php 
  // Show IF Conditional region3
  if (@$_SESSION['has_filter_tfi_listFILE_UPLOAD2'] == 1) {
?>
            <tr class="KT_row_filter">
              <td>&nbsp;</td>
              <td><input type="text" name="tfi_listFILE_UPLOAD2_filename" id="tfi_listFILE_UPLOAD2_filename" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listFILE_UPLOAD2_filename']); ?>" size="20" maxlength="45" /></td>
              <td><input type="text" name="tfi_listFILE_UPLOAD2_relative_path" id="tfi_listFILE_UPLOAD2_relative_path" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listFILE_UPLOAD2_relative_path']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listFILE_UPLOAD2_server_date" id="tfi_listFILE_UPLOAD2_server_date" value="<?php echo @$_SESSION['tfi_listFILE_UPLOAD2_server_date']; ?>" size="10" maxlength="22" /></td>
              <td><input type="text" name="tfi_listFILE_UPLOAD2_sender_date" id="tfi_listFILE_UPLOAD2_sender_date" value="<?php echo @$_SESSION['tfi_listFILE_UPLOAD2_sender_date']; ?>" size="10" maxlength="22" /></td>
              <td><input type="text" name="tfi_listFILE_UPLOAD2_imei" id="tfi_listFILE_UPLOAD2_imei" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listFILE_UPLOAD2_imei']); ?>" size="20" maxlength="100" /></td>
              <td><input type="submit" name="tfi_listFILE_UPLOAD2" value="<?php echo NXT_getResource("Filter"); ?>" /></td>
            </tr>
            <?php } 
  // endif Conditional region3
?>
        </thead>
        <tbody>
          <?php if ($totalRows_rsFILE_UPLOAD1 == 0) { // Show if recordset empty ?>
            <tr>
              <td colspan="7"><?php echo NXT_getResource("The table is empty or the filter you've selected is too restrictive."); ?></td>
            </tr>
            <?php } // Show if recordset empty ?>
          <?php if ($totalRows_rsFILE_UPLOAD1 > 0) { // Show if recordset not empty ?>
            <?php do { ?>
              <tr class="<?php echo @$cnt1++%2==0 ? "" : "KT_even"; ?>">
                <td><input type="checkbox" name="kt_pk_FILE_UPLOAD" class="id_checkbox" value="<?php echo $row_rsFILE_UPLOAD1['id']; ?>" />
                    <input type="hidden" name="id" class="id_field" value="<?php echo $row_rsFILE_UPLOAD1['id']; ?>" />
                </td>
                <td><div class="KT_col_filename"><?php echo KT_FormatForList($row_rsFILE_UPLOAD1['filename'], 20); ?></div></td>
                <td><div class="KT_col_relative_path"><?php echo KT_FormatForList($row_rsFILE_UPLOAD1['relative_path'], 20); ?></div></td>
                <td><div class="KT_col_server_date"><?php echo KT_formatDate($row_rsFILE_UPLOAD1['server_date']); ?></div></td>
                <td><div class="KT_col_sender_date"><?php echo KT_formatDate($row_rsFILE_UPLOAD1['sender_date']); ?></div></td>
                <td><div class="KT_col_imei"><?php echo KT_FormatForList($row_rsFILE_UPLOAD1['imei'], 20); ?></div></td>
                <td><a class="KT_edit_link" href="FileDetails.php?id=<?php echo $row_rsFILE_UPLOAD1['id']; ?>&amp;KT_back=1"><?php echo NXT_getResource("edit_one"); ?></a> <a class="KT_delete_link" href="#delete"><?php echo NXT_getResource("delete_one"); ?></a> </td>
              </tr>
              <?php } while ($row_rsFILE_UPLOAD1 = mysql_fetch_assoc($rsFILE_UPLOAD1)); ?>
            <?php } // Show if recordset not empty ?>
        </tbody>
      </table>
      <div class="KT_bottomnav">
        <div>
          <?php
            $nav_listFILE_UPLOAD2->Prepare();
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
        <a class="KT_additem_op_link" href="FileDetails.php?KT_back=1" onclick="return nxt_list_additem(this)"><?php echo NXT_getResource("add new"); ?></a> </div>
    </form>
  </div>
  <br class="clearfixplain" />
</div>
<p>&nbsp;</p>
</body>
</html>
<?php
mysql_free_result($rsFILE_UPLOAD1);
?>
