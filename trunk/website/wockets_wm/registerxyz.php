<?php require_once('Connections/Wockets.php'); ?>
<?php
// Load the common classes
require_once('includes/common/KT_common.php');

// Load the required classes
require_once('includes/tfi/TFI.php');
require_once('includes/tso/TSO.php');
require_once('includes/nav/NAV.php');

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
$tfi_listACCOUNTS2 = new TFI_TableFilter($conn_Wockets, "tfi_listACCOUNTS2");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.username", "STRING_TYPE", "username", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.user_type", "STRING_TYPE", "user_type", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.first_name", "STRING_TYPE", "first_name", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.last_name", "STRING_TYPE", "last_name", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.email", "STRING_TYPE", "email", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.password", "STRING_TYPE", "password", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.registration_datetime", "DATE_TYPE", "registration_datetime", "=");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.active", "STRING_TYPE", "active", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.reg_key", "STRING_TYPE", "reg_key", "%");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.disable_date", "DATE_TYPE", "disable_date", "=");
$tfi_listACCOUNTS2->addColumn("ACCOUNTS.attempts", "STRING_TYPE", "attempts", "%");
$tfi_listACCOUNTS2->Execute();

// Sorter
$tso_listACCOUNTS2 = new TSO_TableSorter("rsACCOUNTS1", "tso_listACCOUNTS2");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.username");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.user_type");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.first_name");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.last_name");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.email");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.password");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.registration_datetime");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.active");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.reg_key");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.disable_date");
$tso_listACCOUNTS2->addColumn("ACCOUNTS.attempts");
$tso_listACCOUNTS2->setDefault("ACCOUNTS.username");
$tso_listACCOUNTS2->Execute();

// Navigation
$nav_listACCOUNTS2 = new NAV_Regular("nav_listACCOUNTS2", "rsACCOUNTS1", "", $_SERVER['PHP_SELF'], 10);

//NeXTenesio3 Special List Recordset
$maxRows_rsACCOUNTS1 = $_SESSION['max_rows_nav_listACCOUNTS2'];
$pageNum_rsACCOUNTS1 = 0;
if (isset($_GET['pageNum_rsACCOUNTS1'])) {
  $pageNum_rsACCOUNTS1 = $_GET['pageNum_rsACCOUNTS1'];
}
$startRow_rsACCOUNTS1 = $pageNum_rsACCOUNTS1 * $maxRows_rsACCOUNTS1;

// Defining List Recordset variable
$NXTFilter_rsACCOUNTS1 = "1=1";
if (isset($_SESSION['filter_tfi_listACCOUNTS2'])) {
  $NXTFilter_rsACCOUNTS1 = $_SESSION['filter_tfi_listACCOUNTS2'];
}
// Defining List Recordset variable
$NXTSort_rsACCOUNTS1 = "ACCOUNTS.username";
if (isset($_SESSION['sorter_tso_listACCOUNTS2'])) {
  $NXTSort_rsACCOUNTS1 = $_SESSION['sorter_tso_listACCOUNTS2'];
}
mysql_select_db($database_Wockets, $Wockets);

$query_rsACCOUNTS1 = "SELECT ACCOUNTS.username, ACCOUNTS.user_type, ACCOUNTS.first_name, ACCOUNTS.last_name, ACCOUNTS.email, ACCOUNTS.password, ACCOUNTS.registration_datetime, ACCOUNTS.active, ACCOUNTS.reg_key, ACCOUNTS.disable_date, ACCOUNTS.attempts, ACCOUNTS.user_id FROM ACCOUNTS WHERE {$NXTFilter_rsACCOUNTS1} ORDER BY {$NXTSort_rsACCOUNTS1}";
$query_limit_rsACCOUNTS1 = sprintf("%s LIMIT %d, %d", $query_rsACCOUNTS1, $startRow_rsACCOUNTS1, $maxRows_rsACCOUNTS1);
$rsACCOUNTS1 = mysql_query($query_limit_rsACCOUNTS1, $Wockets) or die(mysql_error());
$row_rsACCOUNTS1 = mysql_fetch_assoc($rsACCOUNTS1);

if (isset($_GET['totalRows_rsACCOUNTS1'])) {
  $totalRows_rsACCOUNTS1 = $_GET['totalRows_rsACCOUNTS1'];
} else {
  $all_rsACCOUNTS1 = mysql_query($query_rsACCOUNTS1);
  $totalRows_rsACCOUNTS1 = mysql_num_rows($all_rsACCOUNTS1);
}
$totalPages_rsACCOUNTS1 = ceil($totalRows_rsACCOUNTS1/$maxRows_rsACCOUNTS1)-1;
//End NeXTenesio3 Special List Recordset

$nav_listACCOUNTS2->checkBoundries();
?><!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<link href="includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="includes/common/js/base.js" type="text/javascript"></script>
<script src="includes/common/js/utility.js" type="text/javascript"></script>
<script src="includes/skins/style.js" type="text/javascript"></script>
<script src="includes/nxt/scripts/list.js" type="text/javascript"></script>
<script src="includes/nxt/scripts/list.js.php" type="text/javascript"></script>
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
  .KT_col_username {width:140px; overflow:hidden;}
  .KT_col_user_type {width:140px; overflow:hidden;}
  .KT_col_first_name {width:140px; overflow:hidden;}
  .KT_col_last_name {width:140px; overflow:hidden;}
  .KT_col_email {width:140px; overflow:hidden;}
  .KT_col_password {width:140px; overflow:hidden;}
  .KT_col_registration_datetime {width:140px; overflow:hidden;}
  .KT_col_active {width:140px; overflow:hidden;}
  .KT_col_reg_key {width:140px; overflow:hidden;}
  .KT_col_disable_date {width:140px; overflow:hidden;}
  .KT_col_attempts {width:140px; overflow:hidden;}
</style>
</head>

<body>

<div class="KT_tng" id="listACCOUNTS2">
  <h1> ACCOUNTS
    <?php
  $nav_listACCOUNTS2->Prepare();
  require("includes/nav/NAV_Text_Statistics.inc.php");
?>
  </h1>
  <div class="KT_tnglist">
    <form action="<?php echo KT_escapeAttribute(KT_getFullUri()); ?>" method="post" id="form1">
      <div class="KT_options"> <a href="<?php echo $nav_listACCOUNTS2->getShowAllLink(); ?>"><?php echo NXT_getResource("Show"); ?>
            <?php 
  // Show IF Conditional region1
  if (@$_GET['show_all_nav_listACCOUNTS2'] == 1) {
?>
              <?php echo $_SESSION['default_max_rows_nav_listACCOUNTS2']; ?>
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
  if (@$_SESSION['has_filter_tfi_listACCOUNTS2'] == 1) {
?>
                              <a href="<?php echo $tfi_listACCOUNTS2->getResetFilterLink(); ?>"><?php echo NXT_getResource("Reset filter"); ?></a>
                              <?php 
  // else Conditional region2
  } else { ?>
                              <a href="<?php echo $tfi_listACCOUNTS2->getShowFilterLink(); ?>"><?php echo NXT_getResource("Show filter"); ?></a>
                              <?php } 
  // endif Conditional region2
?>
      </div>
      <table cellpadding="2" cellspacing="0" class="KT_tngtable">
        <thead>
          <tr class="KT_row_order">
            <th> <input type="checkbox" name="KT_selAll" id="KT_selAll"/>
            </th>
            <th id="username" class="KT_sorter KT_col_username <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.username'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.username'); ?>">Username</a> </th>
            <th id="user_type" class="KT_sorter KT_col_user_type <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.user_type'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.user_type'); ?>">User_type</a> </th>
            <th id="first_name" class="KT_sorter KT_col_first_name <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.first_name'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.first_name'); ?>">First_name</a> </th>
            <th id="last_name" class="KT_sorter KT_col_last_name <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.last_name'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.last_name'); ?>">Last_name</a> </th>
            <th id="email" class="KT_sorter KT_col_email <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.email'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.email'); ?>">Email</a> </th>
            <th id="password" class="KT_sorter KT_col_password <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.password'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.password'); ?>">Password</a> </th>
            <th id="registration_datetime" class="KT_sorter KT_col_registration_datetime <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.registration_datetime'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.registration_datetime'); ?>">Registration_datetime</a> </th>
            <th id="active" class="KT_sorter KT_col_active <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.active'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.active'); ?>">Active</a> </th>
            <th id="reg_key" class="KT_sorter KT_col_reg_key <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.reg_key'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.reg_key'); ?>">Reg</a> </th>
            <th id="disable_date" class="KT_sorter KT_col_disable_date <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.disable_date'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.disable_date'); ?>">Disable_date</a> </th>
            <th id="attempts" class="KT_sorter KT_col_attempts <?php echo $tso_listACCOUNTS2->getSortIcon('ACCOUNTS.attempts'); ?>"> <a href="<?php echo $tso_listACCOUNTS2->getSortLink('ACCOUNTS.attempts'); ?>">Attempts</a> </th>
            <th>&nbsp;</th>
          </tr>
          <?php 
  // Show IF Conditional region3
  if (@$_SESSION['has_filter_tfi_listACCOUNTS2'] == 1) {
?>
            <tr class="KT_row_filter">
              <td>&nbsp;</td>
              <td><input type="text" name="tfi_listACCOUNTS2_username" id="tfi_listACCOUNTS2_username" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_username']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_user_type" id="tfi_listACCOUNTS2_user_type" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_user_type']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_first_name" id="tfi_listACCOUNTS2_first_name" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_first_name']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_last_name" id="tfi_listACCOUNTS2_last_name" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_last_name']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_email" id="tfi_listACCOUNTS2_email" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_email']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_password" id="tfi_listACCOUNTS2_password" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_password']); ?>" size="20" maxlength="100" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_registration_datetime" id="tfi_listACCOUNTS2_registration_datetime" value="<?php echo @$_SESSION['tfi_listACCOUNTS2_registration_datetime']; ?>" size="10" maxlength="22" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_active" id="tfi_listACCOUNTS2_active" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_active']); ?>" size="20" maxlength="45" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_reg_key" id="tfi_listACCOUNTS2_reg_key" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_reg_key']); ?>" size="20" maxlength="64" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_disable_date" id="tfi_listACCOUNTS2_disable_date" value="<?php echo @$_SESSION['tfi_listACCOUNTS2_disable_date']; ?>" size="10" maxlength="22" /></td>
              <td><input type="text" name="tfi_listACCOUNTS2_attempts" id="tfi_listACCOUNTS2_attempts" value="<?php echo KT_escapeAttribute(@$_SESSION['tfi_listACCOUNTS2_attempts']); ?>" size="20" maxlength="16" /></td>
              <td><input type="submit" name="tfi_listACCOUNTS2" value="<?php echo NXT_getResource("Filter"); ?>" /></td>
            </tr>
            <?php } 
  // endif Conditional region3
?>
        </thead>
        <tbody>
          <?php if ($totalRows_rsACCOUNTS1 == 0) { // Show if recordset empty ?>
            <tr>
              <td colspan="13"><?php echo NXT_getResource("The table is empty or the filter you've selected is too restrictive."); ?></td>
            </tr>
            <?php } // Show if recordset empty ?>
          <?php if ($totalRows_rsACCOUNTS1 > 0) { // Show if recordset not empty ?>
            <?php do { ?>
              <tr class="<?php echo @$cnt1++%2==0 ? "" : "KT_even"; ?>">
                <td><input type="checkbox" name="kt_pk_ACCOUNTS" class="id_checkbox" value="<?php echo $row_rsACCOUNTS1['user_id']; ?>" />
                    <input type="hidden" name="user_id" class="id_field" value="<?php echo $row_rsACCOUNTS1['user_id']; ?>" />
                </td>
                <td><div class="KT_col_username"><?php echo KT_FormatForList($row_rsACCOUNTS1['username'], 20); ?></div></td>
                <td><div class="KT_col_user_type"><?php echo KT_FormatForList($row_rsACCOUNTS1['user_type'], 20); ?></div></td>
                <td><div class="KT_col_first_name"><?php echo KT_FormatForList($row_rsACCOUNTS1['first_name'], 20); ?></div></td>
                <td><div class="KT_col_last_name"><?php echo KT_FormatForList($row_rsACCOUNTS1['last_name'], 20); ?></div></td>
                <td><div class="KT_col_email"><?php echo KT_FormatForList($row_rsACCOUNTS1['email'], 20); ?></div></td>
                <td><div class="KT_col_password"><?php echo KT_FormatForList($row_rsACCOUNTS1['password'], 20); ?></div></td>
                <td><div class="KT_col_registration_datetime"><?php echo KT_formatDate($row_rsACCOUNTS1['registration_datetime']); ?></div></td>
                <td><div class="KT_col_active"><?php echo KT_FormatForList($row_rsACCOUNTS1['active'], 20); ?></div></td>
                <td><div class="KT_col_reg_key"><?php echo KT_FormatForList($row_rsACCOUNTS1['reg_key'], 20); ?></div></td>
                <td><div class="KT_col_disable_date"><?php echo KT_formatDate($row_rsACCOUNTS1['disable_date']); ?></div></td>
                <td><div class="KT_col_attempts"><?php echo KT_FormatForList($row_rsACCOUNTS1['attempts'], 20); ?></div></td>
                <td><a class="KT_edit_link" href="acc.php?user_id=<?php echo $row_rsACCOUNTS1['user_id']; ?>&amp;KT_back=1"><?php echo NXT_getResource("edit_one"); ?></a> <a class="KT_delete_link" href="#delete"><?php echo NXT_getResource("delete_one"); ?></a> </td>
              </tr>
              <?php } while ($row_rsACCOUNTS1 = mysql_fetch_assoc($rsACCOUNTS1)); ?>
            <?php } // Show if recordset not empty ?>
        </tbody>
      </table>
      <div class="KT_bottomnav">
        <div>
          <?php
            $nav_listACCOUNTS2->Prepare();
            require("includes/nav/NAV_Text_Navigation.inc.php");
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
        <a class="KT_additem_op_link" href="acc.php?KT_back=1" onclick="return nxt_list_additem(this)"><?php echo NXT_getResource("add new"); ?></a> </div>
    </form>
  </div>
  <br class="clearfixplain" />
</div>
<p>&nbsp;</p>
</body>
</html>
<?php
mysql_free_result($rsACCOUNTS1);
?>
