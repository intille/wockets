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

//Start Restrict Access To Page
$restrict = new tNG_RestrictAccess($conn_Wockets, "");
//Grand Levels: Any
$restrict->Execute();
//End Restrict Access To Page

// Load the Calendar classes
require_once('includes/cal/CAL.php');

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
$query_Recordset1 = "SELECT id,first_name, last_name FROM PARTICIPANTS ORDER BY last_name ASC";
$Recordset1 = mysql_query($query_Recordset1, $Wockets) or die(mysql_error());
$row_Recordset1 = mysql_fetch_assoc($Recordset1);
$totalRows_Recordset1 = mysql_num_rows($Recordset1);

if (!isset($_GET['participant_id']))
	$_GET['participant_id']=$row_Recordset1['id'];

if (!isset($_GET['date']))
	$_GET['date']=date("Y-m-d");	

mysql_select_db($database_Wockets, $Wockets);
$query_Recordset2 = "SELECT * FROM CAL_DAYS";
$Recordset2 = mysql_query($query_Recordset2, $Wockets) or die(mysql_error());
$row_Recordset2 = mysql_fetch_assoc($Recordset2);
$totalRows_Recordset2 = mysql_num_rows($Recordset2);

// Make a logout transaction instance
$logoutTransaction = new tNG_logoutTransaction($conn_Wockets);
$tNGs->addTransaction($logoutTransaction);
// Register triggers
$logoutTransaction->registerTrigger("STARTER", "Trigger_Default_Starter", 1, "GET", "KT_logout_now");
$logoutTransaction->registerTrigger("END", "Trigger_Default_Redirect", 99, "index.php");
// Add columns
// End of logout transaction instance

// Execute all the registered transactions
$tNGs->executeTransactions();

// Get the transaction recordset
$rscustom = $tNGs->getRecordset("custom");
$row_rscustom = mysql_fetch_assoc($rscustom);
$totalRows_rscustom = mysql_num_rows($rscustom);
?>
<?php require_once('calendar.php');?>

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<title>Untitled Document</title>
<script src="includes/cssmenus2/js/cssmenus.js" type="text/javascript"></script>
<link href="includes/cssmenus2/skins/interakt_blue/horizontal.css" rel="stylesheet" type="text/css" />
<script src="includes/common/js/base.js" type="text/javascript"></script>
<script src="includes/common/js/utility.js" type="text/javascript"></script>


<link href="includes/skins/mxkollection3.css" rel="stylesheet" type="text/css" media="all" />
<script src="includes/skins/style.js" type="text/javascript"></script>
</head>

<body>
<p> </p>
<div id="cssMenu1" class="horizontal" >
  <ul class="interakt_blue">
    
    <li> <a href="main.php" title="Home">Home</a>
    </li>
    <li> <a href="#" title="Study">Study</a>
        <ul>
          <li> <a href="admin/phones.php" title="Phones">Phones</a> </li>
          <li> <a href="admin/wockets.php" title="Wockets">Wockets</a> </li>
          <li> <a href="admin/participants.php" title="Participants">Participants</a> </li>
        </ul>
    </li>
    <li> <a href="#" title="Export">Actions</a>
        <ul>
          <li> <a href="admin/participant_phone.php" title="Assign phone to participant">Assign Phone</a> </li>
          <li> <a href="admin/participant_wocket.php" title="Assign Wocket">Assign Wocket</a> </li>
          <li> <a href="ExportData.php" title="Export Data">Export Data</a> </li>
        </ul>
    </li>
    <li> <a href="#" title="Advanced">Advanced</a>
        <ul>
          <li> <a href="admin/accounts.php" title="User Accounts">User Accounts</a> </li>
          <li> <a href="admin/Files.php" title="Files">Files</a> </li>
          <li> <a href="admin/phone_stats.php" title="Phone Statistics">Phone Statistics</a> </li>
          <li> <a href="admin/wocket_stats.php" title="Wockets Statistics">Wockets Statistics</a> </li>
        </ul>
    </li>
    <li>
 <a href="<?php echo $logoutTransaction->getLogoutLink(); ?>" title="Logout">Logout</a>
    </li>	
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
<p></p>
<p>&nbsp;</p>
<table>
  <tr>
    <td valign="top"><form>
      <strong>Participants: </strong>
      <select  ONCHANGE="location = this.options[this.selectedIndex].value;">
        <?php
$rows_Recordset1 = 2;
$cols_Recordset1 = ceil($totalRows_Recordset1/ 2);
for ($i=0; $i<$rows_Recordset1; $i++) {
	for ($j=0; $j<$cols_Recordset1; $j++) {
		$currentIndex_Recordset1 = $i + $rows_Recordset1 * $j;
		if (@mysql_data_seek($Recordset1, $currentIndex_Recordset1)) {
			$row_Recordset1 = mysql_fetch_assoc($Recordset1);
?>
        <option value="main.php?participant_id=<?php echo $row_Recordset1['id']?>" <?php if ((isset($_GET['participant_id'])) &&($_GET['participant_id']==$row_Recordset1['id'])) echo "selected=\"selected\""; ?>><?php echo $row_Recordset1['last_name'].", ". $row_Recordset1['first_name'];?></option>
        <?php
		} else {
			echo '';
		} // end if;
	} //end for 2
	if ($i != $rows_Recordset1-1) {
		echo "";
	}
} // end for 1
?>
      </select>
      <p> </p>
    </form>
        <?php

  $url="main.php?participant_id=".$_GET['participant_id']."&";
	
  $calNugget_Recordset2 = new CAL_CalendarNugget("");
  $calNugget_Recordset2->setDetailPage($url, "");
  $calNugget_Recordset2->setDateParam("date");
  $calNugget_Recordset2->setViewModParam("view");

  $calNugget_Recordset2->setRecordset("Recordset2");
  $calNugget_Recordset2->setField("ID", "id");
  $calNugget_Recordset2->setField("TITLE", "title");
  $calNugget_Recordset2->setField("START_DATE", "start");
  $calNugget_Recordset2->setField("END_DATE", "start");

  $calNugget_Recordset2->setNewEventEnabled("true");
  $calNugget_Recordset2->setMondayFirst(false);
  $calNugget_Recordset2->setViewWeekNo(true);
  $calNugget_Recordset2->render();
?>
      <p></p></td>
    <td valign="top"><iframe src ="Chart.php?date=<?php echo $_GET['date'];?>&participant_id=<?php echo $_GET['participant_id'];?>" style="border-style:none;width: 820px; height: 520px;" frameborder="0" scrolling="no">
      <p>Your browser does not support iframes.</p>
    </iframe></td>
  </tr>
</table>
</body>
</html>
<?php
mysql_free_result($Recordset1);

mysql_free_result($Recordset2);
?>
