<?php require_once('Connections/Wockets.php'); ?>
<?php
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
</head>

<body>
<p>
<div id="cssMenu1" class="horizontal" >
    <ul class="interakt_blue">
      <li> <a href="#" title="Accounts">Web Site</a>
          <ul>
            <li> <a href="#" title="User Accounts">Accounts</a> </li>
            <li> <a href="#" title="Site Activity">Login Activity</a> </li>
          </ul>
      </li>
      <li> <a href="#" title="Participants">Participants</a>
          <ul>
            <li> <a href="#" title="Personal">Personal</a> </li>
            <li> <a href="#" title="Statistics">Statistics</a> </li>
          </ul>
      </li>
      <li> <a href="#" title="Phones">Phones</a>
          <ul>
            <li> <a href="#" title="Details">Details</a> </li>
            <li> <a href="#" title="Statistics">Statistics</a> </li>
          </ul>
      </li>
      <li> <a href="#" title="Advanced">Advanced</a> </li>
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
</p>

<p>&nbsp;</p>

<table>
<tr>
<td valign="top">
<form>

<strong>Participants: </strong> <select  ONCHANGE="location = this.options[this.selectedIndex].value;">
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
		
		<p>

		</p>
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
?></p>
</td>
<td valign="top">

<iframe src ="Chart.php?date=<?php echo $_GET['date'];?>&participant_id=<?php echo $_GET['participant_id'];?>" style="border-style:none;width: 820px; height: 520px;" frameborder="0" scrolling="no">
  <p>Your browser does not support iframes.</p>
</iframe>

</td>
</tr>
</table>


</body>
</html>
<?php
mysql_free_result($Recordset1);

mysql_free_result($Recordset2);
?>
