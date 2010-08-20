<?php

include("initDB.php");

//connect to DB, those who opened it has to be responsible closing it using the returned dbhandle.
$dbhandle = initializeDB("wockets+wockets");

$result = mysql_query("SELECT * from subjects_test");

$activeSubjectInfo = array();
$arrayIndex = 0;

while($row = mysql_fetch_array($result))
{
	$activeSubjectInfo[$arrayIndex] = array("id"=>$row["id"], "nickname"=>$row["nickname"]);
	$arrayIndex++;
}

echo json_encode($activeSubjectInfo);

mysql_close($dbhandle);

?>