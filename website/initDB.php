<?php


function initializeDB($myDB){
	
	// connect to the database when this file begins.
	$myServer = "sql.mit.edu";
	$myUser = "wockets";
	$myPass = "muy66jib";
	//$myDB = "cityproject+cityproject";
	
	//connection to the database
	$dbhandle = mysql_connect($myServer, $myUser, $myPass)
	  or die("Couldn't connect to SQL Server on $myServer");
	
	//select a database to work with
	$selected = mysql_select_db($myDB, $dbhandle)
	  or die("Couldn't open database $myDB");
  
  	return $dbhandle;
}

function closeDB($dbhandle){
	mysql_close($dbhandle);
}
?>