<?php 
	$mysql_server_name='wockets.media.mit.edu';
	$mysql_username='wockets';
	$mysql_password='76giotto';
	$mysql_database='phoneauthority';
	$conn=mysql_connect($mysql_server_name,$mysql_username,$mysql_password,$mysql_database); 
	mysql_select_db($mysql_database,$conn); 
?>
