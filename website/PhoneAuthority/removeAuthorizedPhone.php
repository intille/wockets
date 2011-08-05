<?php 
	if(isset($_POST['phoneID'])){
		include("conn_open.php");
		$sql="delete from phone where phoneID='{$_POST['phoneID']}';"; 
		mysql_query($sql); 
		include("conn_close.php");
		echo "true";
	}else{
		echo "false";
	}
?>