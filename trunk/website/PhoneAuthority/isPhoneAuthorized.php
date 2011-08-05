<?php 
	if(isset($_POST['phoneID'])&&isset($_POST['phoneOwner'])){
		include("conn_open.php");
		$sql="select * from phone where phoneID='{$_POST['phoneID']}' and phoneOwner='{$_POST['phoneOwner']}';";
		$result=mysql_query($sql);
		$row = mysql_fetch_array($result);
		if(!$row) 
			echo "false";
		else
			echo "true";
		mysql_free_result($result);
		include("conn_close.php");
	}else{
		echo "false";
	}
?>