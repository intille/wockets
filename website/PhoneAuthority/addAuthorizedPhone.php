<?php 
	if(isset($_POST['phoneID'])&&isset($_POST['phoneOwner'])&&$_POST['phoneOwner']=='NUMAD'){
		include("conn_open.php");
		$sql="select * from phone where phoneID='{$_POST['phoneID']}';";
		$result = mysql_query($sql);
		$row = mysql_fetch_array($result);
		if(!$row)
			$sql="insert into phone(phoneID,phoneOwner) values('{$_POST['phoneID']}','{$_POST['phoneOwner']}');";
		else
			$sql="update phone set phoneOwner= '{$_POST['phoneOwner']}' where phoneID='{$_POST['phoneID']}';";
		mysql_query($sql); 
		include("conn_close.php");
		echo "true";
	}else{
		echo "false";
	}
?>