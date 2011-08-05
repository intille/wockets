<?php 
		include("conn_open.php");
		$sql="select * from phone;";
		$result=mysql_query($sql);
		$list="";
		while ($row = mysql_fetch_array($result)){
			$list.=$row['phoneID'].',';
		}
		echo substr($list,0,-1);
		mysql_free_result($result);
		include("conn_close.php");
?>