<?php
# FileName="Connection_php_mysql.htm"
# Type="MYSQL"
# HTTP="true"
$hostname_Wockets = "sql.mit.edu";
$database_Wockets = "wockets+wockets";
$username_Wockets = "wockets";
$password_Wockets = "muy66jib";
$Wockets = mysql_pconnect($hostname_Wockets, $username_Wockets, $password_Wockets) or trigger_error(mysql_error(),E_USER_ERROR); 
?>