<?php
# FileName="Connection_php_mysql.htm"
# Type="MYSQL"
# HTTP="true"
$hostname_Wockets = "18.85.54.236";
$database_Wockets = "wockets";
$username_Wockets = "wockets";
$password_Wockets = "76giotto";
$Wockets = mysql_pconnect($hostname_Wockets, $username_Wockets, $password_Wockets) or trigger_error(mysql_error(),E_USER_ERROR); 
?>