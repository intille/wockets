<?php
// Array definitions
  $tNG_login_config = array();
  $tNG_login_config_session = array();
  $tNG_login_config_redirect_success  = array();
  $tNG_login_config_redirect_failed  = array();

// Start Variable definitions
  $tNG_debug_mode = "DEVELOPMENT";
  $tNG_debug_log_type = "";
  $tNG_debug_email_to = "you@yoursite.com";
  $tNG_debug_email_subject = "[BUG] The site went down";
  $tNG_debug_email_from = "webserver@yoursite.com";
  $tNG_email_host = "";
  $tNG_email_user = "";
  $tNG_email_port = "25";
  $tNG_email_password = "";
  $tNG_email_defaultFrom = "noreply@mit.edu";
  $tNG_login_config["connection"] = "Wockets";
  $tNG_login_config["table"] = "ACCOUNTS";
  $tNG_login_config["pk_field"] = "user_id";
  $tNG_login_config["pk_type"] = "NUMERIC_TYPE";
  $tNG_login_config["email_field"] = "email";
  $tNG_login_config["user_field"] = "username";
  $tNG_login_config["password_field"] = "password";
  $tNG_login_config["level_field"] = "";
  $tNG_login_config["level_type"] = "STRING_TYPE";
  $tNG_login_config["randomkey_field"] = "reg_key";
  $tNG_login_config["activation_field"] = "active";
  $tNG_login_config["password_encrypt"] = "false";
  $tNG_login_config["autologin_expires"] = "30";
  $tNG_login_config["redirect_failed"] = "login.php";
  $tNG_login_config["redirect_success"] = "main.php";
  $tNG_login_config["login_page"] = "login.php";
  $tNG_login_config["max_tries"] = "5";
  $tNG_login_config["max_tries_field"] = "attempts";
  $tNG_login_config["max_tries_disableinterval"] = "30";
  $tNG_login_config["max_tries_disabledate_field"] = "disable_date";
  $tNG_login_config["registration_date_field"] = "";
  $tNG_login_config["expiration_interval_field"] = "";
  $tNG_login_config["expiration_interval_default"] = "";
  $tNG_login_config["logger_pk"] = "id";
  $tNG_login_config["logger_table"] = "LOGINHISTORY";
  $tNG_login_config["logger_user_id"] = "user_id";
  $tNG_login_config["logger_ip"] = "ip";
  $tNG_login_config["logger_datein"] = "last_login_date";
  $tNG_login_config["logger_datelastactivity"] = "last_activity_date";
  $tNG_login_config["logger_session"] = "session";
  $tNG_login_config_session["kt_login_id"] = "user_id";
  $tNG_login_config_session["kt_login_user"] = "username";
  $tNG_login_config_session["kt_user_type"] = "user_type";
// End Variable definitions
?>