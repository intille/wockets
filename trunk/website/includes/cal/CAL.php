<?php
	$KT_CAL_uploadErrorMsg = '<strong>File not found:</strong> <br />%s<br /><strong>Please upload the includes/ folder to the testing server.</strong> <br /><a href="http://www.interaktonline.com/error/?error=upload_includes" onclick="return confirm(\'Some data will be submitted to InterAKT. Do you want to continue?\');" target="KTDebugger_0">Online troubleshooter</a>';
	$KT_CAL_uploadFileList = array(
		'../common/KT_common.php',
		'../common/lib/resources/KT_Resources.php',
		'../common/lib/db/KT_Db.php',
		'CAL_functions.inc.php',
		'CAL_CalendarBase.class.php',
		'CAL_Calendar.class.php',
		'CAL_CalendarNugget.class.php',
		'CAL_ViewBase.class.php',
		'CAL_ViewNuggetHtml.class.php',
		'CAL_ViewDay.class.php',
		'CAL_ViewWeek.class.php',
		'CAL_ViewMonth.class.php',
		'CAL_ViewYear.class.php'
	);

	for ($KT_CAL_i=0;$KT_CAL_i<sizeof($KT_CAL_uploadFileList);$KT_CAL_i++) {
		$KT_CAL_uploadFileName = dirname(realpath(__FILE__)). '/' . $KT_CAL_uploadFileList[$KT_CAL_i];
		if (file_exists($KT_CAL_uploadFileName)) {
			require_once($KT_CAL_uploadFileName);
		} else {
			die(sprintf($KT_CAL_uploadErrorMsg,$KT_CAL_uploadFileList[$KT_CAL_i]));
		}
	}

	KT_setServerVariables();
	KT_session_start();
	KT_getInternalTimeFormat();
	$GLOBALS['KT_inFmtRule'] = KT_format2rule($GLOBALS['KT_db_date_format'] . ' ' . $GLOBALS['KT_db_time_format_internal']);
?>