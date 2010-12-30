<?php
function CAL_XHTML_Url($badurl) {
	return str_replace('&', '&amp;', str_replace('&amp;', '&', $badurl));
}

function CAL_getResource($resourceName) {
	return KT_getResource($resourceName, 'CAL', array());
}

function CAL_getWeekDay($date_ymd, $monday_first) {
	$ret = CAL_extract('w',$date_ymd);
	if ($monday_first) {
		$ret--;
		if ($ret < 0) {
			$ret = 6;
		}
	}
	return $ret;
}

function CAL_normalize($Y, $m, $d, $H, $i, $s) {
	if ($s>59) {
		$i += (int)($s/60);
		$s = $s%60;
	}
	if ($s<0) {
		$i += (int)(($s-59)/60);
		$s = 59-(abs($s)-1)%60;
	}

	if ($i>59) {
		$H += (int)($i/60);
		$i = $i%60;
	}
	if ($i<0) {
		$H += (int)(($i-59)/60);
		$i = 59-(abs($i)-1)%60;
	}

	if ($H>23) {
		$d += (int)($H/24);
		$H = $H%24;
	}
	if ($H<0) {
		$d += (int)(($H-23)/24);
		$H = 23-(abs($H)-1)%24;
	}

	$needExtraNorm = false;
	if ($m > 0 && $m < 13) {
		$d--;
		$ts = @mktime(0, 0, 0, $m, 1, $Y);
		if ($ts < 0) {
			die("MX Calendar Error: dates must be somewhere withing year range: 1901 and 2038.");
		}
		$currMonthNoDays = date('t', $ts);
		if ($d > $currMonthNoDays-1) {
			$m += (int)($d/$currMonthNoDays);
			$d = $d%$currMonthNoDays;
		}
		if ($d<0) {
			$m--;
			$mTmp = $m;
			$YTmp = $Y;
			if ($mTmp < 1) {
				$mTmp = 12;
				$YTmp--;
			}
			$ts = @mktime(0, 0, 0, $mTmp, 1, $YTmp);
			if ($ts < 0) {
				die("MX Calendar Error: dates must be somewhere withing year range: 1901 and 2038.");
			}
			$currMonthNoDays = date('t', $ts);
			$d = $currMonthNoDays+$d;
		}
		$d++;
	} else {
		$needExtraNorm = true;
	}

	$m--;
	if ($m>11) {
		$Y += (int)($m/12);
		$m = $m%12;
	}
	if ($m<0) {
		$Y += (int)(($m-11)/12);
		$m = 11-(abs($m)-1)%12;
	}
	$m++;

	if ($needExtraNorm) {
		list($Y, $m, $d, $H, $i, $s) = CAL_normalize($Y, $m, $d, $H, $i, $s);
	}

	return array($Y, $m, $d, $H, $i, $s);
}

function CAL_addDate($date_ymd, $value, $to_what) {
	if (empty($date_ymd)){
			die("MX Calendar Error: the start dates cannot be null.");
	}
	list($Ymd, $His) = explode(' ', $date_ymd);
	list($Y, $m, $d) = explode('-', $Ymd);
	list($H, $i, $s) = explode(':', $His);

	switch ($to_what) {
		case "i":
			$i+=$value;
			break;
		case "H":
			$H+=$value;
			break;
		case "d":
			$d+=$value;
			break;
		case "m":
			$m+=$value;
			break;
		case "Y":
			$Y+=$value;
			break;
	}

	list($Y, $m, $d, $H, $i, $s) = CAL_normalize($Y, $m, $d, $H, $i, $s);
	if ($m<10) {
		$m = '0' . (int)$m;
	}
	if ($d<10) {
		$d = '0' . (int)$d;
	}
	if ($H<10) {
		$H = '0' . (int)$H;
	}
	if ($i<10) {
		$i = '0' . (int)$i;
	}
	if ($s<10) {
		$s = '0' . (int)$s;
	}

	return "$Y-$m-$d $H:$i:$s";
}

function CAL_DateIntersect($startDate1, $endDate1, $startDate2, $endDate2) {
	$ret = false;
	if ($startDate1 >= $startDate2 && $endDate1 <= $endDate2) {
		$ret = true;
	} elseif ($startDate1 <= $startDate2 && $endDate1 >= $endDate2) {
		$ret = true;
	} elseif ($startDate1 >= $startDate2 && $startDate1 < $endDate2) {
		$ret = true;
	} elseif ($endDate1 > $startDate2 && $endDate1 <= $endDate2) {
		$ret = true;
	}
	return $ret;
}

function CAL_dynamicLink($dynamicLink) {
	return KT_DynamicData($dynamicLink, '', '', false, array(), false);
}

function CAL_compareEvents($e1, $e2) {
	$cmp1 = $e1['start'];
	$cmp2 = $e2['start'];
	if ($cmp1 == $cmp2) {
		return 0;
	}
	return ($cmp1 < $cmp2) ? -1 : 1;
}

function CAL_getLink($vParam, $vValue) {
	if ($vValue == "today") {
		return CAL_XHTML_Url(KT_addReplaceParam(KT_getFullUri(), $vParam, KT_convertDate(date('Y-m-d'), "yyyy-mm-dd", $GLOBALS['KT_db_date_format'])));
	} else {
		return CAL_XHTML_Url(KT_addReplaceParam(KT_getFullUri(), $vParam, $vValue));
	}
}

function CAL_roundHour($date, $direction) {
	list($Ymd, $His) = explode(' ', $date);
	list($Y, $m, $d) = explode('-', $Ymd);
	list($H, $i, $s) = explode(':', $His);
	$s = '00';
	if ($i == 0 || $i == 30) {
		return $date;
	}

	if ($direction == "down") {
		if ($i < 30) {
			$i = "00";
		} else {
			$i = "30";
		}
	} else {
		if ($i < 30) {
			$i = "30";
		} else {
			$i = "00";
			list($Y, $m, $d, $H, $i, $s) = CAL_normalize($Y, $m, $d, $H+1, $i, $s);
		}
	}

	if ($m<10) {
		$m = '0' . (int)$m;
	}
	if ($d<10) {
		$d = '0' . (int)$d;
	}
	if ($H<10) {
		$H = '0' . (int)$H;
	}
	if ($i<10) {
		$i = '0' . (int)$i;
	}
	if ($s<10) {
		$s = '0' . (int)$s;
	}

	return "$Y-$m-$d $H:$i:$s";
}

function CAL_extract($format, $date) {
	list($Ymd, $His) = explode(' ', $date);
	list($Y, $m, $d) = explode('-', $Ymd);
	list($H, $i, $s) = explode(':', $His);
	
	$date = $Ymd." 12:00:00";

	if (strpos($format, 'w') !== false) {
		$w = @date('w', strtotime($date));
	} else {
		$w = '';
	}
	if (strpos($format, 'F') !== false) {
		$F = @date('F', strtotime($date));
	} else {
		$F = '';
	}
	if (strpos($format, 'W') !== false) {
		$wbig = @date('W', strtotime($date));
	} else {
		$wbig = '';
	}
	if (strpos($format, 'l') !== false) {
		$l = @date('l', strtotime($date));
	} else {
		$l = '';
	}

	$ret = str_replace(array('F', 'w', 'W', 'l'), array('_F_', '_w_', '_W_', '_l_'), $format);
	$ret = str_replace(array('Y', 'm', 'd', 'H', 'i', 's', '_l_', '_F_', '_w_', '_W_', ), array($Y, $m, $d, $H, $i, $s, $l, $F, $w, $wbig), $ret);

	return $ret;
}

function CAL_hourDiff($startDate, $endDate) {
	$h1 = CAL_extract('H', $startDate) + CAL_extract('i', $startDate)/60;
	$h2 = CAL_extract('H', $endDate) + CAL_extract('i', $endDate)/60;

	$tmp = 0;

	if (CAL_extract('d', $startDate) != CAL_extract('d', $endDate)) {
		$tmp = 24;
	}

	return $tmp + $h2-$h1;
}

/*
* function CAL_glueQueryStrings : keepes URL and params from source and adds distinct params from second string
*
*/
function CAL_glueQueryStrings($qstring_src, $qstring_aux) {
	// extract the URI if any
	if (strpos($qstring_src, '?') !== false) {
		$uri = preg_replace("/\?.*$/", '', $qstring_src);
		$qstring_src = preg_replace("/^.*\?/", '', $qstring_src);
	} else {
		if (strpos($qstring_src, "=") !== false) {
			$uri = '';
		} else {
			$uri = $qstring_src;
			$qstring_src = '';
		}
	}
	
	if (strpos($qstring_aux, '?') !== false) {
		$qstring_aux = preg_replace("/^.*\?/", '', $qstring_aux);
	} else {
		if (strpos($qstring_aux, "=") === false) {
			$qstring_aux = '';
		}
	}
	
	$src_params = explode('&', $qstring_src);
	$aux_params = explode('&', $qstring_aux);
	
	foreach($src_params as $src_key => $src_param) {
		if (trim($src_param) != '') {
			$src_param_name = explode('=', $src_param);
			$src_param_name = $src_param_name[0];
			foreach($aux_params as $aux_key => $aux_param) {
				if (trim($aux_param) != '') {
					$aux_param_name = explode('=', $aux_param);
					$aux_param_name = $aux_param_name[0];
					if ($src_param_name == $aux_param_name) {
						unset($aux_params[$aux_key]);
					}
				} else {
					unset($aux_params[$aux_key]);
				}
			}
		} else {
			unset($src_params[$src_key]);
		}
	}
	
	$qstring = array_merge($src_params, $aux_params);
	$qstring = implode('&', $qstring);
	
	if ($qstring != '') {
		$uri .= '?' . $qstring;
	}
	return $uri;
}

?>