<?php

class CAL_ViewBase {

  var $calendar;
	
	var $todayDate;
	var $todayDate_db;
	var $selectedDate;
	var $selectedDate_db;
	
	var $startDate;
	var $endDate;
	
	var $data;

	function CAL_ViewBase(&$calendar) {
		$this->calendar = &$calendar;
		$this->data = array();
		$this->data['nav'] = array();
		$this->data['body'] = array();
	}	
	
	function render() {
		$this->_setTodaySelected();
		$this->_setInterval();
		$this->_prepareNav();
		$this->_computeEvents();
		$this->_transformEvents();
		$this->_renderData();
	}
	
	function _checkValidDate($date) {
		$ret = $date;
		
		$inFmtRule = KT_format2rule($GLOBALS['KT_db_date_format']. ' '.$GLOBALS['KT_db_time_format_internal']);
		$dateArr = KT_applyDate2rule($date, $inFmtRule);
		$valid = KT_isValidDate($dateArr, true);
		if (!$valid) {
			$ret = $this->todayDate_db;
		}
		if (strlen($ret) == 10) {
			$ret .= ' 00:00:00';
		}	
		if (strlen($ret) != 19) {
			$ret = $this->todayDate_db.' 00:00:00';
		}
		//echo $date." -> ".$ret."<br/>\n";
		return $ret;
	}
	
	function _setTodaySelected() {
		//Set Today Date and Selected Date (Y-m-d & db format - _db)
		$this->todayDate = date('Y-m-d') . ' 00:00:00';
		$this->todayDate_db = KT_convertDate($this->todayDate, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']);
		$dateRef = $this->calendar->getDateParam();
		if (isset($_GET[$dateRef])) {
			$this->selectedDate_db = $_GET[$dateRef];
			$this->selectedDate_db = $this->_checkValidDate($this->selectedDate_db);
		} else {
			$this->selectedDate_db = $this->todayDate_db;
		}
		$format = $GLOBALS['KT_db_date_format'];
		if (strpos($this->selectedDate_db,' ') !== false || strpos($this->selectedDate_db,':') !== false) {
			$format .= ' '.$GLOBALS['KT_screen_time_format_internal'];
		}
		$this->selectedDate = KT_convertDate($this->selectedDate_db, $format, 'yyyy-mm-dd');
		$this->selectedDate .= ' 00:00:00';
	}
	
	function _transformEvents() {
		$page = $this->calendar->getNewEventLink();
		$page_sep = "?";
		$page_day = KT_getFullUri();
		$screenDateTimeFormat = $GLOBALS['KT_screen_date_format'] . ' ' . $GLOBALS['KT_screen_time_format_internal'];
	
		if ($this->calendar->getFromYearView() == true && $this->calendar->forcedDate != '') {
			$selectedDate = CAL_addDate($this->calendar->forcedDate, 0, 'd');
		}else{
			$selectedDate = CAL_addDate($this->selectedDate, 0, 'd');
		}

		if ($this->calendar->type == 'view') {
			if ($this->calendar->sendKTBack) {
				$page = KT_addReplaceParam($page, 'KT_back', 1);
			} else {
				foreach($_GET as $key => $value) {
					$page = CAL_glueQueryStrings($page, $key . '=' . $value);
					//$page = KT_addReplaceParam($page, $key, $value);
				}
			}
		}
		
		$page = KT_addReplaceParam($page, $this->calendar->dateParam, NULL);
		$page = KT_addReplaceParam($page, $this->calendar->dateParam . "_sf", NULL);
		if (strpos($page,"?") !== false) {
			$page_sep = "&";
		}
		
		$page_day = KT_addReplaceParam($page_day, $this->calendar->dateParam, NULL);
		$page_day = KT_addReplaceParam($page_day, $this->calendar->viewModParam, 'day');
		
		$cDate = CAL_extract('Y-m-d',$this->startDate) . ' 00:00:00';
		$prevMonth = '';
		$ym_selectedDate = CAL_extract('Y-m', $selectedDate);
		while ($cDate < $this->endDate) {
			$this->data['body'][$cDate]['day'] = CAL_extract('d',$cDate);
			
			$this->data['body'][$cDate]['othermonth'] = CAL_extract('Y-m', $cDate) != $ym_selectedDate;
			
			$tmp_weekday = CAL_extract('w', $cDate);
			$this->data['body'][$cDate]['weekend'] = ($tmp_weekday == 0 || $tmp_weekday == 6);
			
			if ($this->calendar->fromYearView == false) {
				$this->data['body'][$cDate]['weekday'] = CAL_extract('l',$cDate);
				$this->data['body'][$cDate]['month'] = '';
				$tmpMonth = CAL_extract('m',$cDate);
				if ($prevMonth != $tmpMonth) {
					$prevMonth = $tmpMonth;
					$this->data['body'][$cDate]['month'] = CAL_extract('F',$cDate);
				}
			}

			$tmp_date = $cDate;
			
			if ($this->calendar->getNewEventEnabled()) {
				if ($this->calendar->type == 'view') {
					$tmp_date = CAL_addDate($cDate, $this->calendar->getStartHour(), 'H');
				}
				$tmppage = $page . $page_sep . $this->calendar->dateParam . "=" . rawurlencode(KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
				$tmppage = $tmppage . "&" . $this->calendar->dateParam . "_sf=" . rawurlencode(KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $screenDateTimeFormat));
				$this->data['body'][$cDate]['add'] = $tmppage;
			}
			
			$this->data['body'][$cDate]['link'] = $page_day ."&" . $this->calendar->getDateParam() . "=" . rawurlencode(KT_convertDate($tmp_date, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
			
			if (!isset($this->data['body'][$cDate]['event'])) {
				$this->data['body'][$cDate]['event'] = array();
				$this->data['body'][$cDate]['title'] = CAL_getResource('VIEW_DAY');
			} else {
				if ($this->calendar->getFromYearView() == false) {
					usort($this->data['body'][$cDate]['event'], "CAL_compareEvents");
					$this->data['body'][$cDate]['title'] = $this->data['body'][$cDate]['event'][0]['title'];
					for ($i=1;$i<count($this->data['body'][$cDate]['event']);$i++) {
						$this->data['body'][$cDate]['title'] .= "\n" . $this->data['body'][$cDate]['event'][$i]['title'];
					}
				} else {
					$this->data['body'][$cDate]['title'] = CAL_getResource('VIEW_DAY');
				}
			}
			$cDate = CAL_addDate($cDate, 1, 'd');
		}
		ksort($this->data['body']);
		if (isset($this->data['body'][$this->todayDate])) {
			$this->data['body'][$this->todayDate]['today'] = true;
		}
		if (isset($this->data['body'][$this->selectedDate])) {
			$this->data['body'][$this->selectedDate]['selected'] = true;
		}
	}
	
  function _computeEvents() {
		$rs = &$this->calendar->getRecordset();
		$dbDateTimeFormat = $GLOBALS['KT_db_date_format'] . ' ' . $GLOBALS['KT_db_time_format_internal'];
		$fn_START_DATE = $this->calendar->getFieldName('START_DATE');
		$fn_END_DATE = $this->calendar->getFieldName('END_DATE');
		$fn_RECURRING = $this->calendar->getFieldName('RECURRING');
		$fn_TITLE = $this->calendar->getFieldName('TITLE');
		$fn_DESCRIPTION = $this->calendar->getFieldName('DESCRIPTION');
		
		$rs->MoveFirst();
		while (!$rs->EOF) {
			$GLOBALS["row_".$this->calendar->getRecordsetName()] = $rs->fields;
			$startDate = $rs->Fields($fn_START_DATE);
			$startDate = KT_convertDate($startDate, $dbDateTimeFormat, 'yyyy-mm-dd HH:ii:ss');
			
			if ($fn_END_DATE !== NULL && $rs->Fields($fn_END_DATE) != '') {
				$endDate = $rs->Fields($fn_END_DATE);
				$endDate = KT_convertDate($endDate, $dbDateTimeFormat, 'yyyy-mm-dd HH:ii:ss');
			} else {
				if ($fn_RECURRING !== NULL && trim($rs->Fields($fn_RECURRING)) != '') {
					$endDate = $this->endDate;
				} else {
					$endDate = CAL_addDate($startDate, 1, 'H');
				}
			}
			
			if (strlen($startDate) == 10) {
				$startDate .= ' 00:00:00';
			}
			if (strlen($endDate) == 10) {
				$endDate .= ' 00:00:00';
			}
			if ($endDate <= $startDate) {
				$endDate = CAL_addDate($startDate, 1, 'H');
			}
			$specificClass = '';
			if ($this->calendar->type == 'view') {
				if ($this->calendar->getSpecificEventClass() != '') {
					$specificClass = $rs->Fields($this->calendar->getSpecificEventClass());
				}
			}
			$start = null;
			$end = null;
			if ($startDate >= $this->startDate && $endDate <= $this->endDate) {
				$start = $startDate;
				$end = $endDate;
			} elseif ($startDate <= $this->startDate && $endDate >= $this->endDate) {
				$start = $this->startDate;
				$end = $this->endDate;
			} elseif ($startDate >= $this->startDate && $startDate < $this->endDate) {
				$start = $startDate;
				$end = $this->endDate;
			} elseif ($endDate > $this->startDate && $endDate <= $this->endDate) {
				$start = $this->startDate;
				$end = $endDate;
			}
			
			if ($start !== NULL && $end !== NULL) {
				if ($fn_RECURRING !== NULL && in_array(strtoupper($rs->Fields($fn_RECURRING)),array('DAY','WEEK','MONTH','YEAR')) ) {
					// Recurring Events	
					switch (strtoupper($rs->Fields($fn_RECURRING))) {
						case 'DAY':
							$cDate = CAL_extract('Y-m-d', $start) . ' ' . CAL_extract('H:i:s', $startDate);
							$arrDates = array();
							do {
								if ($cDate <= $endDate) {
									$arrDates[] = $cDate;
								}
								$cDate = CAL_addDate($cDate, 1, 'd');
							} while ($cDate < $end);
							if ($cDate >= $end) {
								$cDate = $end;
								$arrDates[] = $cDate;
							}
							
							// Create events array;
							$t_title = $rs->Fields($fn_TITLE);
							$t_desc = "";
							$t_link = "";
							if ($this->calendar->type == 'view') {
								if ($fn_DESCRIPTION != null) {
									$t_desc = KT_FormatForList($rs->Fields($fn_DESCRIPTION),255);
								}
								$t_link = KT_DynamicData($this->calendar->getEventLink(), '', '', false, array(), false);
								if ($this->calendar->sendKTBack) {
									$t_link = KT_addReplaceParam($t_link, 'KT_back', 1);
								} else {
									foreach($_GET as $key => $value) {
										$t_link = CAL_glueQueryStrings($t_link, $key . '=' . $value);
										//$t_link = KT_addReplaceParam($t_link, $key, $value);
									}
								}
							}
							$tmp_hour = CAL_extract('H',$endDate);
							$tmp_minute = CAL_extract('i',$endDate);
							for ($i=1;$i<count($arrDates);$i++) {
								$tmp_sdate = $arrDates[$i-1];
								$cDate = CAL_extract('Y-m-d',$tmp_sdate) . ' 00:00:00';
								$tmp_edate = CAL_addDate($cDate, 60*$tmp_hour+$tmp_minute, 'i');
								if ($tmp_edate <= $tmp_sdate) {
									$tmp_edate = CAL_addDate($tmp_sdate, 1, 'H');
								}
								if ($this->calendar->type == 'view') {
									$t_link = KT_addReplaceParam($t_link, $this->calendar->dateParam, KT_convertDate($cDate, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
								}
								$tmp_arr = array(
									'start' => $tmp_sdate,
									'end' => $tmp_edate,
									'title' => $t_title,
									'desc' => $t_desc,
									'link' => $t_link,
									'class' => $specificClass
								);
								$this->data['body'][$cDate]['event'][] = $tmp_arr;
							}
							
							break;
						case 'WEEK':
							$tmp_week_day = CAL_extract('w',$startDate);
							//echo $startDate.' = '.$tmp_week_day."<br/>\n";
							$tmp_week_day2 = CAL_extract('w',$this->startDate);
							//echo $this->startDate.' = '.$tmp_week_day2."<br/>\n";
							$tmp_week_day -= $tmp_week_day2;
							$cDate = CAL_addDate($this->startDate, $tmp_week_day, 'd');
							$cDate = CAL_extract('Y-m-d', $cDate) . ' ' . CAL_extract('H:i:s',$startDate);
							$arrDates = array();
							while ($cDate <= $end) {
								if ($cDate>=$startDate && $cDate >= $this->startDate && $cDate <= $this->endDate) {
									$arrDates[] = $cDate; 
								}
								$cDate = CAL_addDate($cDate, 7, 'd');
							}
							// Create events array;
							$t_title = $rs->Fields($fn_TITLE);
							$t_desc = "";
							$t_link = "";
							if ($this->calendar->type == 'view') {
								if ($fn_DESCRIPTION != null) {
									$t_desc = KT_FormatForList($rs->Fields($fn_DESCRIPTION),255);
								}
								$t_link = KT_DynamicData($this->calendar->getEventLink(), '', '', false, array(), false);
								if ($this->calendar->sendKTBack) {
									$t_link = KT_addReplaceParam($t_link, 'KT_back', 1);
								} else {
									foreach($_GET as $key => $value) {
										$t_link = CAL_glueQueryStrings($t_link, $key . '=' . $value);
										//$t_link = KT_addReplaceParam($t_link, $key, $value);
									}
								}
							}
							$tmp_hour = CAL_extract('H',$endDate);
							$tmp_minute = CAL_extract('i',$endDate);
							for ($i=0;$i<count($arrDates);$i++) {
								$tmp_sdate = $arrDates[$i];
								$cDate = CAL_extract('Y-m-d',$tmp_sdate) . ' 00:00:00';
								$tmp_edate = CAL_addDate($cDate, 60*$tmp_hour+$tmp_minute, 'i');
								if ($tmp_edate <= $tmp_sdate) {
									$tmp_edate = CAL_addDate($tmp_sdate, 1, 'H');
								}
								if ($this->calendar->type == 'view') {
									$t_link = KT_addReplaceParam($t_link, $this->calendar->dateParam, KT_convertDate($cDate, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
								}
								$tmp_arr = array(
									'start' => $tmp_sdate,
									'end' => $tmp_edate,
									'title' => $t_title,
									'desc' => $t_desc,
									'link' => $t_link,
									'class' => $specificClass
								);
								$this->data['body'][$cDate]['event'][] = $tmp_arr;
							}
							break;
						case 'MONTH':
              $tmpDate = CAL_extract('Y-m', $this->startDate) . '-' . CAL_extract('01 H:i:s', $startDate);
							$arrDates = array();
							$cDate = CAL_addDate($tmpDate, CAL_extract('d', $startDate)-1, 'd');
							while ($cDate <= $end) {
								if ($cDate >= $this->startDate && CAL_extract('d',$cDate) == CAL_extract('d',$startDate)) {
									$arrDates[] = $cDate; 
								}
								$tmpDate = CAL_addDate($tmpDate, 1, 'm');
								$cDate = CAL_addDate($tmpDate, CAL_extract('d', $startDate)-1, 'd');
							}
							// Create events array;
							$t_title = $rs->Fields($fn_TITLE);
							$t_desc = "";
							$t_link = "";
							if ($this->calendar->type == 'view') {
								if ($fn_DESCRIPTION != null) {
									$t_desc = KT_FormatForList($rs->Fields($fn_DESCRIPTION),255);
								}
								$t_link = KT_DynamicData($this->calendar->getEventLink(), '', '', false, array(), false);
								if ($this->calendar->sendKTBack) {
									$t_link = KT_addReplaceParam($t_link, 'KT_back', 1);
								} else {
									foreach($_GET as $key => $value) {
										$t_link = CAL_glueQueryStrings($t_link, $key . '=' . $value);
										//$t_link = KT_addReplaceParam($t_link, $key, $value);
									}
								}
							}
							$tmp_hour = CAL_extract('H',$endDate);
							$tmp_minute = CAL_extract('i',$endDate);
							for ($i=0;$i<count($arrDates);$i++) {
								$tmp_sdate = $arrDates[$i];
								$cDate = CAL_extract('Y-m-d',$tmp_sdate) . ' 00:00:00';
								$tmp_edate = CAL_addDate($cDate, 60*$tmp_hour+$tmp_minute, 'i');
								if ($tmp_edate <= $tmp_sdate) {
									$tmp_edate = CAL_addDate($tmp_sdate, 1, 'H');
								}
								if ($this->calendar->type == 'view') {
									$t_link = KT_addReplaceParam($t_link, $this->calendar->dateParam, KT_convertDate($cDate, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
								}
								$tmp_arr = array(
									'start' => $tmp_sdate,
									'end' => $tmp_edate,
									'title' => $t_title,
									'desc' => $t_desc,
									'link' => $t_link,
									'class' => $specificClass
								);
								$this->data['body'][$cDate]['event'][] = $tmp_arr;
							}
							break;
						case 'YEAR':
              $cDate = CAL_extract('Y', $this->startDate).'-'.CAL_extract('m-d H:i:s', $startDate);
							if ($cDate != CAL_addDate($cDate, 0, 'd')) {
								break;
							}
              $arrDates = array();
              while ($cDate <= $end) {
                if ($cDate >= $this->startDate) {
                  $arrDates[] = $cDate; 
                }
								$cDate = CAL_addDate($cDate, 1, 'Y');
              }
							// Create events array;
							$t_title = $rs->Fields($fn_TITLE);
							$t_desc = "";
							$t_link = "";
							if ($this->calendar->type == 'view') {
								if ($fn_DESCRIPTION != null) {
									$t_desc = KT_FormatForList($rs->Fields($fn_DESCRIPTION),255);
								}
								$t_link = KT_DynamicData($this->calendar->getEventLink(), '', '', false, array(), false);
								if ($this->calendar->sendKTBack) {
									$t_link = KT_addReplaceParam($t_link, 'KT_back', 1);
								} else {
									foreach($_GET as $key => $value) {
										$t_link = CAL_glueQueryStrings($t_link, $key . '=' . $value);
										//$t_link = KT_addReplaceParam($t_link, $key, $value);
									}
								}
							}
							$tmp_hour = CAL_extract('H',$endDate);
							$tmp_minute = CAL_extract('i',$endDate);
							for ($i=0;$i<count($arrDates);$i++) {
								$tmp_sdate = $arrDates[$i];
								$cDate = CAL_extract('Y-m-d',$tmp_sdate) . ' 00:00:00';
								$tmp_edate = CAL_addDate($cDate, 60*$tmp_hour+$tmp_minute, 'i');
								if ($tmp_edate <= $tmp_sdate) {
									$tmp_edate = CAL_addDate($tmp_sdate, 1, 'H');
								}
								if ($this->calendar->type == 'view') {
									$t_link = KT_addReplaceParam($t_link, $this->calendar->dateParam, KT_convertDate($cDate, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
								}
								$tmp_arr = array (
									'start' => $tmp_sdate,
									'end' => $tmp_edate,
									'title' => $t_title,
									'desc' => $t_desc,
									'link' => $t_link,
									'class' => $specificClass
								);
								$this->data['body'][$cDate]['event'][] = $tmp_arr;
							}
							break;
					}
				} else {
					// Non- Recurring Events
					//echo 'Non-Recurring: '.date('Y-m-d H:i:s',$start).' => '.date('Y-m-d H:i:s',$end)."\n";
					$cDate = $start;
					$arrDates = array();
					do {
						if ($cDate < $this->endDate) {
							$arrDates[] = $cDate; 
						}
						$cDate = CAL_addDate($cDate, 1, 'd');
					} while ($cDate < $end);
					if ($cDate >= $end) {
						$cDate = $end;
						if ($cDate <= $this->endDate) {
							$arrDates[] = $cDate;
						}
					}
					// Create events array;
					$t_title = $rs->Fields($fn_TITLE);
					$t_desc = "";
					$t_link = "";
					if ($this->calendar->type == 'view') {
						if ($fn_DESCRIPTION != null) {
							$t_desc = KT_FormatForList($rs->Fields($fn_DESCRIPTION),255);
						}
						$t_link = KT_DynamicData($this->calendar->getEventLink(), '', '', false, array(), false);
						if ($this->calendar->sendKTBack) {
							$t_link = KT_addReplaceParam($t_link, 'KT_back', 1);
						} else {
							foreach($_GET as $key => $value) {
								$t_link = CAL_glueQueryStrings($t_link, $key . '=' . $value);
								//$t_link = KT_addReplaceParam($t_link, $key, $value);
							}
						}
					}
					for ($i=1;$i<count($arrDates);$i++) {
						$tmp_sdate = $arrDates[$i-1];
						$tmp_edate = $arrDates[$i];
						if ($tmp_edate == $tmp_sdate) {
							$tmp_edate = CAL_addDate($tmp_edate,1, 'H');
						}
						$cDate = CAL_extract('Y-m-d', $tmp_sdate) . ' 00:00:00';
						if ($this->calendar->type == 'view') {
							$t_link = KT_addReplaceParam($t_link, $this->calendar->dateParam, KT_convertDate($cDate, 'yyyy-mm-dd HH:ii:ss', $GLOBALS['KT_db_date_format']));
						}
						$tmp_arr = array(
							'start' => $tmp_sdate,
							'end' => $tmp_edate,
							'title' => $t_title,
							'desc' => $t_desc,
							'link' => $t_link,
							'class' => $specificClass
						);
						$this->data['body'][$cDate]['event'][] = $tmp_arr;
					}
				}
			}
			$rs->MoveNext();
		}
		$rs->MoveFirst();
		//print_r($this->data); 
	}
}
?>