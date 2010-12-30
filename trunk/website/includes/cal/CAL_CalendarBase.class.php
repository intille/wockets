<?php
class CAL_CalendarBase 
{
	var $relPath;
	var $dateParam;
	var $viewModParam;
	var $rs;
	var $recordsetName;
	var $arrFields;
	var $eventLink;
	var $newEventLink;
	var $newEventEnabled;
	var $newEventEnabledExp;
	var $mondayFirst;
	var $viewWeekNo;
	var $err;
	var $fromYearView;

	function CAL_CalendarBase($relPath) {
		$this->relPath = $relPath; 
		$this->mondayFirst = true;
		$this->fromYearView = false;
	}	
	
	function setDateParam($dateParam) {
		$this->dateParam = $dateParam;
	}
	
	function setViewModParam($viewModParam) {
		$this->viewModParam = $viewModParam;
	}
	
	function setRecordset($recordsetName) {
		$this->recordsetName = $recordsetName;
		if (!isset($GLOBALS[$recordsetName])) {
			$this->err = 'error';
			return;
		}
		$recordset = &$GLOBALS[$this->recordsetName];
		if (is_resource($recordset)) {
			$this->rs = new KT_Recordset($recordset); 
		} else {
			$this->rs = &$recordset;
			// super dirty hack pentru ca se pierd referinte
			// $this->rs->MoveLast();
			// $this->rs->MoveNext();
			$this->rs->MoveFirst();
		}
	} 
	
	function setField($key, $column) {
		$this->arrFields[strtoupper($key)] = $column;
	}
	
	function setNewEventEnabled($expr='') {
		if ($expr=='') {
			$expr = '1==2';
		}		
		$this->newEventEnabledExp = $expr;
		$run = KT_DynamicData($expr, '', 'expression');
		$runTrigger = false;
		$ok = false;
		eval('$runTrigger = ('.$run.');$ok = true;');
		if ($ok !== true) {
			die('Internal Error.Invalid boolean expression: '.$run);
		}
		if ($runTrigger) {
			$this->newEventEnabled = true;
		} else {
			$this->newEventEnabled = false;
		}
	}
	
	function setEventLink($url) {
		$this->eventLink = $this->parseForPlaceHolders($url);
	}

	function setNewEventLink($url='') {
		if (!strpos($url, '?')) {
			$url .= '?';
		}
		$this->newEventLink = $this->parseForPlaceHolders($url);
		//$this->newEventLink = $url;
	}
	
	function setMondayFirst($bol) {
		$this->mondayFirst = $bol;
	}

	function setViewWeekNo($viewWeekNo) {
		$this->viewWeekNo = $viewWeekNo;
	}


	function getRelPath() {
		return $this->relPath;
	}

	function &getRecordset() {
		return $this->rs;
	}
	
	function getFieldName($name) {
		if (isset($this->arrFields[$name])) {
			return $this->arrFields[$name];	
		} else {
			return null;
		}	
	}
	
	function getRecordsetName() {
		return $this->recordsetName;	
	}
	
	function getEventLink() {
		return $this->eventLink;
	}
	
	function getNewEventEnabled() {
		return $this->newEventEnabled;	
	}
	
	function getNewEventEnabledExp() {
		return $this->newEventEnabledExp;	
	}
	
	function getNewEventLink() {
		$newEventLink = $this->newEventLink;
		$newEventLink = KT_DynamicData($newEventLink, '', '', false, array(), false);
		return $newEventLink;
	}
	
	function getViewModParam() {
		return $this->viewModParam;	
	}
	
	function getDateParam() {
		return $this->dateParam;	
	}
	
	function getMondayFirst() {
		return $this->mondayFirst;
	}

	function getViewWeekNo() {
		return $this->viewWeekNo;
	}

	function getFromYearView() {
		return $this->fromYearView;
	}
	
	function parseForPlaceHolders($text) {
		$arrKeys = array_keys($this->arrFields);
		foreach ($arrKeys as $key => $val) {
			if (preg_match("/\{".$val."\}/i", $text)) {
				$text = str_replace('{'.$val.'}', '{' . $this->getRecordsetName() . '.' . $this->getFieldName($val) . '}' , $text);
			}
		}
		return $text;	
	}
}
?>