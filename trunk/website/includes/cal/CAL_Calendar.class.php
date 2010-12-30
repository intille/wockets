<?php
class CAL_Calendar extends CAL_CalendarBase
{
	var $maxEvents;
	var $defaultView;
	var $startHour;
	var $endHour;
	var $forceDateParam;
	var $addEventTarget;
	var $viewEventTarget;
	var $displayEndHour;
	var $specificEventClass;
	var $sendKTBack;
		
	function CAL_Calendar($relPath) {
		$this->relPath = $relPath; 
		$this->mondayFirst = true;
		$this->forceDateParam = '';
		
		$this->type = 'view';
		$this->fromYearView = false;
		$this->addEventTarget = '';
		$this->viewEventTarget = '';
		$this->displayEndHour = true;
		$this->specificEventClass = '';
		$this->sendKTBack = false;
	}	
	
	function setDefaultView($defaultView) {
		$this->defaultView = strtolower($defaultView);
	}
	
	function setStartHour($startHour) {
		$this->startHour = $startHour;
		if ($this->startHour < 10) {
			$this->startHour = '0'.$this->startHour;
		}
	}
	
	function setEndHour($endHour) {
		$this->endHour = $endHour;
		if ($this->endHour < 10) {
			$this->endHour = '0'.$this->endHour;
		}
	}
	
	function setMaxEvents($maxEvents) {
		$this->maxEvents = $maxEvents;
	}
	
	function setAddEventTarget($addEventTarget) {
		$this->addEventTarget = $addEventTarget;
	}
	
	function setViewEventTarget($viewEventTarget) {
		$this->viewEventTarget = $viewEventTarget;
	}
	
	function setDisplayEndHour($displayEndHour) {
		$this->displayEndHour = $displayEndHour;
	}
	
	function setSpecificEventClass($specificEventClass) {
		$this->specificEventClass = $specificEventClass;
	}
	
	function setSendKTBack($sendKTBack) {
		$this->sendKTBack = $sendKTBack;
	}
	
	function setEventLink($url) {
		if (!preg_match("/\{ID\}/ms", $url)) {
			$url = KT_addReplaceParam($url, $this->getFieldName("ID"), "{ID}");
			$url = str_replace("%7BID%7D", "{ID}", $url);
		}
		$this->eventLink = $this->parseForPlaceHolders($url);
	}

	function render() {
		$how = $this->getDefaultView();
		if (isset($_GET[$this->getViewModParam()])) {
			$how = strtolower($_GET[$this->getViewModParam()]);
		}
		switch ($how) {
			case 'day':
				$renderer = new CAL_ViewDay($this);
				break;
			case 'year':
				$renderer = new CAL_ViewYear($this);
				break;
			case 'week':
				$renderer = new CAL_ViewWeek($this);
				break;
			case 'month':
				$renderer = new CAL_ViewMonth($this);
				break;
			default:
				break;
		}
		if (isset($renderer)) {
			$renderer->render();
		}
	}

	function getAddEventTarget() {
		return $this->addEventTarget;
	}
	
	function getViewEventTarget() {
		return $this->viewEventTarget;
	}
	
	function getDisplayEndHour() {
		return $this->displayEndHour;
	}
	
	function getSpecificEventClass() {
		return $this->specificEventClass;
	}
	
	function getSendKTBack() {
		return $this->sendKTBack;
	}

	function getMaxEvents() {
		return $this->maxEvents;	
	}
	
	function getStartHour() {
		return $this->startHour;	
	}
	
	function getEndHour() {
		return $this->endHour;	
	}
	
	function getDefaultView() {
		if ($this->defaultView!='') {
			return $this->defaultView;
		} else {
			return 'day';	
		}
	}
}
?>