<?php
class CAL_CalendarNugget  extends CAL_CalendarBase
{
	var $forcedDate;
	var $detailPage;
	var $detailTarget;
		
	function CAL_CalendarNugget($relPath) {
		$this->relPath = $relPath; 
		$this->mondayFirst = true;
		$this->fromYearView = false;
		$this->displayAs = 'html';
		$this->forcedDate = '';
		$this->type = 'nugget';
		$this->detailPage = '';
		$this->detailTarget = '';
	}
	
	function forceDateParam($forcedDate) {
		$this->forcedDate = $forcedDate;
	}
	
	function setFromYearView($fromYearView) {
		$this->fromYearView = $fromYearView;
	}
	
	function displayAs($displayAs) {
		$this->displayAs = strtolower($displayAs);
	}

	function render() {
		switch ($this->getDisplayAs()) {
			case 'html':
				$renderer = new CAL_ViewNuggetHtml($this);
				break;
			default:
				break;
		}
		if (isset($renderer)) {
			$renderer->render();
		}
	}
	
	function getDisplayAs() {
		return $this->displayAs;	
	}

	function setDetailPage($detailPage, $detailTarget) {
		$this->detailPage = $detailPage;
		$this->detailTarget = $detailTarget;
	}

}
?>