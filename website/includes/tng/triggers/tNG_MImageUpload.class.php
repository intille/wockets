<?php
/*
	Copyright (c) InterAKT Online 2000-2006. All rights reserved.
*/

/**
 * Handle the multimpe image upload.
 * Only for PRO version	 
 * @access public
 */
class tNG_MImageUpload extends tNG_MFileUpload {
	/**
	 * hash with resize values
	 * @var array 
	 * @access private
	 */
	var $resize; 
	/**
	 * hash with thumbnail options
	 * @var array 
	 * @access private
	 */
	var $thumbnail;
	/**
	 * Constructor. Sets relpath, reference value, connection name
	 * @param string relpath
	 * @param string reference
	 * @param string connection name
	 * @access public
	 */
	function tNG_MImageUpload($relPath, $reference, $connName) {
    	parent::tNG_MFileUpload($relPath, $reference, $connName);
    	$this->resize = array();
    	$this->thumbnail = array();
		$this->showThumbnail(150,100,true);
		$this->showImagePopup(640,480);

    }
     /**
	 * Setter. Sets the thumbnails values
	 * @param int width 
	 * @param int height
	 * @param boolean keep proportion
	 * @access private
	 */
    function setResize($width, $height, $keepProportion) {
    	$this->resize['width'] = $width;
    	$this->resize['height'] = $height;
    	$this->resize['keepProportion'] = $keepProportion;
    }
    /**
	 * Setter. Sets the thumbnails values
	 * @param int width 
	 * @param int height
	 * @param boolean keep proportion
	 * @access private
	 */
    function showThumbnail($width, $height, $keepProportion) {
    	$this->thumbnail['width'] = $width;
    	$this->thumbnail['height'] = $height;
    	$this->thumbnail['keepProportion'] = $keepProportion;
    }
    /**
	 * Setter. sets if the image popup will be used and of what sizes
	 * @param int width
	 * @param int height
	 * @access private
	 */
    function showImagePopup($width, $height) {
    	$this->thumbnail['popupWidth'] = $width; 
    	$this->thumbnail['popupHeight'] = $height;
    }
    
     /**
	 * Getter. Gets the link to the upload page
	 * sets in session the neccesary info
	 * @return string
	 * @access public
	 */
    function getUploadLink() {
    	$url = parent::getUploadLink();
    	if ($url == '') {
    		return '';	
    	}
    	if ($this->noOfCalls == 1) {
			$_SESSION['tng_upload'][$this->reference]['properties']['resize'] = $this->resize;
			$_SESSION['tng_upload'][$this->reference]['properties']['thumbnail'] = $this->thumbnail;
			$_SESSION['tng_upload'][$this->reference]['properties']['isImage'] = true;
    	}
		return $url;
    }
}
?>
