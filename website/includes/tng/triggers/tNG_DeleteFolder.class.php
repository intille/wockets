<?php
/*
	Copyright (c) InterAKT Online 2000-2006. All rights reserved.
*/
/**
 * This the tNG_DeleteFolder trigger; 
 * Only for PRO version
 * Delete the related folder.
 * @access public
 */ 
class tNG_DeleteFolder {
	/**
	 * The tNG object
	 * @var object tNG
	 * @access public
	 */
	var $tNG;
	/**
	 * base folder
	 * @var string
	 * @access public
	 */
	var $baseFolder;
	/**
	 * folder to be deleted inside baseFolder;
	 * @var string
	 * @access public
	 */
	var $folder;
	/**
	 * full name folder
	 * @var string
	 * @access public
	 */
	var $fullFolder;
	/**
	* Constructor. Sets the reference to the transaction in which the trigger is used.
	* @param object tNG &$tNG reference to transaction object
	* @access public
	*/
   function tNG_DeleteFolder(&$tNG) {
		$this->tNG = &$tNG;
		$this->folder = '';
	}
    /**
	* Setter. Sets base folder
	* @param string 
	* @access public
	*/
    function setBaseFolder($baseFolder) {
    	$pos = strpos($baseFolder, '{');
		if ($pos !== false) {
			$this->folder = KT_DynamicData(substr($baseFolder, $pos), $this->tNG, '', false, array(), false);
    		$this->baseFolder = substr($baseFolder, 0, $pos);
		} else {
			$this->folder = '';
    		$this->baseFolder = $baseFolder;
		}
    	$this->baseFolder = KT_realpath($baseFolder);
    }
    /**
	* Setter. Sets the dynamic part of the folder
	* @param string 
	* @access public
	*/
	function setFolder($folder) {
		$this->folder .= KT_DynamicData($folder, $this->tNG, '', false, array(), false);
	}
	/**
	* Main class methode
	* @return mixt null or error object in case of error;
	* @access public
	*/
    function Execute() {
		$this->fullFolder = KT_realpath($this->baseFolder. $this->folder);
		// security
		if (substr($this->fullFolder, 0, strlen($this->baseFolder)) != $this->baseFolder) {
			$ret = new tNG_error("FOLDER_DEL_SECURITY_ERROR", array(), array($this->fullFolder, $this->baseFolder));
			return $ret;
		}
    	$ret = null;
    	if (!file_exists($this->fullFolder)) {
    		return $ret;	
    	}
    	$folder = new KT_Folder();
    	// delete thumbnails;
    	$folder->deleteFolderNR($this->fullFolder);
    	if ($folder->hasError()) {
    		$arr = $folder->getError();
    		$ret = new tNG_error("FOLDER_DEL_ERROR", array($arr[0]), array($arr[1]));
    		return $ret;
    	}    	
    	return $ret;	
    }	
}
?>
