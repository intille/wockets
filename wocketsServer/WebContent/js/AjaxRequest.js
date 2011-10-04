/**Created By Salim Khan
 * Project Wockets
 *
 * General Ajax request Method
 */

function getAjaxGETRequest()
{
	var xmlHttp = null;

	if(window.ActiveXObject)
	{
	  xmlHttp=new ActiveXObject("Microsoft.XMLHTTP");
	}
	else if(window.XMLHttpRequest)
	{
	  xmlHttp=new XMLHttpRequest();
	}

	return xmlHttp;
}