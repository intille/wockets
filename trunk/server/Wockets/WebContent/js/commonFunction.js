
function createErrorLabel(errMessage,parent,labelId)
{
	var errLabel = document.getElementById(labelId);
	if(errLabel)
		parent.removeChild(errLabel);
	var newErrorLabel = document.createElement('label');
	newErrorLabel.setAttribute('id',labelId);
	newErrorLabel.innerHTML= errMessage;
	newErrorLabel.style.color = 'red';
	parent.appendChild(newErrorLabel);
}