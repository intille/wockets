/**
 * Created By Salim Khan
 * Project: Wockets
 * Review Graph JavaScript
 */

var options;

function createOption()
{
	var options = {
			chart: {
					renderTo: 'container',
					defaultSeriesType: 'line',
			        borderWidth: 2,
			        zoomType: 'x',
			        reflow: true,
			        theme:"dark-green"
			        //theme:"grid"
					},
			title: {
					text: 'Review Data'
					},
		    credits: {
			            enabled: false
			        },
//		    navigator: {
//		    			top: 250
//			        },
			        navigator: { enabled: false },
			        scrollbar: { enabled: true},
			        
		    legend: {
			            enabled: true,
			            y:-20
			        },
		    rangeSelector: {
				    	buttons: [
//				    	          {
//				    		type: 'minute',
//							count: 1,
//							text: '1m'
//				    		
//				    	},
				    	{
							type: 'minute',
							count: 15,
							text: '15m'
						}, {
							type: 'hour',
							count: 1,
							text: '1h'
						}, {
							type: 'all',
							count: 1,
							text: 'All'
						}],
						selected: 2,
						inputEnabled: false
				   },
			yAxis: {
					title: {
					text: 'Units'
					}
				   },
		    series: []
};
	return options;
}


function createChart(divObj,chartDataJSON)
{
	options = null;
	options = getChartOptions(chartDataJSON);
	options.chart.renderTo= divObj;
	var chart = new Highcharts.StockChart(options);
	return chart;

}
//create option for chart
function getChartOptions(chartDataJSON)
{
	var options = createOption();
	
	//get wocket data
	var wockestData = chartDataJSON.wocketData;
	for(var i=0;i<wockestData.length;i++)
	{
		var wocketRecord = wockestData[i];
		for(var x=0;x<wocketRecord.length;x++)
		{
			var wocketData = wocketRecord[x];
			options.series.push(evalString(wocketData));
		}
	}
	//get phone stats
	var phoneStats = chartDataJSON.phoneStats;
	for(var i=0;i<phoneStats.length;i++)
	{
		var phoneData = phoneStats[i];
		if(phoneData.data.length > 0)
			options.series.push(evalString(phoneData));
	}
	
//	//get raw_Data_stats
//	var rawDataStats = chartDataJSON.rawDataStats;
//	if(rawDataStats.data.length > 0)
//		options.series.push(evalString(rawDataStats));
	
	//get swapped flags
//	var swappedFlagsList = chartDataJSON.swappedFlag;
//	for(var i=0;i<swappedFlagsList.length;i++)
//	{
//		var swappedFlags = swappedFlagsList[i];
//		options.series.push(evalStringForFlags(swappedFlags));
//		printWcktFlags(swappedFlags,"swappedTable");//pass flag JSON object and table DOM unique ID 
//	}
	var swappedFlag = chartDataJSON.swappedFlag;
	if(swappedFlag.data.length > 0)
	{
		options.series.push(evalStringForFlags(swappedFlag));
		printWcktFlags(swappedFlag,"swappedTable");
	}
	
	//get smsList
	var smsList = chartDataJSON.smsList;
	if(smsList.data.length > 0)
	{
		options.series.push(evalStringForFlags(smsList));
		printWcktFlags(smsList,"smsTable");
	}
	
	//get promptList
	var promptList = chartDataJSON.promptList;
	if(promptList.data.length > 0)
	{
		options.series.push(evalStringForFlags(promptList));
		printWcktFlags(promptList,"promptTable");
	}
	
	//get noteList
	var noteList = chartDataJSON.noteList;
	if(noteList.data.length > 0)
	{
		options.series.push(evalStringForFlags(noteList));
		printWcktFlags(noteList,"noteTable");
	}
	
	//get HRdata
	var heartRateData = chartDataJSON.hrData;
	for(var i=0;i<heartRateData.length;i++)
	{
		var hrData = heartRateData[i];
		if(hrData.data.length > 0)
			options.series.push(evalString(hrData));
	}
	
	//get dataUploadEvent
	var dataUploadEvent = chartDataJSON.dataUploadEvent;
	if(dataUploadEvent.data.length > 0)
	{
		options.series.push(evalStringForFlags(dataUploadEvent));
	}

	//get hidden series to make Y-axis fix
	var hiddenSeries = chartDataJSON.hiddenSeries;
	options.series.push(evalString(hiddenSeries));
	
	return options;
	
}
//print flag detail to table
function printWcktFlags(Flags,tableId)
{
	var table = document.getElementById(tableId);
	var data = Flags.data;
	var rowCount = table.rows.length;
	for(var i=0;i<data.length;i++)
	{
		var obj = data[i];
		var row = table.insertRow(rowCount+i);
		var cell1 = row.insertCell(0);
		cell1.innerHTML = obj.title;
		var cell2 = row.insertCell(1);
        cell2.innerHTML =  obj.text;
	}

}

function evalString(jsonObj)
{
	var dataArry = jsonObj.data;
	for(var i=0; i<dataArry.length; i++)
	{
		var innerArray = dataArry[i];
		var str = innerArray[0];
		innerArray[0] = eval(str);
		dataArry[i] = innerArray;
	}

	jsonObj.data = dataArry;
	return jsonObj;
}

function evalStringForFlags(Flags)
{
	var dataArry = Flags.data;
	for(var i=0; i<dataArry.length; i++)
	{
		var obj = dataArry[i];
		var xValue = eval(obj.x);
		obj.x = xValue;
		dataArry[i] = obj;
	}
	Flags.data = dataArry;
	return Flags;
}

//send ajax request to get participant all data for chart in JSON format
function sendAjax(participantId,selectedDate)
{
	var chartObj;
	var xmlHttp= getAjaxGETRequest();//it return simpale xmlHttp object for ajax then we set its method either GET or POST
	xmlHttp.onreadystatechange=function()
	{
		if (xmlHttp.readyState==4 && xmlHttp.status==200)
		{
			chartObj = "("+xmlHttp.responseText+")";
	    }
	  };
	
	  xmlHttp.open("POST","getParticipantChartData.html",false);
	  xmlHttp.setRequestHeader("Content-type","application/x-www-form-urlencoded");
	  xmlHttp.send("pId="+participantId+"&date="+selectedDate);
	  return eval(chartObj);
}

////get call on Dhtmlx cell Expand and collapse
function onExpandOrCollapseChart()
{
	if(options)
	{
		var width = dhxLayout.cells("b").getWidth();
		document.getElementById("chartContainer").style.width = (width*0.9);//set chart width 90% of the cell b width
		options.chart.renderTo= "chartContainer";
		chart = new Highcharts.StockChart(options);
	}
}






