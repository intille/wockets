using System;
using System.IO;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesLogger.
	/// </summary>
	public class MITesActivityLogger
	{
		private FileWriter fw; 
		private String logData;
		private static String DEFAULT_LOG_FILE = "\\My Documents\\data\\MITesActivityLogFile";
		private int lastTickTime;
		private DateTime lastDateTime; 
		private string resultLine;
		private string keyLine; 
		private int lastWriteTime; 

		/// <summary>
		/// String saved to logfile when there is no data to report
		/// </summary>
		public static readonly string NONE_STRING = "";

//		private int lastEpochTime = 0;  
//		double[,] activityResults;
		
		/// <summary>
		/// Ceate an object that will save activity count and HR data that is computed by a MITesActivityCounter and a MITesHRAnalyzer. 
		/// </summary>
		public MITesActivityLogger()
		{
			SetupFiles(DEFAULT_LOG_FILE);
		}

		/// <summary>
		/// Ceate an object that will save activity count and HR data that is computed by a MITesActivityCounter and a MITesHRAnalyzer. 
		/// </summary>
		public MITesActivityLogger(string aFileName)
		{
			SetupFiles(aFileName);
		}

		/// <summary>
		/// Create the directories where data files wil be saved. 
		/// </summary>
		/// <param name="aFilePath"></param>
		public void SetupDirectories(string aFilePath)
		{
			if (!Directory.Exists (aFilePath + "\\data"))
				Directory.CreateDirectory (aFilePath + "\\data");

			if (!Directory.Exists (aFilePath + "\\data\\ims"))
				Directory.CreateDirectory (aFilePath + "\\data\\ims");

			if (!Directory.Exists (aFilePath + "\\data\\actigraph"))
				Directory.CreateDirectory (aFilePath + "\\data\\actigraph");

			if (!Directory.Exists (aFilePath + "\\data\\activity"))
				Directory.CreateDirectory (aFilePath + "\\data\\activity");

			if (!Directory.Exists (aFilePath + "\\data\\log"))
				Directory.CreateDirectory (aFilePath + "\\data\\log");

			if (!Directory.Exists (aFilePath + "\\data\\raw"))
				Directory.CreateDirectory (aFilePath + "\\data\\raw");
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetFileName()
		{
			return logData;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetLastTickTime()
		{
			return lastTickTime;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public DateTime GetLastDateTime()
		{
			return lastDateTime;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public string GetReportKey(string aLabel)
		{
			string s = "," + aLabel;
			return s;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public string GetReport(string aValue)
		{
			string s = "," + aValue;
			return s;
		}

		private void SetupFiles(String logFileName)
		{
			DateTime dt = DateTime.Now;
			int tc = Environment.TickCount; 
			logData = logFileName  + "." + dt.Year + "-" + dt.Month + "-" + dt.Day + "-" + dt.Hour + "-" + dt.Minute + "-" + dt.Second + "-" + dt.Millisecond + ".csv";
			
			fw = new FileWriter(logData,false);
		}	

//		private int saveCounter = 0; 

		/// <summary>
		/// 
		/// </summary>
		public void StartReportLine()
		{
			resultLine = "";
		    lastTickTime = Environment.TickCount;
			lastDateTime = DateTime.Now; 
		}
		
		/// <summary>
		/// 
		/// </summary>
		public void StartReportKeyLine()
		{
			keyLine = "";
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesHRAnalyzer"></param>
		public void AddKeyLine(MITesHRAnalyzer aMITesHRAnalyzer)
		{
			keyLine += aMITesHRAnalyzer.GetReportKey();
		}

		// / <summary>
		// / 
		// / </summary>
		// / <param name="aMITesStepsAnalyzer"></param>
        //public void AddKeyLine(MITesStepsAnalyzerNew aMITesStepsAnalyzer)
        //{
        //    keyLine += aMITesStepsAnalyzer.GetReportKey();
        //}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesHRAnalyzer"></param>
		public void AddReportLine(MITesHRAnalyzer aMITesHRAnalyzer)
		{
			resultLine += aMITesHRAnalyzer.GetReport();
		}

		// / <summary>
		// / 
		// /  </summary>
		// / <param name="aMITesStepsAnalyzer"></param>
        //public void AddReportLine(MITesStepsAnalyzerNew aMITesStepsAnalyzer)
        //{
        //    resultLine += aMITesStepsAnalyzer.GetReport();
        //}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aLabel"></param>
		public void AddKeyLine(string aLabel)
		{
			keyLine += "" + GetReportKey(aLabel);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aLabel"></param>
		public void AddReportLine(string aLabel)
		{
			resultLine += "" + GetReport(aLabel);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesRangeAnalyzer"></param>
		public void AddKeyLine(MITesRangeAnalyzer aMITesRangeAnalyzer)
		{
			keyLine += aMITesRangeAnalyzer.GetReportKey();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesRangeAnalyzer"></param>
		public void AddReportLine(MITesRangeAnalyzer aMITesRangeAnalyzer)
		{
			resultLine += aMITesRangeAnalyzer.GetReport();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesLightAnalyzer"></param>
		public void AddKeyLine(MITesLightAnalyzer aMITesLightAnalyzer)
		{
			keyLine += aMITesLightAnalyzer.GetReportKey();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesLightAnalyzer"></param>
		public void AddReportLine(MITesLightAnalyzer aMITesLightAnalyzer)
		{
			resultLine += aMITesLightAnalyzer.GetReport();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesCurrentAnalyzer"></param>
		public void AddKeyLine(MITesCurrentAnalyzer aMITesCurrentAnalyzer)
		{
			keyLine += aMITesCurrentAnalyzer.GetReportKey();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesCurrentAnalyzer"></param>
		public void AddReportLine(MITesCurrentAnalyzer aMITesCurrentAnalyzer)
		{
			resultLine += aMITesCurrentAnalyzer.GetReport();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesTempAnalyzer"></param>
		public void AddKeyLine(MITesTempAnalyzer aMITesTempAnalyzer)
		{
			keyLine += aMITesTempAnalyzer.GetReportKey();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesTempAnalyzer"></param>
		public void AddReportLine(MITesTempAnalyzer aMITesTempAnalyzer)
		{
			resultLine += aMITesTempAnalyzer.GetReport();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesObjectAnalyzer"></param>
		public void AddKeyLine(MITesObjectAnalyzer aMITesObjectAnalyzer)
		{
			keyLine += aMITesObjectAnalyzer.GetReportKey();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesObjectAnalyzer"></param>
		public void AddReportLine(MITesObjectAnalyzer aMITesObjectAnalyzer)
		{
			resultLine += aMITesObjectAnalyzer.GetReport();
		}
		
		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesActivityCounter"></param>
		public void AddKeyLine(MITesActivityCounter aMITesActivityCounter)
		{
			keyLine += aMITesActivityCounter.GetReportKey();
		}
	
		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesActivityCounter"></param>
		public void AddReportLine(MITesActivityCounter aMITesActivityCounter)
		{
			resultLine += aMITesActivityCounter.GetReport();
		}

		/// <summary>
		/// 
		/// </summary>
		public void SaveReportLine()
		{		
			WriteLogData(resultLine);

//			if (saveCounter == 0)
//			{
//				WriteTickCountCorrespondence();
//				WriteSensorStatus();	
//			}
//			saveCounter++;
//			if (saveCounter > 50)
//				saveCounter = 0;
		}

		/// <summary>
		/// 
		/// </summary>
		public void SaveReportKeyLine()
		{	
			Console.WriteLine (keyLine);
			WriteLogKey(keyLine);
		}
	
		/// <summary>
		/// 
		/// </summary>
        //public void WriteSensorStatus(MITesSensorCalibrator aMITesSensorCalibrator)
        //{
        //    String str = aMITesSensorCalibrator.GetStatusLine();
        //    WriteLogComment(str);
        //}

		/// <summary>
		/// Get the last time that any type of data was written
		/// </summary>
		/// <returns>A time in millseconds</returns>
		public int GetLastWriteTime()
		{
			return lastWriteTime;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		public void WriteLogData(String str)
		{
			WriteLogData(str, Environment.TickCount);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		/// <param name="aTimeMS"></param>
		public void WriteLogData(String str, int aTimeMS)
		{
			lastWriteTime = aTimeMS; 
			fw.OpenFile(false);
			fw.WriteLine(aTimeMS + "," + DateTime.Now + "," + DateTime.Now.Millisecond + ",DATA," + str);
			fw.CloseFile();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		public void WriteLogComment(String str)
		{
			WriteLogComment(str, Environment.TickCount);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		/// <param name="aTimeMS"></param>
		public void WriteLogComment(String str, int aTimeMS)
		{
			lastWriteTime = aTimeMS; 
			fw.OpenFile(false);
			fw.WriteLine(aTimeMS + "," + DateTime.Now + "," + DateTime.Now.Millisecond + ",COMMENT," + str);
			fw.CloseFile();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		public void WriteLogKey(String str)
		{
			fw.OpenFile(false);
			fw.WriteLine(Environment.TickCount + "," + DateTime.Now + "," + DateTime.Now.Millisecond + ",KEY," + str);
			fw.CloseFile();
		}

	
		private void WriteTickCountCorrespondence()
		{
			DateTime dt = DateTime.Now;
			WriteLogComment("TICKCOUNT, TickCount correspondence " + " " + dt.Year + " " + dt.Month + " " + dt.Day + " " + dt.Hour + " " + dt.Minute + " " + dt.Second + " " + dt.Millisecond);
		}


		private void WriteFrameRate(int rate)
		{
			DateTime dt = DateTime.Now;
			WriteLogComment("FRAMERATE," + rate);
		}
	}
}