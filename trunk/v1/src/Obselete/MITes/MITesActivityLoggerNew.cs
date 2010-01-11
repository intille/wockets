using System;
using System.IO;
using System.Threading;
using HousenCS.IO;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityLoggerNew
	/// </summary>
	public class MITesActivityLoggerNew
	{
		private FileWriter fw; 

        //private int lastUnixTime;
		//private DateTime lastDateTime; 

        private string resultLine;
		private string keyLine; 
		//private int lastWriteTime; 

		/// <summary>
		/// String saved to logfile when there is no data to report
		/// </summary>
		public static readonly string NONE_STRING = "";

		/// <summary>
		/// Ceate an object that will save activity count and HR data that is computed by a MITesActivityCounter and a MITesHRAnalyzer. 
		/// </summary>
		public MITesActivityLoggerNew(string aFileName)
		{
			SetupFiles(aFileName);
		}

        ///// <summary>
        ///// 
        ///// </summary>
        ///// <returns></returns>
        //public int GetLastUnixTime()
        //{
        //    return lastUnixTime;
        //}

        ///// <summary>
        ///// 
        ///// </summary>
        ///// <returns></returns>
        //public DateTime GetLastDateTime()
        //{
        //    return lastDateTime;
        //}

		private void SetupFiles(String logFileName)
		{
            fw = new FileWriter(logFileName, false);
            fw.OpenFile(false);
		}	
		
//			resultLine += aMITesHRAnalyzer.GetReport();

        /// <summary>
        /// 
        /// </summary>
        public void ShutDown()
        {
            if (fw != null)
                fw.CloseFile();
        }

        /// <summary>
        /// 
        /// </summary>
        public void StartKeyLine()
        {
            keyLine = "UnixTime,DateTime"; 
        }

        /// <summary>
        /// 
        /// </summary>
        public void StartReportLine(double aUnixTime)
        {
            resultLine = "";
            DateTime dt = new DateTime();
            UnixTime.GetDateTime((long) aUnixTime, out dt);
            resultLine += aUnixTime + "," + dt; 
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
        /// <param name="aMITesActivityCounter"></param>
        /// <param name="currentTime"></param>
        public void AddReportLine(MITesActivityCounter aMITesActivityCounter, double currentTime)
        {
            resultLine += aMITesActivityCounter.GetReport(currentTime);
        }

        /// <summary>
        /// 
        /// </summary>
        public void AddEmptyReportLine()
        {
            resultLine += MITesActivityCounter.GetEmptyReport();
        }

		/// <summary>
		/// 
		/// </summary>
		public void SaveReportLine()
		{		
			WriteLogData(resultLine);
		}

		/// <summary>
		/// 
		/// </summary>
		public void SaveReportKeyLine()
		{	
			Console.WriteLine (keyLine);
			WriteLogKey(keyLine);
		}
	
        ///// <summary>
        ///// Get the last time that any type of data was written
        ///// </summary>
        ///// <returns>A time in millseconds</returns>
        //public int GetLastWriteTime()
        //{
        //    return lastWriteTime;
        //}

	    private int writeCount = 0; 
        /// <summary>
        /// 
        /// </summary>
        /// <param name="str"></param>
		public void WriteLogData(string str)
		{
//			lastWriteTime = aTimeMS; 
			fw.WriteLine(str);

            writeCount++; 
            if (writeCount == 1000)
            {
                fw.Flush();
                writeCount = 0; 
            }
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="str"></param>
		public void WriteLogKey(String str)
		{
            WriteLogData(str);
		}
	}
}