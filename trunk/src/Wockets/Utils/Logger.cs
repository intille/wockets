using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace Wockets.Utils
{
    public static class Logger
    {
        private static String errorPath;
        private static String warnPath;
        private static String debugPath;     
        private static object wLock = new Object();
        private static object dLock = new Object();
        private static object eLock = new Object();
        private static object d2Lock = new Object();
        private static string _FilePath = "";

        public static void InitLogger(String filePath)
        {
            try
            {
                _FilePath = filePath;
                Directory.CreateDirectory(filePath);
            }
            catch
            {
            }
        }

        public static void Warn(String msg)
        {
            try
            {
                lock (wLock)
                {
                    DateTime now = DateTime.Now;
                    string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                    if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                        Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                    TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\warn.csv",true);
                    tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                    tw.Flush();
                    tw.Close();
                }
            }
            catch
            {
            }
        }
      
        public static void Debug(String msg)
        {
            try
            {
                DateTime now = DateTime.Now;
                string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                    Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\debug.csv",true);
                tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
        }

        public static void Error(String msg)
        {
            try
            {
                DateTime now = DateTime.Now;
                string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                    Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\error.csv",true);
                tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
        }


        public static void Log(String msg)
        {
            try
            {
                DateTime now = DateTime.Now;
                string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                    Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\log.csv", true);
                tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
        }

    }
}
