using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace Wockets.Utils
{
    public class LocalLogger
    {
        //private String errorPath;
        //private String warnPath;
        //private String debugPath;
        //private object wLock = new Object();
        //private object dLock = new Object();
        //private object eLock = new Object();
        //private object d2Lock = new Object();

        private string _FilePath = "";
        private string _FilePrefix = "";


        public LocalLogger(String filePath, String filePrefix)
        {
            try
            {
                _FilePath = filePath;
                if (!Directory.Exists(_FilePath))
                    Directory.CreateDirectory(filePath);
                _FilePrefix = filePrefix;

            }
            catch
            {
            }
        }


        public void InitLogger(String filePath, String filePrefix)
        {
            try
            {
                _FilePath = filePath;
                if (!Directory.Exists(_FilePath))
                    Directory.CreateDirectory(filePath);
                _FilePrefix = filePrefix;

            }
            catch
            {
            }
        }



        public void Warn(String msg)
        {
            try
            {
                //lock (wLock)
                //{
                    DateTime now = DateTime.Now;
                    string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                    if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                        Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                    TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\" + _FilePrefix + "warn.csv", true);
                    tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                    tw.Flush();
                    tw.Close();
                //}
            }
            catch
            {
            }
        }

        public void Debug(String msg)
        {
            try
            {
                DateTime now = DateTime.Now;
                string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                    Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\" + _FilePrefix + "debug.csv", true);
                tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
        }

        public void Error(String msg)
        {
            try
            {
                DateTime now = DateTime.Now;
                string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                    Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\" + _FilePrefix + "error.csv", true);
                tw.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                tw.Flush();
                tw.Close();
            }
            catch
            {
            }
        }


        public void Log(String msg)
        {
            try
            {
                DateTime now = DateTime.Now;
                string hourlyPath = now.ToString("yyyy-MM-dd") + "\\" + now.Hour;
                if (!Directory.Exists(_FilePath + "\\" + hourlyPath))
                    Directory.CreateDirectory(_FilePath + "\\" + hourlyPath);
                TextWriter tw = new StreamWriter(_FilePath + "\\" + hourlyPath + "\\" + _FilePrefix + "log.csv", true);
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
