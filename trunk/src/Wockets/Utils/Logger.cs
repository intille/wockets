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
        private static String debug2Path;
        private static StreamWriter e;
        private static StreamWriter w;
        private static StreamWriter d;
        private static StreamWriter d2;
        private static object wLock = new Object();
        private static object dLock = new Object();
        private static object eLock = new Object();
        private static object d2Lock = new Object();
        private static bool initialized = false;

        public static void InitLogger(String filePath)
        {
            Directory.CreateDirectory(filePath);
            errorPath = filePath + "error.txt";
            warnPath = filePath + "warn.txt";
            debugPath = filePath + "debug.csv";
            debug2Path = filePath + "debug2.csv";
            e = new StreamWriter(new FileStream(errorPath, FileMode.Create));
            w = new StreamWriter(new FileStream(warnPath, FileMode.Create));
            d = new StreamWriter(new FileStream(debugPath, FileMode.Create));
            d2 = new StreamWriter(new FileStream(debug2Path, FileMode.Create));
            initialized = true;
        }

        public static void Warn(String msg)
        {
            if (!initialized)
                InitLogger(".\\");
            lock (wLock)
            {
                w.WriteLine("WARNING: "+WocketsTimer.GetUnixTime()+ ","+DateTime.Now+","+ msg);
                w.Flush();
            }
        }


        public static void Debug2(String msg)
        {
            if (!initialized)
                InitLogger(".\\");
            lock (d2Lock)
            {
                d2.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                d2.Flush();
            }
        }


        public static void Debug(String msg)
        {
            if (!initialized)
                InitLogger(".\\");
            lock (dLock)
            {
                d.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);                
                d.Flush();
            }
        }

        public static void Error(String msg)
        {
            if (!initialized)
                InitLogger(".\\");
            lock (eLock)
            {
                e.WriteLine(WocketsTimer.GetUnixTime() + "," + DateTime.Now + "," + msg);
                e.Flush();
            }
        }

        public static void Close()
        {
            w.Close();
            d.Close();
            e.Close();
            d2.Close();
        }
    }
}
