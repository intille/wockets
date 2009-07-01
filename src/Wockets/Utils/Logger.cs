using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace Wockets.Utils
{
    public class Logger
    {
        private static String errorPath;
        private static String warnPath;
        private static String debugPath;

        public static void InitLogger(String filePath)
        {
            Directory.CreateDirectory(filePath+"\\data\\log");
            errorPath = filePath + "\\data\\log\\error.txt";
            warnPath = filePath + "\\data\\log\\warn.txt";
            debugPath = filePath + "\\data\\log\\debug.txt";
            FileStream a = new FileStream(errorPath, FileMode.Create);
            a.Close();
            a = new FileStream(warnPath, FileMode.Create);
            a.Close();
            a = new FileStream(debugPath, FileMode.Create);
            a.Close();
        }

        public static void Warn(String msg)
        {

            StreamWriter writer = new StreamWriter(new FileStream(warnPath, FileMode.Append));
            writer.WriteLine(DateTime.Now + " WARNING: " + msg);
            writer.Flush();
            writer.Close();
        }

        public static void Debug(String msg)
        {

            StreamWriter writer = new StreamWriter(new FileStream(debugPath, FileMode.Append));
            writer.WriteLine(DateTime.Now + " DEBUG: " + msg);
            writer.Flush();
            writer.Close();
        }

        public static void Error(Exception ex)
        {
            StreamWriter writer = new StreamWriter(new FileStream(errorPath, FileMode.Append));
            writer.WriteLine(DateTime.Now + " Error:");
            writer.WriteLine(ex.Message.Trim());
            writer.WriteLine("Stack Trace    : " + ex.StackTrace.Trim());
            writer.WriteLine("^^-------------------------------------------------------------------^^");
            writer.Flush();
            writer.Close();

        }
    }
}
