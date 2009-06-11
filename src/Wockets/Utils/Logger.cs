using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace Wockets.Utils
{
    public class Logger
    {
        private String errorPath;
        private String warnPath;
        private String debugPath;

        public Logger(String filePath)
        {
            Directory.CreateDirectory(filePath+"\\data\\log");
            this.errorPath = filePath + "\\data\\log\\error.txt";
            this.warnPath = filePath + "\\data\\log\\warn.txt";
            this.debugPath = filePath + "\\data\\log\\debug.txt";
            FileStream a = new FileStream(this.errorPath, FileMode.Create);
            a.Close();
            a = new FileStream(this.warnPath, FileMode.Create);
            a.Close();
            a = new FileStream(this.debugPath, FileMode.Create);
            a.Close();
        }

        public void Warn(String msg)
        {

            StreamWriter writer = new StreamWriter(new FileStream(this.warnPath, FileMode.Append));
            writer.WriteLine(DateTime.Now + " WARNING: " + msg);
            writer.Flush();
            writer.Close();
        }

        public void Debug(String msg)
        {

            StreamWriter writer = new StreamWriter(new FileStream(this.debugPath, FileMode.Append));
            writer.WriteLine(DateTime.Now + " DEBUG: " + msg);
            writer.Flush();
            writer.Close();
        }

        public void Error(Exception ex)
        {
            StreamWriter writer = new StreamWriter(new FileStream(this.errorPath, FileMode.Append));
            writer.WriteLine(DateTime.Now + " Error:");
            writer.WriteLine(ex.Message.Trim());
            writer.WriteLine("Stack Trace    : " + ex.StackTrace.Trim());
            writer.WriteLine("^^-------------------------------------------------------------------^^");
            writer.Flush();
            writer.Close();

        }
    }
}
