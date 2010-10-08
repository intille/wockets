using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils.Http;
using System.Collections;
using System.Collections.Specialized;
using Wockets;
using System.Net;
using System.IO;
using System.Threading;
using System.Collections.Generic;
using Wockets.Utils;
using System.Threading;
using System.Runtime.InteropServices;
using Wockets.Kernel;

namespace DataUploader
{
    class Program
    {
        private static Thread stayUpThread;
        private static Thread postThread;

        [DllImport("CoreDll.dll")]
        public static extern void SystemIdleTimerReset();
        private static void StayUp()
        {
            while (true)
            {
                if (DateTime.Now.Subtract(startTime).TotalSeconds > 120)
                {
                    startTime = DateTime.Now.AddDays(2);
                    if (FileUploader.webrequest!=null)
                        FileUploader.webrequest.Abort();                    
                }
                SystemIdleTimerReset();
                Thread.Sleep(1000);
            }
        }

        static DateTime startTime;
        static void Main(string[] args)
        {
            DateTime startTime=DateTime.Now;
            Core.WRITE_LAST_UPLOAD_TIME(startTime);
            stayUpThread = new Thread(new ThreadStart(StayUp));
            stayUpThread.Start();

            CurrentPhone._Number="";
            CurrentSubject._ID = 1;
            Dictionary<string, DateTime> files = FileUploader.Scan(DateTime.Now.Subtract(new TimeSpan(2, 0, 0, 0)), DateTime.Now.Subtract(new TimeSpan(0, 0, 0, 0)));            
            //Sort files by creation time 
            var sortedFiles = from k in FileUploader._NotUploaded.Keys
                              orderby FileUploader._NotUploaded[k] ascending
                        select k;


            Core.WRITE_LAST_UPLOAD_NEWFILES(files.Count);
            FileUploader._Uri = "http://wockets.media.mit.edu/FileUpload.php";
            int success = 0;
            int failure = 0;
            foreach (string filename in sortedFiles)
            {
                DateTime creationTime = FileUploader._NotUploaded[filename];
                try
                {
                    
                    int start = filename.IndexOf("\\Wockets\\") + 9;
                    int length = filename.LastIndexOf("\\") - start;
                    string relative_path = "";
                    if (length > 0)
                        relative_path = filename.Substring(start, length);
                    NameValueCollection postData = new NameValueCollection();
                    relative_path = relative_path.Replace("\\", "/");
                    relative_path = "IMEI-" + CurrentPhone._IMEI + "/" + relative_path;
                    postData.Add("relative_path", relative_path.Replace("\\", "/"));
                    postData.Add("imei", CurrentPhone._IMEI);
                    postData.Add("sender_date", DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"));
                    postData.Add("KT_Insert1", "Insert");

                    startTime = DateTime.Now;
                    WebResponse response = FileUploader.Post(new Uri(FileUploader._Uri), postData, filename,
                           "application/octet-stream", "filename", null);
                    StreamReader reader = new StreamReader(response.GetResponseStream());
                    string str = reader.ReadLine();
                    string md5 = "";
                    while (str != null)
                    {
                        str = reader.ReadLine();
                        md5 += str;
                    }
                    response.Close();

                    if (md5.Length > 0)
                    {
                        int md5start = md5.IndexOf("<filemd5>") + 9;
                        int md5end = md5.IndexOf("</filemd5>");
                        md5 = md5.Substring(md5start, md5end - md5start);
                    }
                    string localmd5 = Hash.GetMD5HashFromFile(filename);

                    if (md5 == localmd5)
                    {
                        success++;
                        if (!FileUploader._Success.ContainsKey(filename))
                            FileUploader._Success.Add(filename, creationTime);
                        Core.WRITE_LAST_UPLOAD_SUCCESSFILES(success);
                    }
                    else if (!FileUploader._Failure.ContainsKey(filename))
                    {
                        failure++;
                        FileUploader._Failure.Add(filename, creationTime);
                        Core.WRITE_LAST_UPLOAD_FAILEDFILES(failure);
                    }

                    Thread.Sleep(5000);

                }
                catch (Exception e)
                {
                    failure++;
                    if (!FileUploader._Failure.ContainsKey(filename))
                        FileUploader._Failure.Add(filename, creationTime);
                    Core.WRITE_LAST_UPLOAD_FAILEDFILES(failure);
                }

                FileUploader.Save();          
            }
            Core.WRITE_LAST_UPLOAD_DURATION(DateTime.Now.Subtract(startTime));
            FileUploader.Save();          
           
    
            
            stayUpThread.Abort();
            System.Diagnostics.Process.GetCurrentProcess().Kill();
        }
    }
}
