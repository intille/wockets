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

namespace DataUploader
{
    class Program
    {
        static void Main(string[] args)
        {

            CurrentPhone._Number="";
            CurrentSubject._ID = 1;
            FileUploader.Load();
            Dictionary<string,DateTime> files = FileUploader.Scan(DateTime.Now.Subtract(new TimeSpan(1000,0,0,0)));            
            //Sort files by creation time 
            var sortedFiles = from k in FileUploader._NotUploaded.Keys
                              orderby FileUploader._NotUploaded[k] ascending
                        select k;


           
            FileUploader._Uri = "http://18.85.54.236/FileUpload.php";


            foreach (string filename in sortedFiles)
            {
                DateTime creationTime = FileUploader._NotUploaded[filename];                
                int start = filename.IndexOf("\\Wockets\\") + 9;
                int length = filename.LastIndexOf("\\") - start;
                string relative_path = "";
                if (length > 0)
                    relative_path = filename.Substring(start, length);
                NameValueCollection postData = new NameValueCollection();
                relative_path = relative_path.Replace("\\", "/");
                relative_path = "Subject" + CurrentSubject._ID.ToString("000") + "/" + relative_path;
                postData.Add("relative_path", relative_path.Replace("\\", "/"));
                postData.Add("imei", CurrentPhone._IMEI);
                postData.Add("sender_date", DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"));
                postData.Add("KT_Insert1", "Insert");

                try
                {

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
                        FileUploader._Success.Add(filename, creationTime);
                        //FileUploader._Uploaded.Add(filename, creationTime);
                        
                    }
                    else
                        FileUploader._Failure.Add(filename, creationTime);
                        //FileUploader._NotUploaded.Add(filename, creationTime);

                    Thread.Sleep(5000);

                }
                catch (Exception e)
                {
                }
                //Check if the md5 is good, file uploaded correctly

            }

            //Exit
            FileUploader.Save();
        }
    }
}
