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
using Wockets.Utils.IPC;

namespace DataUploader
{
    class Program
    {
        private static Thread stayUpThread;
        private static Thread postThread;
        private static Thread terminateThread;

        [DllImport("CoreDll.dll")]
        public static extern void SystemIdleTimerReset();
        private static int respawns = 0;



        private static void StayUp()
        {
            while (true)
            {
                if (DateTime.Now.Subtract(startTime).TotalSeconds > 180)
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                else if (DateTime.Now.Subtract(startTime).TotalSeconds > 120)
                {
                    startTime = DateTime.Now.AddDays(2);
                }
               
                SystemIdleTimerReset();
                Thread.Sleep(1000);
            }
        }



        private static void TerminateHandler()
        {
            try
            {

                NamedEvents namedEvent = new NamedEvents();
                namedEvent.Receive("TerminateUploader");
                namedEvent.Reset();                              
                try
                {
                    if (FileUploader.rstream != null)
                    {
                        FileUploader.rstream.Close();
                        FileUploader.rstream = null;
                    }
                }
                catch { }

                notdone = false;
                Thread.Sleep(1000);
                System.Diagnostics.Process.GetCurrentProcess().Close();
                System.Diagnostics.Process.GetCurrentProcess().Kill();

            }
            catch
            {
                System.Diagnostics.Process.GetCurrentProcess().Close();
                System.Diagnostics.Process.GetCurrentProcess().Kill();
            }

        }


        static DateTime startTime;
        //static WebResponse response;
        static void PostThread()
        {
            Core.WRITE_LAST_UPLOAD_NEWFILES(0);
            Core.WRITE_LAST_UPLOAD_SUCCESSFILES(0);
            Core.WRITE_LAST_UPLOAD_FAILEDFILES(0);
            DateTime startTime = DateTime.Now;
            Core.WRITE_LAST_UPLOAD_TIME(startTime);
            stayUpThread = new Thread(new ThreadStart(StayUp));
            stayUpThread.Start();

            CurrentPhone._Number = "";
            CurrentSubject._ID = 1;
            Dictionary<string, DateTime> files = FileUploader.Scan(DateTime.Now.Subtract(new TimeSpan(20, 0, 0, 0)), DateTime.Now.Subtract(new TimeSpan(0, 0, 0, 0)));
            //Sort files by creation time 
            var sortedFiles = from k in FileUploader._NotUploaded.Keys
                              orderby FileUploader._NotUploaded[k] descending
                              select k;


            Core.WRITE_LAST_UPLOAD_NEWFILES(files.Count);
            FileUploader._Uri = "http://wockets.media.mit.edu/FileUpload.php";
            String getUri = "http://wockets.media.mit.edu/CheckFile.php";
            int success = 0;
            int failure = 0;
            //foreach (string filename in sortedFiles)
            foreach (KeyValuePair<String, DateTime> entry in FileUploader._NotUploaded)
            {
                string filename = entry.Key;
                DateTime creationTime = FileUploader._NotUploaded[filename];
                try
                {

                    int start = filename.IndexOf("\\Wockets\\") + 9;
                    int length = filename.LastIndexOf("\\") - start;                   
                    string relative_path = "";
                    if (length > 0)
                        relative_path = filename.Substring(start, length);
                    NameValueCollection postData = new NameValueCollection();
                    NameValueCollection getData = new NameValueCollection();
                    relative_path = relative_path.Replace("\\", "/");



                    //Check file on server
                    //relative_path = "IMEI-" + CurrentPhone._IMEI + "/" + relative_path;
                    getData.Add("relative_path", relative_path);
                    getData.Add("filename", filename.Substring(filename.LastIndexOf("\\") + 1));
                    getData.Add("imei", CurrentPhone._IMEI);

                    startTime = DateTime.Now;
                    string checkresponse = ""; 
                    string md5 = "";
                    string localmd5 = Hash.GetMD5HashFromFile(filename);
                    using (WebResponse response = FileUploader.Get(new Uri(getUri), getData))
                    {

                        StreamReader reader = null;
                        try
                        {
                            reader = new StreamReader(response.GetResponseStream());
                            string str = reader.ReadLine();
                            if (str!=null)
                                checkresponse += str;
                            while (str != null)
                            {
                                str = reader.ReadLine();
                                if (str!=null)
                                checkresponse += str;
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Debug("PostThread: exception 1:" + e.Message);
                        }
                        finally
                        {
                            if (reader != null) reader.Close();
                            if (response != null) response.Close();
                        }
                    }

                    if ((checkresponse!=null) && (checkresponse.Length > 0) && (checkresponse != "false"))
                    {
                        string[] tokens = checkresponse.Split(new char[] { ',' });
                        if ((tokens != null) && (tokens.Length == 4))
                        {
                            DateTime serverTime = DateTime.Parse(tokens[2]);
                            DateTime senderTime = DateTime.Parse(tokens[3]);
                            if ((tokens[0] == "true") && (localmd5 == tokens[1]))
                            {
                                if ((DateTime.Now.Subtract(serverTime).TotalDays >= 1) &&
                                    (DateTime.Now.Subtract(senderTime).TotalDays >= 1))
                                {
                                    try
                                    {
                                        File.Delete(filename);
                                    }
                                    catch
                                    {
                                    }
                                }
                                success++;
                                Core.WRITE_LAST_UPLOAD_SUCCESSFILES(success);
                                continue;
                            }
                        }
                    }

                    //relative_path = "IMEI-" + CurrentPhone._IMEI + "/" + relative_path;
                    postData.Add("relative_path", relative_path);
                    postData.Add("root_path", "none");
                    postData.Add("imei", CurrentPhone._IMEI);
                    postData.Add("sender_date", DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"));
                    postData.Add("KT_Insert1", "Insert");

                    startTime = DateTime.Now;
                    //string md5 = "";
                    //string localmd5 = Hash.GetMD5HashFromFile(filename);
                    Logger.Debug("PostThread: about to upload"+filename);
                    using (WebResponse response = FileUploader.Post(new Uri(FileUploader._Uri), postData, filename, "application/octet-stream", "filename", null))
                    {
                       
                        StreamReader reader =null;
                        try
                        {
                            reader = new StreamReader(response.GetResponseStream());
                            string str = reader.ReadLine();
                            while (str != null)
                            {
                                str = reader.ReadLine();
                                md5 += str;
                            }                            
                        }
                        catch (Exception e)
                        {
                            Logger.Debug("PostThread: exception 1:" + e.Message);
                        }
                        finally
                        {
                            if (reader != null) reader.Close();
                            if (response != null) response.Close();                                                       
                        }
                    }


                    if (md5.Length > 0)
                    {
                        int md5start = md5.IndexOf("<filemd5>") + 9;
                        int md5end = md5.IndexOf("</filemd5>");
                        md5 = md5.Substring(md5start, md5end - md5start);
                    }
                  
                    if (md5 == localmd5)
                    {
                        Logger.Debug("PostThread: MD5 Match:" + md5);
                        success++;
                        //if (!FileUploader._Success.ContainsKey(filename))
                        //    FileUploader._Success.Add(filename, creationTime);
                        Core.WRITE_LAST_UPLOAD_SUCCESSFILES(success);
                    }
                    else if (!FileUploader._Failure.ContainsKey(filename))
                    {
                        Logger.Debug("PostThread: MD5 Mismatch:" + md5+","+localmd5);
                        failure++;
                        //if (!FileUploader._Failure.ContainsKey(filename))
                        //    FileUploader._Failure.Add(filename, creationTime);
                        Core.WRITE_LAST_UPLOAD_FAILEDFILES(failure);
                    }

                    Thread.Sleep(5000);
                    SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                    if (bpower.BatteryCurrent < 0)
                        break;

                }
                catch (Exception e)
                {
                    Logger.Debug("PostThread: exception 2:" + e.Message);
                    failure++;
                    //if (!FileUploader._Failure.ContainsKey(filename))
                    //    FileUploader._Failure.Add(filename, creationTime);
                    Core.WRITE_LAST_UPLOAD_FAILEDFILES(failure);
                }               

                //FileUploader.Save();
            }
            Core.WRITE_LAST_UPLOAD_DURATION(DateTime.Now.Subtract(startTime));
            //FileUploader.Save();
            notdone = false;

        }


        static bool notdone = true;


        static void Main(string[] args)
        {

            #region Identify the Storage Card

            string firstCard = "";
            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();


            //iterate through them
            for (int x = 0; x < fsi.Length; x++)
            {
                //check to see if this is a temporary storage card (e.g. SD card)
                if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                {
                    firstCard = fsi[x].FullName;
                    try
                    {
                        Directory.CreateDirectory(firstCard + "\\writable");
                        Directory.Delete(firstCard + "\\writable");
                    }
                    catch (Exception)
                    {
                        firstCard = "";
                        continue;
                    }
                    //if so, return the path

                    break;
                }
            }

            #endregion



            Logger.InitLogger( firstCard + "\\uploadlog");
            Logger.Debug("Starting Uploader");
            startTime = DateTime.Now;
            postThread = new Thread(new ThreadStart(PostThread));
            postThread.Start();
            terminateThread = new Thread(new ThreadStart(TerminateHandler));
            terminateThread.Start();
            //terminateThread.Join();
            while (notdone) Thread.Sleep(1000);

            Logger.Debug("Main:");
            try
            {
                stayUpThread.Abort();
            }
            catch 
            { 

            }

            System.Diagnostics.Process.GetCurrentProcess().Kill();
        }
    
    
    }
}
