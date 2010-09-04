using System;

using System.Collections.Generic;
using System.Text;
using System.Threading;
using System.Net;
using System.IO;
using System.Security.Cryptography;
//using Wockets.Utils.sms;




namespace Wockets.Utils.HttpUploader
{

    public class FileUploader
    {


        #region Declare Variables

       
        //--- Upload Monitor ---
        private static Thread fileUploadMonitorThread;
        private const int sendFilePollingFreq = 30; // seconds
        private const int fileResendRetryTimes = 3;


        //Files to upload queue
        private static List<FileToSend> fileUploadQueue = new List<FileToSend>();
        private static List<FileToSend> fileFailedToUploadList = new List<FileToSend>();


        //--- URL To WebServer--------------
        private String uri = "";


        //--- Logs ---
        private const String fileUploadHistoryFileName = "flog.txt";
        private static StreamReader fileUploadHistoryReader;
        private static StreamWriter fileUploadHistoryWriter, logWriter;
        private static bool enableLogging = false;


        //Session variables
        
        private static String selectedDirectoryPath = "";
        private static String selectedSubDirectoryPath = "";

        private static int sessionSuccessfullyUploadedCount = 0;
        private static int sessionFailedUploadCount = 0;

        private static String sessionSubjectID = "";
        private static String applicationName = "";

        //--- Errors ---
        private static String lastErrorMessage;


        ////Event Handler and Delegate
        private static bool fileUploadSessionRunning = false;
        //public delegate void FileUploaderResponseHandler(object sender, MyEventArgs e);
        //public event FileUploaderResponseHandler FinishedUploadingEvent;
       

  #endregion


        #region  Start File Uploader Monitoring Thread

        public FileUploader(string url)
        {

            this.uri = url;

            //Initialize the file upload monitor
            fileUploadMonitorThread = new Thread(new ThreadStart(fileUploadMonitor));
            fileUploadMonitorThread.Start();

        }


        

        public static void fileUploadMonitor()
        {


            #region commented
            // while(true)
            //{
            #endregion 



            //check the sharing of this variable
                while (fileUploadQueue.Count > 0)
                {
                    
                    //Get the file from the Queue & try to send it
                    FileToSend fileToSend = fileUploadQueue[0];
                    String sendFileResult = fileToSend.sendFile();


                    if (sendFileResult == "success")
                    {

                        #region if success


                        if (enableLogging)
                        {
                            logWriter.WriteLine(DateTime.Now + "," + fileToSend.getFilePath() + " successfully uploaded.");
                            logWriter.Flush();
                        }

                        sessionSuccessfullyUploadedCount++;

                        //record uploaded file
                        FileInfo finfo = new FileInfo(fileToSend.getFilePath());
                        fileUploadHistoryWriter = new StreamWriter(finfo.Directory.FullName + "/" + fileUploadHistoryFileName, true);
                        fileUploadHistoryWriter.WriteLine(finfo.FullName + "," + finfo.LastWriteTime.ToString());
                        fileUploadHistoryWriter.Flush();
                        fileUploadHistoryWriter.Close();

                        sessionSubjectID = fileToSend.getSubjectId();
                        applicationName = fileToSend.applicationName;
                        fileUploadQueue.RemoveAt(0);


                        #endregion


                    }
                    else
                    {

                        #region if error

                        lastErrorMessage = DateTime.Now + "," + fileToSend.getFilePath() + " " + sendFileResult;

                        if (enableLogging)
                        {
                            logWriter.WriteLine(lastErrorMessage);
                            logWriter.Flush();
                        }

                        if (fileToSend.failedCount >= fileResendRetryTimes)
                        {
                            
                            // fileFailedToUploadList.Add(fileToSend);
                            // put a log on failed to send messages.
                            if (enableLogging)
                            {
                                logWriter.WriteLine(DateTime.Now + "," + fileToSend.getFilePath() + " failed to send too many times. Giving up retrying.");
                                logWriter.Flush();
                            }

                            sessionFailedUploadCount++;

                            fileUploadQueue.RemoveAt(0);

                        }
                        else
                        {
                            fileToSend.failedCount++;

                            // retry a little later every time
                            // Sleep before trying again
                            //Thread.Sleep(sendFilePollingFreq * fileToSend.failedCount * 1000);
                        }


                        #endregion

                    }
                }



                #region update the session parameters & logs

                if (fileUploadSessionRunning)
                {
                    if (enableLogging)
                    {
                        logWriter.WriteLine(DateTime.Now + ", File upload session finished. Successfully uploaded files count: " + sessionSuccessfullyUploadedCount + ", Failed to upload file count: " + sessionFailedUploadCount);
                        logWriter.Flush();
                    }


                    sessionSuccessfullyUploadedCount = 0;
                    sessionFailedUploadCount = 0;
                    fileUploadSessionRunning = false;

                }

                #endregion

            

            #region commented
            //this is for repeating the operation later/
                //Thread.Sleep(sendFilePollingFreq * 1000);
            //}
            #endregion 


           
        }




        #endregion



        #region Logging Functions
        public static void enableLogger(StreamWriter logWriter)
        {
            FileUploader.logWriter = logWriter;

            if(logWriter != null)
                FileUploader.enableLogging = true;
        }

        public static String getLastErrorMessage(){
            return lastErrorMessage;
        }

        #endregion 



        #region Add File to the Queue
        // upload files
        public static void uploadFile(String postFileURL, String pathToFile, String nameFile, String applicationName, String subjectId, String dataType, String subDirectoryPath, String notes)
        {
            //FileToSend fileToSend = new FileToSend(postFileURL, pathToFile, projectName, subjectId, dataType, subDirectoryPath, notes);
            FileToSend fileToSend = new FileToSend(postFileURL, pathToFile, applicationName, subjectId, dataType, subDirectoryPath, notes);
            fileUploadQueue.Add(fileToSend);
        }

        #endregion 




        #region Scan Files & Directories Functions


        // recursively uploading files in a directory
        public static bool uploadAllFilesInDirectory(String postFileURL, String directoryPath, String projectName, String subjectId, String dataType, String subDirectoryPath, String[] excludeDirectoryPaths, String notes)
        {
            

            selectedDirectoryPath = directoryPath;
            selectedSubDirectoryPath = subDirectoryPath;


            if (Directory.Exists(selectedDirectoryPath))
            {
                //int fileCounter = 0;
                //fileCounter = countFilesInDirectory(selectedDirectoryPath, excludeDirectoryPaths, fileCounter);

                if (!fileUploadSessionRunning)
                {
                    fileUploadSessionRunning = true;
                }

                scanFilesAndUpload(postFileURL, selectedDirectoryPath, projectName, subjectId, dataType, selectedSubDirectoryPath, excludeDirectoryPaths, notes);


                return true;
            }

            return false;
        }

        // recursively scan files in directories and check if it's uploaded or not.
        // returns true if the specified folder exists
        private static bool scanFilesAndUpload(String postFileURL, String directoryPath, String projectName, String subjectId, String dataType, String subDirectoryPath, String[] excludeDirectoryPaths, String notes)
        {
            try
            {   //Check if local directory exist
                if (!Directory.Exists(directoryPath))
                {
                    return false;
                }
                else
                {
                    //--- check the directory files -----
                    #region Scan files in Directory

                    if (excludeDirectoryPaths != null)
                    {
                        for (int i = 0; i < excludeDirectoryPaths.Length; i++)
                        {
                            if (directoryPath == excludeDirectoryPaths[i])
                            {
                                return false;
                            }
                        }
                    }

                    try
                    {
                        string[] fileList = Directory.GetFiles(directoryPath);

                        Dictionary<String, String> uploadedList = new Dictionary<String, String>();

                        if (fileList != null)
                        {

                            //Get File to upload
                            String pathToHistoryFile = directoryPath + "\\" + fileUploadHistoryFileName;
                            if (File.Exists(pathToHistoryFile))
                            {
                                fileUploadHistoryReader = File.OpenText(pathToHistoryFile);
                                string input = null;
                                while ((input = fileUploadHistoryReader.ReadLine()) != null)
                                {
                                    // filename,last write time
                                    String[] splittedLine = input.Split(',');
                                    uploadedList.Add(splittedLine[0], splittedLine[1]);
                                }
                                fileUploadHistoryReader.Close();

                                // check files to see if it's uploaded or not
                                for (int i = 0; i < fileList.Length; i++)
                                {
                                    // skip file if it's the log file
                                    if (Path.GetFileName(fileList[i]) == fileUploadHistoryFileName)
                                        continue;

                                    //Here add the File to upload to the filetoupload list
                                    if (uploadedList.ContainsKey(fileList[i]))
                                    {
                                        FileInfo finfo = new FileInfo(fileList[i]);

                                        // now check last write time
                                        if (uploadedList[fileList[i]] != finfo.LastWriteTime.ToString())
                                        {
                                            // time not equal, upload required.
                                            //FileToSend fileToSend = new FileToSend(postFileURL, directoryPath + "/" + fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                            FileToSend fileToSend = new FileToSend(postFileURL, directoryPath + "/" + fileList[i],  projectName, subjectId, dataType, subDirectoryPath, notes);
                                            fileUploadQueue.Add(fileToSend);
                                        }
                                        else
                                        {
                                            if (enableLogging)
                                            {
                                                logWriter.WriteLine(DateTime.Now + "," + fileList[i] + ", already uploaded.");
                                                logWriter.Flush();
                                            }
                                        }
                                    }
                                    else
                                    {
                                        // new file, upload required.
                                        //FileToSend fileToSend = new FileToSend(postFileURL, fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                        FileToSend fileToSend = new FileToSend(postFileURL, fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                        fileUploadQueue.Add(fileToSend);
                                    }
                                }
                            }
                            else // the flog.txt do not exist, upload everything.
                            {

                                // check files to see if it's uploaded or not
                                for (int i = 0; i < fileList.Length; i++)
                                {
                                    //FileToSend fileToSend = new FileToSend(postFileURL, fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                    FileToSend fileToSend = new FileToSend(postFileURL, fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                    fileUploadQueue.Add(fileToSend);
                                }
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        if (enableLogging)
                        {
                            logWriter.WriteLine("Error in Check directory files:" + e.Message);
                            logWriter.Flush();
                        }
                    }

                    #endregion



                    //----- Check directories  ---------------
                    #region Scan directories

                    try
                    {
                        string[] dirList = Directory.GetDirectories(directoryPath);

                        if (dirList != null)
                        {

                            for (int i = 0; i < dirList.Length; i++)
                            {
                                String newSubDirectoryPath = dirList[i].Substring(selectedDirectoryPath.Length);

                                //Call the function recursively to upload all files in the subfolder.
                                scanFilesAndUpload(postFileURL, dirList[i], projectName, subjectId, dataType, FileUploader.selectedSubDirectoryPath + newSubDirectoryPath, excludeDirectoryPaths, notes);
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        if (enableLogging)
                        {
                            logWriter.WriteLine("Error in Check directories:" + e.Message);
                            logWriter.Flush();
                        }
                    }

                    #endregion

                }
            }
            catch (Exception e)
            {
                if (enableLogging)
                {
                    logWriter.WriteLine("Error:" + e.Message);
                    logWriter.Flush();
                }
                return false;
            }

            return true;
        }


        public static bool scanLogFilesAndDelete(String directoryPath, String[] excludeDirectoryPaths)
        {
            try
            {   //Check if local directory exist
                if (!Directory.Exists(directoryPath))
                {
                    return false;
                }
                else
                {
                    //--- check the directory files -----
                    #region Scan files in Directory

                    if (excludeDirectoryPaths != null)
                    {
                        for (int i = 0; i < excludeDirectoryPaths.Length; i++)
                        {
                            if (directoryPath == excludeDirectoryPaths[i])
                            {
                                return false;
                            }
                        }
                    }

                    try
                    {
                        string[] fileList = Directory.GetFiles(directoryPath);

                        Dictionary<String, String> uploadedList = new Dictionary<String, String>();

                        if (fileList != null)
                        {
                            String pathToHistoryFile = directoryPath + "\\" + fileUploadHistoryFileName;
                            if (File.Exists(pathToHistoryFile))
                            {
                                //Make sure that I backup the history file properly
                                File.Delete(pathToHistoryFile);
                                if (enableLogging)
                                {
                                    logWriter.WriteLine(DateTime.Now + ", Log  deleted:" + pathToHistoryFile);
                                    logWriter.Flush();
                                }
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        if (enableLogging)
                        {
                            logWriter.WriteLine("Error in Check directory files:" + e.Message);
                            logWriter.Flush();
                        }
                    }

                    #endregion

                    //----- Check directories  ---------------
                    #region Scan directories

                    try
                    {
                        string[] dirList = Directory.GetDirectories(directoryPath);

                        if (dirList != null)
                        {
                            for (int i = 0; i < dirList.Length; i++)
                            {

                                //Call the function recursively to get the file sizes in the subfolder.
                                scanLogFilesAndDelete(dirList[i], excludeDirectoryPaths);
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        if (enableLogging)
                        {
                            logWriter.WriteLine("Error in Check directories:" + e.Message);
                            logWriter.Flush();
                        }
                    }

                    #endregion

                }
            }
            catch (Exception e)
            {
                if (enableLogging)
                {
                    logWriter.WriteLine("Error:" + e.Message);
                    logWriter.Flush();
                }
                return false;
            }

            return true;
        }

        #endregion




        #region CRC32

        public static long getCRC32(String filePath)
        {
            Crc32 crc32 = new Crc32();
            String hash = String.Empty;

            using (FileStream fs = File.Open(filePath, FileMode.Open))
                foreach (byte b in crc32.ComputeHash(fs)) hash += b.ToString("x2").ToLower();

            long crc32Base10 = Convert.ToInt64(hash, 16);
            return crc32Base10;
        }

        #endregion 

        #region MD5 

        public static String GetMD5HashFromFile(String fileName)
        {
            FileStream file = new FileStream(fileName, FileMode.Open);
            MD5 md5 = new MD5CryptoServiceProvider();
            byte[] retVal = md5.ComputeHash(file);
            file.Close();

            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < retVal.Length; i++)
            {
                sb.Append(retVal[i].ToString("x2"));
            }
            return sb.ToString();
        }

        #endregion


    }




    
    internal class FileToSend
    {

        #region Declare Variables

        internal String postFileURL, filePath, fileName, applicationName, subjectId, dataType, dateString, subDirectoryPath, notes;
        private double unixTime;
        private const int httpWebrequestTimeout = 600; // in seconds
        public int failedCount = 0;
        private String checkSum;


        #endregion 



        public FileToSend(String postFileURL, String filePath, String applicationName, String subjectId, String dataType, String subDirectoryPath, String notes)
        {
            this.postFileURL = postFileURL;

          
                if( !Directory.Exists(filePath) )
                   this.filePath = Path.GetDirectoryName(filePath) + "\\";
                else
                    if (!filePath.EndsWith("\\"))
                       this.filePath = filePath;
                    else
                       this.filePath = filePath + "\\";
           
                

            this.fileName = Path.GetFileName(filePath);
            this.applicationName = applicationName;
            this.subjectId = subjectId;
            this.dataType = dataType;

            this.subDirectoryPath = subDirectoryPath.Replace('\\', '/');
            this.notes = notes;


            TimeSpan timeZoneOffset = TimeZone.CurrentTimeZone.GetUtcOffset(DateTime.Now);
            this.dateString = DateTime.UtcNow.ToString("yyyy-MM-dd HH:mm:ss.fff") + getGMT(timeZoneOffset);
            this.unixTime = getUnixtime();

            //this.checkSum = FileUploadManager.getCRC32(filePath);
            this.checkSum = FileUploader.GetMD5HashFromFile(filePath);

        }



        #region Set/Get Parameters


        public String getSubjectId()
        {
            return subjectId;
        }

   
        public String getFilePath()
        {
            return filePath;
        }


        private String getGMT(TimeSpan tzd)
        {
            String tzdPart = "Z";
            if (tzd != TimeSpan.Zero)
                tzdPart = String.Format("{0}{1:00}:{2:00}", tzd > TimeSpan.Zero ? "+" : "-", System.Math.Abs(tzd.Hours), tzd.Minutes);
            return tzdPart;
        }

        
        private double getUnixtime()
        {
            return (DateTime.UtcNow - new DateTime(1970, 1, 1, 0, 0, 0)).TotalSeconds * 1000;
        }


        #endregion 




        // returns status of the connection
        internal String sendFile()
        {
            try
            {

                #region commented

                
                #region Web Request

                // Create the web request
                HttpWebRequest httpWebRequest = (HttpWebRequest)WebRequest.Create(postFileURL);


                // Create a boundary
                string boundary = "----------------------------" + DateTime.Now.Ticks.ToString("x");
                httpWebRequest.ContentType = "multipart/form-data; boundary=" + boundary;

                
                httpWebRequest.Method = "POST";
                httpWebRequest.KeepAlive = true;
                httpWebRequest.Timeout = httpWebrequestTimeout * 1000;
                
                //Credentials
                //httpWebRequest.Credentials = System.Net.CredentialCache.DefaultCredentials;
                httpWebRequest.Credentials = new NetworkCredential("atenea", "wkt_password");
                httpWebRequest.PreAuthenticate = true;

                #endregion



                #region Headers 

                // Get the boundry in bytes
                byte[] boundarybytes = System.Text.Encoding.ASCII.GetBytes("\r\n--" + boundary + "\r\n");


                //add file path
                string headerTemplate = "Content-Disposition: form-data;" +
                                        "name=\"type\";" +
                                        "relative_path=\"" + filePath + "\"\r\n\r\n"; 


                //add the filename
               headerTemplate += "Content-Disposition: form-data;" +
                                        "name=\"{0}\";" +
                                        "filename=\"{1}\"\r\n ";
                
                //add the file stream header
                headerTemplate +="Content-Type: application/octet-stream\r\n\r\n";

                // Add the filename to the header
                string header = string.Format(headerTemplate, "file", fileName);

                //convert the header to a byte array
                byte[] headerbytes = System.Text.Encoding.UTF8.GetBytes(header);

                // Add all of the content up.
                httpWebRequest.ContentLength = new FileInfo(filePath).Length +
                                               headerbytes.Length +
                                               (boundarybytes.Length * 2) + 2;
                
                

                #region commented

                #endregion 

                #endregion


                #region Get Stream
                
                // Get the output stream
                Stream requestStream = httpWebRequest.GetRequestStream();

                // Write out the starting boundry
                requestStream.Write(boundarybytes, 0, boundarybytes.Length);

                // Write the header including the filename.
                requestStream.Write(headerbytes, 0, headerbytes.Length);


                #endregion


                #region Send the header and file

                // Open up a filestream.
                FileStream fileStream = new FileStream(filePath, FileMode.Open, FileAccess.Read);

                // Use 4096 for the buffer
                byte[] buffer = new byte[4096];

                int bytesRead = 0;

                // Loop through whole file uploading parts in a stream.
                while ((bytesRead = fileStream.Read(buffer, 0, buffer.Length)) != 0)
                {
                    requestStream.Write(buffer, 0, bytesRead);
                    requestStream.Flush();
                }



                // Write out the trailing boundry
                boundarybytes = System.Text.Encoding.ASCII.GetBytes("\r\n--" + boundary + "--\r\n");
                requestStream.Write(boundarybytes, 0, boundarybytes.Length);
                

                #endregion



                #region Close the request and file stream

                requestStream.Close();
                fileStream.Close();
                
                #endregion



                #region Get Web Response

                    WebResponse webResponse = httpWebRequest.GetResponse();
                    Stream responseStream = webResponse.GetResponseStream();
                    StreamReader responseReader = new StreamReader(responseStream);
                    String uploadResponse = responseReader.ReadToEnd();



                    // Close response object.
                    webResponse.Close();


                    //Check the WebResponse
                    if (uploadResponse.Trim(new char[] { '\n' }) == checkSum)
                    {
                        return "success";
                    }
                    else
                    {
                        //return uploadResponse;
                        return "failure";
                    }

                #endregion

                

                #endregion 


                


            }
           catch (Exception e)
           {
               // no internet connection
               return e.Message;
           }
        }





    }


}
