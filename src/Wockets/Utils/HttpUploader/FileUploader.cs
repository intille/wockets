using System;

using System.Collections.Generic;
using System.Text;
using System.Threading;
using System.Net;
using System.IO;
using System.Security.Cryptography;
using Wockets.Utils.sms;




namespace Wockets.Utils.HttpUploader
{

    public class FileUploadManager
    {


  #region Declare Variables

       
        //--- Upload Monitor ---
        private static Thread fileUploadMonitorThread;
        private const int sendFilePollingFreq = 30; // seconds
        private const int fileResendRetryTimes = 3;

        //Files to upload queue
        private static List<FileToSend_Via_SMS> fileUploadQueue = new List<FileToSend_Via_SMS>();
        private static List<FileToSend_Via_SMS> fileFailedToUploadList = new List<FileToSend_Via_SMS>();
        

        //--- Logs ---
        private const String fileUploadHistoryFileName = "flog.txt";
        private static StreamReader fileUploadHistoryReader;
        private static StreamWriter fileUploadHistoryWriter, logWriter;

        private static bool enableLogging = false;


        //Session variables
        private static String selectedDirectoryPath = "";
        private static String selectedSubDirectoryPath = "";

        private static bool fileUploadSessionRunning = false;
        private static int sessionSuccessfullyUploadedCount = 0;
        private static int sessionFailedUploadCount = 0;

        private static String sessionSubjectID = "";
        private static String projectName = "";

        //--- Errors ---
        private static String lastErrorMessage;


        //--- URL --------------
        private static String uri = "http://wockets.scripts.mit.edu/monitoring/postData.php";


        //--- sms related -----
        private static String gatewayNumber = "6173012490";
        private static char projectCode = 'W';
        private static char programCode = 'U';
        private static SMSManager2 smsMgr;
        

        #endregion


        static FileUploadManager()
        {
            //Initialize the file upload monitor
            fileUploadMonitorThread = new Thread(new ThreadStart(fileUploadMonitor));
            fileUploadMonitorThread.Start();

            //if using sms, uncomment this line
            //smsMgr = new SMSManager2(projectCode, programCode);
        }




        public static void fileUploadMonitor()
        {

           

            while(true){

                while (fileUploadQueue.Count > 0)
                {
                    //FileToSend fileToSend = fileUploadQueue[0];
                    FileToSend_Via_SMS fileToSend = fileUploadQueue[0];
                    String sendFileResult = fileToSend.sendFile();

                    if (sendFileResult == "success")
                    {
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
                        projectName = fileToSend.projectName;
                        fileUploadQueue.RemoveAt(0);

                    }
                    else
                    {
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
                            Thread.Sleep(sendFilePollingFreq * fileToSend.failedCount * 1000);
                        }
                    }
                }

                if (fileUploadSessionRunning)
                {
                    if (enableLogging)
                    {
                        logWriter.WriteLine(DateTime.Now + ", File upload session finished. Successfully uploaded files count: " + sessionSuccessfullyUploadedCount + ", Failed to upload file count: " + sessionFailedUploadCount);
                        logWriter.Flush();
                        
                    }

                    // construct sms 
                    /*
                    String txtToSend =  "1,2010-08-07 10:10:10,1281175810000,log,AppUpdater,8:1";

                    SMSManager2.SMSErrorMessage errorMsg = smsMgr.sendControlledSMS(gatewayNumber, projectCode, programCode, "log", txtToSend, false);
                    if (errorMsg != SMSManager2.SMSErrorMessage.None && enableLogging)
                    {
                        logWriter.WriteLine("Error Sending Message: Code: " + errorMsg);
                        logWriter.Flush();
                    }
                     */

                    if (HttpPostDataManager.IsIpAcquired)
                    {
                        // USE LAST SUBJECT ID . ONLY one subject available.
                        // get unix time
                        String localUnixTime = ((DateTime.UtcNow - new DateTime(1970, 1, 1, 0, 0, 0)).TotalSeconds - 4 * 60 * 60).ToString();
                        HttpPostDataManager.SendData(uri, sessionSubjectID, projectName, "file_upload_status_tracking", localUnixTime + "000", "2", "File Upload Session finished [ success: " + sessionSuccessfullyUploadedCount + ", failed: " + sessionFailedUploadCount);

                    }

                    sessionSuccessfullyUploadedCount = 0;
                    sessionFailedUploadCount = 0;
                    fileUploadSessionRunning = false;
                     
                }

                Thread.Sleep(sendFilePollingFreq * 1000);
            }
        }

        public static void enableLogger(StreamWriter logWriter)
        {
            FileUploadManager.logWriter = logWriter;

            if(logWriter != null)
                FileUploadManager.enableLogging = true;
        }

        public static String getLastErrorMessage(){
            return lastErrorMessage;
        }

        // upload files
        public static void uploadFile(String postFileURL, String pathToFile, String projectName, String subjectId, String dataType, String subDirectoryPath, String notes)
        {
            //FileToSend fileToSend = new FileToSend(postFileURL, pathToFile, projectName, subjectId, dataType, subDirectoryPath, notes);
            FileToSend_Via_SMS fileToSend = new FileToSend_Via_SMS(postFileURL, pathToFile, projectName, subjectId, dataType, subDirectoryPath, notes);
            fileUploadQueue.Add(fileToSend);
        }
        
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

                /*
                // construct sms 
                String txtToSend = subjectId + ",2010-08-07 10:10:17,1281172810000,log,AppUpdater,File upload started";

                SMSManager2.SMSErrorMessage errorMsg = smsMgr.sendControlledSMS(gatewayNumber, projectCode, programCode, "log", txtToSend, false);
                if (errorMsg != SMSManager2.SMSErrorMessage.None && enableLogging)
                {
                    logWriter.WriteLine("Error Sending Message: Code: " + errorMsg);
                    logWriter.Flush();
                }
                */

                if (HttpPostDataManager.IsIpAcquired)
                {
                        // get unix time
                        String localUnixTime = ((DateTime.UtcNow - new DateTime(1970,1,1,0,0,0)).TotalSeconds - 4*60*60).ToString();
                        HttpPostDataManager.SendData(uri, subjectId, "wockets", "file_upload_status_tracking", localUnixTime + "000", "2", "File upload started.");
                       
                }


                return true;
            }

            return false;
        }

        private static int countFilesInDirectory(String directoryPath, String[] excludeDirectoryPaths, int fileCounter)
        {
            try
            {   //Check if local directory exist
                if (!Directory.Exists(directoryPath))
                {
                    return -1;
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
                                return -1;
                            }
                        }
                    }

                    try
                    {
                        string[] fileList = Directory.GetFiles(directoryPath);

                        Dictionary<String, String> uploadedList = new Dictionary<String, String>();

                        if (fileList != null)
                        {
                            // check files to see if it's uploaded or not
                            for (int i = 0; i < fileList.Length; i++)
                            {
                                // skip file if it's the log file
                                if (Path.GetFileName(fileList[i]) == fileUploadHistoryFileName)
                                    continue;

                                // count file
                                fileCounter++;
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
                                int tmpFileCount = countFilesInDirectory(dirList[i], excludeDirectoryPaths, fileCounter);
                                if (tmpFileCount != -1)
                                {
                                    fileCounter = tmpFileCount;
                                }
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
                return -1;
            }

            return fileCounter;
        }

        // recursively scan files in directories and check if it's uploaded or not.
        // returns true if the specified folder exists
        // original template written by Selene Mota.
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

                                    if (uploadedList.ContainsKey(fileList[i]))
                                    {
                                        FileInfo finfo = new FileInfo(fileList[i]);

                                        // now check last write time
                                        if (uploadedList[fileList[i]] != finfo.LastWriteTime.ToString())
                                        {
                                            // time not equal, upload required.
                                            //FileToSend fileToSend = new FileToSend(postFileURL, directoryPath + "/" + fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                            FileToSend_Via_SMS fileToSend = new FileToSend_Via_SMS(postFileURL, directoryPath + "/" + fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
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
                                        FileToSend_Via_SMS fileToSend = new FileToSend_Via_SMS(postFileURL, fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
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
                                    FileToSend_Via_SMS fileToSend = new FileToSend_Via_SMS(postFileURL, fileList[i], projectName, subjectId, dataType, subDirectoryPath, notes);
                                    
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
                                scanFilesAndUpload(postFileURL, dirList[i], projectName, subjectId, dataType, FileUploadManager.selectedSubDirectoryPath + newSubDirectoryPath, excludeDirectoryPaths, notes);
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

        public static long getCRC32(String filePath)
        {
            Crc32 crc32 = new Crc32();
            String hash = String.Empty;

            using (FileStream fs = File.Open(filePath, FileMode.Open))
                foreach (byte b in crc32.ComputeHash(fs)) hash += b.ToString("x2").ToLower();

            long crc32Base10 = Convert.ToInt64(hash, 16);
            return crc32Base10;
        }

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
    }

    // class for sending text through SMS
    internal class FileToSend_Via_SMS
    {
        private const int httpWebrequestTimeout = 600; // in seconds
        internal String postFileURL, filePath, projectName, subjectId, dataType, dateString, subDirectoryPath, notes;
        private double unixTime;
        public int failedCount = 0;
        private String checkSum;

        public FileToSend_Via_SMS(String postFileURL, String filePath, String projectName, String subjectId, String dataType, String subDirectoryPath, String notes)
        {
            this.postFileURL = postFileURL;
            this.filePath = filePath;
            this.projectName = projectName;
            this.subjectId = subjectId;
            this.dataType = dataType;

            this.subDirectoryPath = subDirectoryPath.Replace('\\', '/');
            
            this.notes = notes;
            TimeSpan timeZoneOffset = TimeZone.CurrentTimeZone.GetUtcOffset(DateTime.Now);

            this.dateString = DateTime.UtcNow.ToString("yyyy-MM-dd HH:mm:ss.fff") + getGMT(timeZoneOffset);
            this.unixTime = getUnixtime();

            //this.checkSum = FileUploadManager.getCRC32(filePath);
            this.checkSum = FileUploadManager.GetMD5HashFromFile(filePath);
        }

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

        // returns status of the connection
        internal String sendFile()
        {
            try{
                // Create a boundry
                string boundary = "----------------------------" + DateTime.Now.Ticks.ToString("x");

                // Add the GET parameters
                //postFileURL += "?project=" + projectName + "&subject_id=" + subjectId + "&data_type=" + dataType + "&date_string=" + dateString + "&app_id=" + subDirectoryPath + "&unix_time=" + unixTime + "&notes=" + notes;
                //postFileURL = postFileURL.Replace(" ", "%20");

                // Create the web request
                HttpWebRequest httpWebRequest = (HttpWebRequest)WebRequest.Create(postFileURL);
                httpWebRequest.ContentType = "multipart/form-data; boundary=" + boundary;
                //httpWebRequest.Headers.Add("type", filePath);
                httpWebRequest.Method = "POST";
                httpWebRequest.KeepAlive = false;
                httpWebRequest.Timeout = httpWebrequestTimeout * 1000;

                httpWebRequest.Credentials = System.Net.CredentialCache.DefaultCredentials;

                // Get the boundry in bytes
                byte[] boundarybytes = System.Text.Encoding.ASCII.GetBytes("\r\n--" + boundary + "\r\n");

                // Get the header for the file upload
                
                // add post data
                // project
                String header = "Content-Disposition: form-data; name=\"project\"\r\n\r\n";
                header += projectName + "\r\n--" + boundary + "\r\n";
                
                // subject id
                header += "Content-Disposition: form-data; name=\"subject_id\"\r\n\r\n";
                header += subjectId + "\r\n--" + boundary + "\r\n";

                // data type
                header += "Content-Disposition: form-data; name=\"data_type\"\r\n\r\n";
                header += dataType +"\r\n--" + boundary + "\r\n";

                // date string
                header += "Content-Disposition: form-data; name=\"date_string\"\r\n\r\n";
                header += dateString + "\r\n--" + boundary + "\r\n";

                // app id
                header += "Content-Disposition: form-data; name=\"app_id\"\r\n\r\n";
                header += subDirectoryPath + "\r\n--" + boundary + "\r\n";

                // unix time
                header += "Content-Disposition: form-data; name=\"unix_time\"\r\n\r\n";
                header += unixTime + "\r\n--" + boundary + "\r\n";

                // notes
                header += "Content-Disposition: form-data; name=\"notes\"\r\n\r\n";
                header += notes + "\r\n--" + boundary + "\r\n";
                
                header += "Content-Disposition: form-data; name=\"sendfile\"; filename=\"" + Path.GetFileName(filePath) + "\"\r\nContent-Type: application/octet-stream\r\n\r\n";

                //convert the header to a byte array
                byte[] headerbytes = System.Text.Encoding.UTF8.GetBytes(header);

                // Add all of the content up.
                httpWebRequest.ContentLength = new FileInfo(filePath).Length + headerbytes.Length + (boundarybytes.Length * 2) + 2;

                // Get the output stream
                Stream requestStream = httpWebRequest.GetRequestStream();

                // Write out the starting boundry
                requestStream.Write(boundarybytes, 0, boundarybytes.Length);

                // Write the header including the filename.
                requestStream.Write(headerbytes, 0, headerbytes.Length);

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

                boundarybytes = System.Text.Encoding.ASCII.GetBytes("\r\n--" + boundary + "--\r\n");

                // Write out the trailing boundry
                requestStream.Write(boundarybytes, 0, boundarybytes.Length);

                // Close the request and file stream
                requestStream.Close();
                fileStream.Close();
                    
                WebResponse webResponse = httpWebRequest.GetResponse();

                Stream responseStream = webResponse.GetResponseStream();
                StreamReader responseReader = new StreamReader(responseStream);

                String uploadResponse = responseReader.ReadToEnd();

                // Close response object.
                webResponse.Close();

                if (uploadResponse.Trim(new char[] { '\n' }) == checkSum)
                {
                    return "success";
                }
                else
                {
                    return uploadResponse;
                }
           }
           catch (Exception e)
           {
               // no internet connection
               return e.Message;
           }
        }
    }
}
