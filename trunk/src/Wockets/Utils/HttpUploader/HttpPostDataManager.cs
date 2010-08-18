using System;
using System.Collections.Generic;
using System.Text;
using System.Net;
using System.IO;
using System.Threading;

namespace Wockets.Utils.HttpUploader
{

    /// <summary>
    /// Http Post Sender is temporarily being with SMS Manager because they serve similar purposes.
    /// </summary>
    public class HttpPostDataManager
    {
        private static List<FileToSend> postQueue = new List<FileToSend>();

        // retry connection count
        private static int retryCount = 3;
        private static String parameterWithSpaces, parameterWithoutSpaces, serverResponse;
        private static bool enableLogging = false;
        private const int postDataPollingFreq = 10; // seconds
        private const int postResendRetryTimes = 3;
        private static StreamWriter logWriter;
        private static Thread postMonitorThread;

        /// <summary>
        /// Check if an ip was acquired from DHCP. Won't work with Static ip assignment.
        /// It doesn't try to route to a remote server, therefore, the response is almost instant.
        /// Source: http://xman892.blogspot.com/2006/12/how-to-series-detect-network-connection.html
        /// </summary>
        public static bool IsIpAcquired
        {

            get
            {
                try
                {
                    //Logger.LogDebug("In is DatanetworkConnected. ");
                    string hostName = Dns.GetHostName();
                    IPHostEntry curHost = Dns.GetHostByName(hostName);
                    return curHost.AddressList[0].ToString() != IPAddress.Loopback.ToString();
                }
                catch (Exception ex)
                {
                    if (enableLogging)
                    {
                        logWriter.WriteLine(DateTime.Now + ", Error in isIpAcquired: " + ex.Message);
                        logWriter.Flush();
                    }

                    //Logger.LogError(ex, false);
                    return false;
                }
            }
        }

        /// <summary>
        /// The HTTP Send function is blocking. 
        /// </summary>
        /// <param name="uri">uri for data connection</param>
        /// <param name="clientNum">client number of the phone</param>
        /// <param name="msgContent">message content to send</param>
        /*
        public static void SendData(String uri, String clientNum, String msgContent)
        {
            MessageToSend newMessage = new MessageToSend(uri, clientNum, msgContent);
            Thread sendDataThread = new Thread(newMessage.startConnection);
            sendDataThread.Start();
        }
        */

        static HttpPostDataManager()
        {
            postMonitorThread = new Thread(new ThreadStart(postMonitor));
            postMonitorThread.Start();
        }

        // http post data monitor
        public static void postMonitor()
        {
            while (true)
            {
                while (postQueue.Count > 0)
                {
                    FileToSend postMessage = postQueue[0];
                    if (HttpPostDataManager.constructPostAndSend(postMessage.uri, postMessage.subjectId, postMessage.project, postMessage.dbTable, postMessage.unixTime, postMessage.logLevel, postMessage.logContent))
                    {
                        if (enableLogging)
                        {
                            logWriter.WriteLine(DateTime.Now + ": Post data successfully sent.");
                            logWriter.Flush();
                        }
                        postQueue.RemoveAt(0);
                    }
                    else
                    {
                        if (postMessage.failedCount >= postResendRetryTimes)
                        {
                            // fileFailedToUploadList.Add(fileToSend);
                            // put a log on failed to send messages.
                            if (enableLogging)
                            {
                                logWriter.WriteLine(DateTime.Now + ", a post message " + postMessage.logContent + " failed to send too many times. Giving up retrying.");
                                logWriter.Flush();
                            }

                            postQueue.RemoveAt(0);
                        }
                        else
                        {
                            postMessage.failedCount++;

                            // retry a little later every time
                            Thread.Sleep(postDataPollingFreq * postMessage.failedCount * 1000);
                        }
                    }
                }

                Thread.Sleep(postDataPollingFreq * 1000);
            }
        }

        public static void enableLogger(StreamWriter logWriter)
        {
            HttpPostDataManager.logWriter = logWriter;

            if (logWriter != null)
                HttpPostDataManager.enableLogging = true;
        }

        private static bool constructPostAndSend(String uri, String subjectId, String project, String dbTable, String unixTime, String logLevel, String logContent)
        {
            parameterWithSpaces = "project=" + project + "&id=" + subjectId + "&db_table=" + dbTable + "&log_level=" + logLevel + "&log_content=" + logContent + "&unix_time=" + unixTime;
            parameterWithoutSpaces = parameterWithSpaces.Replace(" ", "%20");
            serverResponse = HttpPost(uri, parameterWithoutSpaces, 600000);// 10 minute time out.

            if (serverResponse != null)
            {
                if (serverResponse.Equals("No Network"))
                {
                    // Don't do anything. Retry.
                    if (enableLogging)
                    {
                        logWriter.WriteLine(DateTime.Now + ", No intenet access, retrying.");
                        logWriter.Flush();
                    }
                }
                else if (serverResponse.StartsWith("true"))
                {
                    if (enableLogging)
                    {
                        logWriter.WriteLine(DateTime.Now + ", Data upload successful.");
                        logWriter.Flush();
                    }
                    //command successful.
                    return true;
                }
                else
                {
                    if (enableLogging)
                    {
                        logWriter.WriteLine(DateTime.Now + ", Data upload problem: " + serverResponse);
                        logWriter.Flush();
                    }
                }
            }

            return false;
        }

        /// <summary>
        /// The HTTP Send function is blocking. 
        /// </summary>
        /// <param name="uri">uri for data connection</param>
        /// <param name="clientNum">client number of the phone</param>
        /// <param name="msgContent">message content to send</param>
        public static void SendData(String uri, String subjectId, String project, String dbTable, String unixTime, String logLevel, String logContent)
        {
            postQueue.Add(new FileToSend(uri, subjectId, project, dbTable, unixTime, logLevel, logContent));
        }

        // HTTP Post method from http://en.csharp-online.net/HTTP_Post
        // parameters: name1=value1&name2=value2	
        private static String HttpPost(string uri, string parameters, int timeout)
        {
            WebRequest webRequest = WebRequest.Create(uri);

            //don't timeout.
            //webRequest.Timeout = timeout;


            //string ProxyString = 
            //   System.Configuration.ConfigurationManager.AppSettings
            //   [GetConfigKey("proxy")];
            //webRequest.Proxy = new WebProxy (ProxyString, true);
            //Commenting out above required change to App.Config
            webRequest.ContentType = "application/x-www-form-urlencoded";
            webRequest.Method = "POST";
            byte[] bytes = Encoding.ASCII.GetBytes(parameters);
            Stream os = null;
            try
            { // send the Post
                webRequest.ContentLength = bytes.Length;   //Count bytes to send
                os = webRequest.GetRequestStream();
                os.Write(bytes, 0, bytes.Length);         //Send it
            }
            catch (WebException ex)
            {
                // When no network available.
                //Logger.LogError("MessageToSend", ex, "HttpPost: Request error", false);
                if (enableLogging)
                {
                    logWriter.WriteLine(DateTime.Now + ", HttpPost: Request error: " + ex.Message);
                    logWriter.Flush();
                }
                return "No Network";
            }
            finally
            {
                if (os != null)
                {
                    os.Close();
                }
            }

            try
            { // get the response

                WebResponse webResponse = webRequest.GetResponse();
                if (webResponse == null)
                { return null; }
                StreamReader sr = new StreamReader(webResponse.GetResponseStream());
                return sr.ReadToEnd().Trim();

            }
            catch (WebException ex)
            {
                // When server did not respond after timeout. Assume didn't get it, resend. 
                //Logger.LogError("MessageToSend", ex, "HttpPost: Response error", false);
                if (enableLogging)
                {
                    logWriter.WriteLine(DateTime.Now + ", HttpPost: Response error: " + ex.Message);
                    logWriter.Flush();
                }
            }

            return null;
        }

        
    }

    internal class FileToSend
    {
        internal String uri, subjectId, project, dbTable, unixTime, logLevel, logContent;
        public int failedCount = 0;

        public FileToSend(String uri, String subjectId, String project, String dbTable, String unixTime, String logLevel, String logContent)
        {
            this.uri = uri;
            this.subjectId = subjectId;
            this.project = project;
            this.dbTable = dbTable;
            this.unixTime = unixTime;
            this.logLevel = logLevel;
            this.logContent = logContent;
        }

    }

    /*
    internal class MessageToSend
    {
        // retry connection count
        private int retryCount = 3;
        private String uri, clientNum, msgContent, parameterWithSpaces, parameterWithoutSpaces, serverResponse;
        public MessageToSend(String uri, String clientNum, String msgContent)
        {
            this.uri = uri;
            this.clientNum = clientNum;
            this.msgContent = msgContent;
        }

        internal void startConnection()
        {
            // retry 3 times before giving up. 
            while (retryCount > 0)
            {
                parameterWithSpaces = "dateTime="+DateTime.Now+"&clientNum=" + clientNum + "&msgContent=" + msgContent ;
                parameterWithoutSpaces = parameterWithSpaces.Replace(" ", "%20");
                serverResponse = HttpPost(uri, parameterWithoutSpaces, 20000);

                if (serverResponse != null)
                {
                    if (serverResponse.Equals("No Network"))
                    {
                        // Don't do anything. Retry.
                    }
                    else  if (serverResponse.StartsWith("false"))
                    {
                        // For our server, equal to false means it didn't send the phone number;
                        Logger.LogError("No phone number in configuration file, will cause problem in remote logging.", false);
                        return;
                    }
                    else if (serverResponse.StartsWith("true"))
                    {
                        //command successful.
                        return;
                    }
                }

                // five second interval between each try.
                Thread.Sleep(5000);

                retryCount--;
            }

            // not connected. Go for SMS.
            // I should let this one BLOCK and use the thread at the Logger.
            SMSManager smsMgr = new SMSManager("");
            smsMgr.sendData("mitsmsmgr@gmail.com", "Status", msgContent, "500");

        }

        // HTTP Post method from http://en.csharp-online.net/HTTP_Post
        // parameters: name1=value1&name2=value2	
        String HttpPost(string uri, string parameters, int timeout)
        {
            WebRequest webRequest = WebRequest.Create(uri);

            //don't timeout.
            //webRequest.Timeout = timeout;
            

            //string ProxyString = 
            //   System.Configuration.ConfigurationManager.AppSettings
            //   [GetConfigKey("proxy")];
            //webRequest.Proxy = new WebProxy (ProxyString, true);
            //Commenting out above required change to App.Config
            webRequest.ContentType = "application/x-www-form-urlencoded";
            webRequest.Method = "POST";
            byte[] bytes = Encoding.ASCII.GetBytes(parameters);
            Stream os = null;
            try
            { // send the Post
                webRequest.ContentLength = bytes.Length;   //Count bytes to send
                os = webRequest.GetRequestStream();
                os.Write(bytes, 0, bytes.Length);         //Send it
            }
            catch (WebException ex)
            {
                // When no network available.
                Logger.LogError("MessageToSend", ex, "HttpPost: Request error", false);
                return "No Network";
            }
            finally
            {
                if (os != null)
                {
                    os.Close();
                }
            }

            try
            { // get the response

                WebResponse webResponse = webRequest.GetResponse();
                if (webResponse == null)
                { return null; }
                StreamReader sr = new StreamReader(webResponse.GetResponseStream());
                return sr.ReadToEnd().Trim();

            }
            catch (WebException ex)
            {
                // When server did not respond after timeout. Assume didn't get it, resend. 
                Logger.LogError("MessageToSend",ex, "HttpPost: Response error", false);
            }

            return null;
        }



    }
     */

}
