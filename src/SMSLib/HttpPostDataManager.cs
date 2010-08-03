using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Net;
using System.IO;
using System.Threading;
using AppUpdater.Logging;

namespace SMSLib
{

    /// <summary>
    /// Http Post Sender is temporarily being with SMS Manager because they serve similar purposes.
    /// </summary>
    public class HttpPostDataManager
    {
        // retry connection count
        private static int retryCount = 3;
        private static String parameterWithSpaces, parameterWithoutSpaces, serverResponse;
        
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
                    Logger.LogDebug("In is DatanetworkConnected. ");
                    string hostName = Dns.GetHostName();
                    IPHostEntry curHost = Dns.GetHostByName(hostName);
                    return curHost.AddressList[0].ToString() != IPAddress.Loopback.ToString();
                }
                catch (Exception ex)
                {
                    Logger.LogError(ex, false);
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


        /// <summary>
        /// The HTTP Send function is blocking. 
        /// </summary>
        /// <param name="uri">uri for data connection</param>
        /// <param name="clientNum">client number of the phone</param>
        /// <param name="msgContent">message content to send</param>
        public static bool SendData(String uri, String clientNum, String msgContent)
        {
            // retry 3 times before giving up. 
            while (retryCount > 0)
            {
                parameterWithSpaces = "dateTime=" + DateTime.Now + "&clientNum=" + clientNum + "&msgContent=" + msgContent;
                parameterWithoutSpaces = parameterWithSpaces.Replace(" ", "%20");
                serverResponse = HttpPost(uri, parameterWithoutSpaces, 20000);

                if (serverResponse != null)
                {
                    if (serverResponse.Equals("No Network"))
                    {
                        // Don't do anything. Retry.
                    }
                    else if (serverResponse.StartsWith("false"))
                    {
                        // For our server, equal to false means it didn't send the phone number;
                        Logger.LogError("No phone number in configuration file, will cause problem in remote logging.", false);
                        return false;
                    }
                    else if (serverResponse.StartsWith("true"))
                    {
                        //command successful.
                        return true;
                    }
                }

                // five second interval between each try.
                Thread.Sleep(5000);

                retryCount--;
            }

            return false;
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
                Logger.LogError("MessageToSend", ex, "HttpPost: Response error", false);
            }

            return null;
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
