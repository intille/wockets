using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Threading;
using System.IO;
using Microsoft.WindowsMobile.PocketOutlook;
using Microsoft.WindowsMobile.PocketOutlook.MessageInterception;
using System.Runtime.InteropServices;
using System.IO.Compression;

namespace SMSLib
{
    /// <summary>
    /// SMSLib is a library for sending messages and files over the SMS network.
    /// </summary>
    public class SMSManager
    {
        /// <summary>
        /// the control prefix for sending data.
        /// </summary>
        internal static String sendControlPrefix, receiveControlPrefix;

        // An ID which uniquiely identifies this application.
        private String appId;

        private String txtToNum;
        private String txtToSend;
        private Byte[] bytesToSend;

        private String emailRecipient;
        private String emailTitle;
        private String emailData;
        private String smsGatewayNumber;

        // for calculating text length
        private const int maxSMSLength = 128;
        private const int headerOverheadBeforePrefix = 8; //<,,,t,u>
        private int headerOverhead = 0;

        // for merging, 129 chars is the cap
        private List<ReceivedMessage> receivedMessageList;

        // keeping track of sentMessages
        private Dictionary<String, SentMessage> unfinishedSentMsgList;

        // For messages that had a problem in sending. 
        internal static List<MessageToResend> requireResendMsgList = new List<MessageToResend>();

        // flow control for sending
        internal static bool flowControlFlag = true;

        /// <summary>
        /// message intercepter
        /// </summary>
        protected MessageInterceptor smsInterceptor = null;

        /// <summary>
        /// Delegate for event handler upon receiving anything.
        /// </summary>
        /// <param name="fullMessage">Received text</param>
        public delegate void MessageReceivedLogEventHandler(String receivedMsg);

        /// <summary>
        /// Event handler upon receiving anything.
        /// </summary>
        public event MessageReceivedLogEventHandler MessageReceivedLog;

        /// <summary>
        /// Delegate for event handler upon receiving text.
        /// </summary>
        /// <param name="fullMessage">Received text</param>
        public delegate void MessageTextReceivedEventHandler(String fullMessage);

        /// <summary>
        /// Event handler upon receiving text.
        /// </summary>
        public event MessageTextReceivedEventHandler MessageTextAllReceived;

        /// <summary>
        /// Delegate for event handler upon receiving bytes.
        /// </summary>
        /// <param name="fullMessage"></param>
        public delegate void MessageBytesReceivedEventHandler(Byte[] fullMessage);

        /// <summary>
        /// Event handler upon receiving bytes.
        /// </summary>
        public event MessageBytesReceivedEventHandler MessageBytesAllReceived;

        /// <summary>
        /// Constructor the of SMSManager, initializes with only sending mechanisms.
        /// </summary>
        /// <param name="sendControlMsgPrefix">Control prefix for sending messages. 
        /// The prefix will be prepended to all the outgoing messages for the message intercepter to identify them at the receiving end.</param>
        /// <param name="hourlyResendMechanism">Setup the mechanism for resending SMS from the resend list every hour</param>
        public SMSManager(String sendControlMsgPrefix)
        {
            sendControlPrefix = sendControlMsgPrefix;
            receivedMessageList = new List<ReceivedMessage>();
            unfinishedSentMsgList = new Dictionary<string, SentMessage>();
            headerOverhead = headerOverheadBeforePrefix + sendControlMsgPrefix.Length;
        }
        
        /// <summary>
        /// Call this method to initialize message interceptor.
        /// </summary>
        /// <param name="receiveControlPrefix">Control prefix for Identifying which messages to intercept</param>
        /// <param name="appInputId">For bringing up the app when it's not running (unique).</param>
        public void initializeMsgInterceptor(String receiveControlMsgPrefix, String appInputId)
        {
            appId = appInputId;
            receiveControlPrefix = receiveControlMsgPrefix;
            // If the message interceptor is already enabled then
            // retrieve its current settings. Otherwise configure
            // a new instance

            if (MessageInterceptor.IsApplicationLauncherEnabled(appId))
            {
                smsInterceptor = new MessageInterceptor(appId, false);
            }
            else
            {
                // We want to intercept messages that begin with "CKF:" within the
                // message body and delete these messages before they reach the
                // SMS inbox.
                smsInterceptor = new MessageInterceptor(InterceptionAction.NotifyAndDelete, false);
                smsInterceptor.MessageCondition = new MessageCondition(MessageProperty.Body,
                    MessagePropertyComparisonType.StartsWith, receiveControlMsgPrefix);
            }

            // Enable the message interceptor, launch application when a certain condition met.
            smsInterceptor.EnableApplicationLauncher(appId);
            smsInterceptor.MessageReceived += SmsInterceptor_MessageReceived;
        }

        private void SmsInterceptor_MessageReceived(object sender, MessageInterceptorEventArgs me)
        {
            SmsMessage request = me.Message as SmsMessage;
            String data = " Nothing";

            if (request != null)
            {
                // Look at the body of the SMS message to determine
                String incomeData = request.Body.Substring(receiveControlPrefix.Length).Trim();

                // <id, total part #, #, data type, compression>
                String[] headerInfo;

                if (incomeData.StartsWith("<"))
                {
                    String header = incomeData.Substring(1, incomeData.IndexOf(">") - 1);
                    headerInfo = header.Split(',');
                    data = incomeData.Substring(incomeData.IndexOf(">") + 1);
                }
                else
                {
                    //logWriter.WriteLine(DateTime.Now + ", Data format received incorrect.");
                    return;
                }

                // see what type of message it is, if a length of 2, means it's a command.
                if (headerInfo.Length == 2)
                {
                    // keeping track of incoming commands.
                    if (this.MessageReceivedLog != null)
                        this.MessageReceivedLog(request.From.Name + " : " + headerInfo[0] + ", cmd=" + headerInfo[1] + ", " + data +"\r\n");
                    //logWriter.WriteLine(DateTime.Now + "," + request.From.Name + "," + headerInfo[0] + ", cmd=" + headerInfo[1] + "," + request.LastModified + "," + request.Received);
                    //logWriter.Flush();

                    switch (headerInfo[1])
                    {
                        case "r":
                            String[] partNumToResend = data.Split(',');
                            try
                            {
                                for (int i = 0; i < partNumToResend.Length; i++)
                                {
                                    String[] originalData = unfinishedSentMsgList[headerInfo[0]].getData();
                                    String messageToSend = sendControlPrefix + "<" + headerInfo[0] + "," + unfinishedSentMsgList[headerInfo[0]].getNumOfMessages() + "," + partNumToResend[i] + ","
                                                                      + unfinishedSentMsgList[headerInfo[0]].getSendDataType() + "," + unfinishedSentMsgList[headerInfo[0]].getCompressed() + ">" + originalData[Convert.ToInt16(partNumToResend[i])];
                                    while (!flowControlFlag)
                                    {
                                        Thread.Sleep(200);
                                    }

                                    Util.SendSMS(request.From.Address, messageToSend);
                                    //logWriter.WriteLine(DateTime.Now + ",Sending: " + headerInfo[0] + "," + (Convert.ToInt16(partNumToResend[i]) + 1) + "/" + unfinishedSentMsgList[headerInfo[0]].getNumOfMessages());
                                    //logWriter.Flush();
                                    flowControlFlag = false;
                                }
                            }
                            catch (KeyNotFoundException)
                            {
                                Util.SendSMS(request.From.Address, sendControlPrefix + "<" + headerInfo[0] + ",k>");
                                //logWriter.WriteLine(DateTime.Now + ",Sending: " + headerInfo[0] + ", kill remaining messages");
                                //logWriter.Flush();

                                //logWriter.WriteLine(DateTime.Now + ", Exception in resending data : " + ex.Message);
                                //logWriter.Flush();
                            }

                            break;
                        case "s":
                            // if message is successfully sent, remove item from list.
                            unfinishedSentMsgList.Remove(headerInfo[0]);
                            break;
                        case "k":
                            for (int i = 0; i < receivedMessageList.Count; i++)
                            {
                                if (receivedMessageList[i].getMessageID().Equals(headerInfo[0]))
                                {
                                    receivedMessageList[i].stopTimer();
                                    receivedMessageList.RemoveAt(i);
                                }
                            }
                            break;
                    }
                }
                else if (headerInfo.Length == 5)
                {
                    // keeping track of incoming messages.
                    if (this.MessageReceivedLog != null)
                    {
                        this.MessageReceivedLog(request.From.Name + " : " + headerInfo[0] + ", seq=" + (Convert.ToUInt16(headerInfo[2]) + 1) + "/" + headerInfo[1] + "," + request.Body.Length + "\r\n");
                    }
                    //logWriter.WriteLine(DateTime.Now + "," + request.From.Name + "," + headerInfo[0] + ",#" + (Convert.ToUInt16(headerInfo[2]) + 1) + "/" + headerInfo[1] + "," + request.LastModified + "," + request.Received + "," + request.Body.Length);
                    //logWriter.Flush();

                    bool msgExist = false;

                    for (int i = 0; i < receivedMessageList.Count; i++)
                    {
                        if (receivedMessageList[i].getMessageID().Equals(headerInfo[0]))
                        {
                            msgExist = true;
                            if (receivedMessageList[i].addMessage(Convert.ToUInt16(headerInfo[2]), data))
                            {
                                outputMessage(headerInfo[3], headerInfo[4], receivedMessageList[i].getFullMessage());
                                //output fully received message.
                                //logWriter.WriteLine(DateTime.Now + "," + request.From.Name + "," + headerInfo[0] + " all received" + "," + request.LastModified + "," + request.Received);
                                //logWriter.Flush();
                                receivedMessageList[i].stopTimer();
                                receivedMessageList.RemoveAt(i);
                            }
                        }
                    }

                    if (!msgExist)
                    {

                        //add new messages to front
                        receivedMessageList.Insert(0, new ReceivedMessage(headerInfo[0], request.From.Address, Convert.ToUInt16(headerInfo[1])));
                        if (receivedMessageList[0].addMessage(Convert.ToUInt16(headerInfo[2]), data))
                        {
                            outputMessage(headerInfo[3], headerInfo[4], receivedMessageList[0].getFullMessage());
                            //output fully received message.
                            //logWriter.WriteLine(DateTime.Now + "," + request.From.Name + "," + headerInfo[0] + " all received" + "," + request.LastModified + "," + request.Received);
                            //logWriter.Flush();

                            receivedMessageList[0].stopTimer();
                            receivedMessageList.RemoveAt(0);

                        }
                    }
                }
            }
        }

        private void outputMessage(String type, String compression, String data)
        {
            //decompress data, c or u. 
            if (compression == "c")
            {
                data = ExpandString(ConvertBase64ToByteArray(data));
            }

            switch (type)
            {
                case "t":
                    if (this.MessageTextAllReceived != null)
                        this.MessageTextAllReceived(data);
                    break;
                case "b":
                    if (this.MessageBytesAllReceived != null)
                        this.MessageBytesAllReceived(ConvertBase64ToByteArray(data));
                    break;
            }
        }

        /// <summary>
        /// Call this method at Form_Closed to clean up the message intercepter.
        /// </summary>
        public void cleanUpInterceptor()
        {
            // Tidy up the resources used by the message interceptor
            if (smsInterceptor != null)
            {
                smsInterceptor.MessageReceived -= SmsInterceptor_MessageReceived;
                smsInterceptor.Dispose();
                smsInterceptor = null;
            }
        }

        private byte[] ConvertBase64ToByteArray(string base64string)
        {
            byte[] binaryData = null;
            try
            {
                binaryData = System.Convert.FromBase64String(base64string);
            }
            catch (Exception)
            {
                return (null);
            }
            return binaryData;
        }

        private string ExpandString(byte[] buffer)
        {
            // turn buffer into a memory stream
            MemoryStream ms = new MemoryStream(buffer);

            // attach decompressor stream to memory stream
            //C1ZStreamReader sr = new C1ZStreamReader(ms);
            DeflateStream sr = new DeflateStream(ms, CompressionMode.Decompress);

            // read uncompressed data
            StreamReader reader = new StreamReader(sr);
            return reader.ReadToEnd();
        }

        /// <summary>
        /// Send text to Email
        /// </summary>
        /// <param name="emailAddress">Recipient email address</param>
        /// <param name="title">Email title</param>
        /// <param name="msg">Email body</param>
        /// <param name="smsGatewayNumber">The SMS Gateway number that directs SMS to email</param>
        public void sendData(String emailAddress, String title, String msg, String smsGatewayNumber)
        {
            this.emailRecipient = emailAddress;
            this.emailTitle = title;
            this.emailData = msg;
            this.smsGatewayNumber = smsGatewayNumber;

            Thread sendDataThread = new Thread(new ThreadStart(sendTextToEmail));
            sendDataThread.Start();
        }

        /// <summary>
        /// Send text message
        /// </summary>
        /// <param name="msgRecipient">10 digit phone number for message recipient</param>
        /// <param name="msg">Message to send.</param>
        public void sendData(String msgRecipient, String msg)
        {
            this.txtToNum = msgRecipient;
            this.txtToSend = msg;

            Thread sendDataThread = new Thread(new ThreadStart(sendText));
            sendDataThread.Start();
        }

        /// <summary>
        /// Send bytes (byte[])
        /// </summary>
        /// <param name="msgRecipient">10 digit phone number for message recipient</param>
        /// <param name="msg">Message to send</param>
        public void sendData(String msgRecipient, Byte[] msg)
        {
            this.txtToNum = msgRecipient;
            this.bytesToSend = msg;

            Thread sendDataThread = new Thread(new ThreadStart(sendBytes));
            sendDataThread.Start();
        }

        private void sendBytes()
        {
            String messageToSend = ""; 
            String txtRecipient = txtToNum;
            String msgTypeLocal = "b";

            if (bytesToSend.Length != 0)
            {
                String msgID = DateTime.Now.Minute.ToString() + DateTime.Now.Second.ToString();

                while (unfinishedSentMsgList.ContainsKey(msgID))
                {
                    msgID = DateTime.Now.Minute.ToString() + DateTime.Now.Second.ToString();
                }

                //---display uncompressed size---
                int uncompressedSize = bytesToSend.Length;

                //---compress the base64 string---
                byte[] compressed = null;
                compressed = CompressString(Convert.ToBase64String(bytesToSend, 0, bytesToSend.Length));

                //---convert the base64 compressed byte array to base64 string---
                String compressedStrBase64 = null;
                compressedStrBase64 = Convert.ToBase64String(compressed, 0, compressed.Length);

                //---display the compressed size---
                int compressedSize = compressedStrBase64.Length;

                int numOfMessages = 0;

                //---only send compressed image if there is a size reduction---
                if (compressedSize < uncompressedSize)
                {
                    String[] arrayOfMessages = splitMessage(msgID, compressedStrBase64, out numOfMessages);
                    unfinishedSentMsgList.Add(msgID, new SentMessage(msgID, numOfMessages, msgTypeLocal, "c", arrayOfMessages));
                    for (int i = 0; i < numOfMessages; i++)
                    {
                        messageToSend = sendControlPrefix + "<" + msgID + "," + numOfMessages + "," + i + "," + msgTypeLocal + "," + "c>" + arrayOfMessages[i];
                        while (!flowControlFlag)
                        {
                            Thread.Sleep(200);
                        }
                        Util.SendSMS(txtToNum, messageToSend);
                        //logWriter.WriteLine(DateTime.Now + ",Sending: " + msgID + "," + (i + 1) + "/" + numOfMessages);
                        //logWriter.Flush();
                        flowControlFlag = false;
                    }
                }
                else
                {
                    String[] arrayOfMessages = splitMessage(msgID, Convert.ToBase64String(bytesToSend), out numOfMessages);
                    unfinishedSentMsgList.Add(msgID, new SentMessage(msgID, numOfMessages, msgTypeLocal, "u", arrayOfMessages));
                    for (int i = 0; i < numOfMessages; i++)
                    {
                        messageToSend = sendControlPrefix + "<" + msgID + "," + numOfMessages + "," + i + "," + msgTypeLocal + "," + "u>" + arrayOfMessages[i];
                        while (!flowControlFlag)
                        {
                            Thread.Sleep(200);
                        }
                        Util.SendSMS(txtToNum, messageToSend);
                        //logWriter.WriteLine(DateTime.Now + ",Sending: " + msgID + "," + (i + 1) + "/" + numOfMessages);
                        //logWriter.Flush();
                        flowControlFlag = false;
                    }
                }
            }
            else
            {
                //MessageBox.Show("No image selected. ", "Error",
                //                MessageBoxButtons.OK, MessageBoxIcon.Asterisk, MessageBoxDefaultButton.Button1);
            }
        }

        private void sendTextToEmail()
        {
            while (!flowControlFlag)
            {
                Thread.Sleep(200);
            }

            String messageToSend = emailRecipient + "#" + emailTitle + "#" + emailData;

            Util.SendSMS(smsGatewayNumber, messageToSend);
            flowControlFlag = false;
        }

        private void sendText()
        {
            String messageToSend = "";

            int numOfMessages = 0;
            byte[] compressedStr = CompressString(txtToSend);
            String txtRecipient = txtToNum;
            String msgTypeLocal = "t";

            //---convert the compressed text to base 64---
            String compressedStrBase64 = System.Convert.ToBase64String(compressedStr, 0, compressedStr.Length);
            String msgID = DateTime.Now.Minute.ToString() + DateTime.Now.Second.ToString();

            while (unfinishedSentMsgList.ContainsKey(msgID))
            {
                msgID = DateTime.Now.Minute.ToString() + DateTime.Now.Second.ToString();
            }

            //---if compressed text is larger than original text, send original text instead---
            if (compressedStrBase64.Length > txtToSend.Length)
            {
                String[] arrayOfMessages = splitMessage(msgID, txtToSend, out numOfMessages);
                unfinishedSentMsgList.Add(msgID, new SentMessage(msgID, numOfMessages, msgTypeLocal, "u", arrayOfMessages));

                for (int i = 0; i < numOfMessages; i++)
                {
                    messageToSend = sendControlPrefix + "<" + msgID + "," + numOfMessages + "," + i + "," + msgTypeLocal + "," + "u>" + arrayOfMessages[i];
                    //wait till ready to send
                    while (!flowControlFlag)
                    {
                        Thread.Sleep(200);
                    }

                    Util.SendSMS(txtRecipient, messageToSend);
                    //logWriter.WriteLine(DateTime.Now + ",Sending: " + msgID + "," + (i + 1) + "/" + numOfMessages);
                    //logWriter.Flush();
                    flowControlFlag = false;
                }
            }
            else
            {
                String[] arrayOfMessages = splitMessage(msgID, compressedStrBase64, out numOfMessages);
                unfinishedSentMsgList.Add(msgID, new SentMessage(msgID, numOfMessages, msgTypeLocal, "c", arrayOfMessages));

                for (int i = 0; i < numOfMessages; i++)
                {
                    messageToSend = sendControlPrefix + "<" + msgID + "," + numOfMessages + "," + i + "," + msgTypeLocal + "," + "c>" + arrayOfMessages[i];
                    while (!flowControlFlag)
                    {
                        Thread.Sleep(200);
                    }
                    Util.SendSMS(txtRecipient, messageToSend);
                    //logWriter.WriteLine(DateTime.Now + ",Sending: " + msgID + "," + (i + 1) + "/" + numOfMessages);
                    //logWriter.Flush();
                    flowControlFlag = false;
                }
            }
        }

        private byte[] CompressString(string str)
        {
            // open memory stream
            MemoryStream ms = new MemoryStream();
            DeflateStream sw = new DeflateStream(ms, CompressionMode.Compress, true);

            // write data into compressor stream
            StreamWriter writer = new StreamWriter(sw, Encoding.Default, 16384);
            writer.Write(str);

            writer.Flush();
            sw.Close();

            return ms.ToArray();
        }

        private String[] splitMessage(String msgID, String messageToSplit, out int numOfMessages)
        {
            String tmpStr = messageToSplit;
            List<String> outputStr = new List<String>();
            int numCount = 0;
            int remainingChars = 0;
            numOfMessages = messageToSplit.Length / (maxSMSLength - 20) + 1; // overestimate total number of messages
            while (tmpStr.Length > 0)
            {
                remainingChars = maxSMSLength - msgID.Length - headerOverhead - digits(numCount) - digits(numOfMessages);

                if (tmpStr.Length > remainingChars)
                {
                    outputStr.Add(tmpStr.Substring(0, remainingChars));
                    tmpStr = tmpStr.Substring(remainingChars);
                }
                else
                {
                    outputStr.Add(tmpStr);
                    tmpStr = "";
                }
                numCount++;
            }
            numOfMessages = numCount;
            return outputStr.ToArray();

        }

        private int digits(int num)
        {
            // Avoid doing work if number is 0
            if (num != 0)
            {
                int n = 0;

                while (num > 0)
                {
                    ++n;
                    num /= 10;
                }

                return n;
            }
            else
                return 1;
        }

        /// <summary>
        /// Method to call in the attempt to resend all the messages that has failed to send in the first place.
        /// Provide uri to attempt to send through HTTP first. Note that if HTTP fails, the system will fall back 
        /// to using SMS. 
        /// CALL THE ResendFailedToSentMsgs() for resends that uses SMS only. 
        /// </summary>
        /// <param name="uri">Provides the uri for sending data through HTTP</param>
        /// <param name="email">Provides the email for sending data through SMS</param>
        /// <param name="title">Provides the email title for sending data through SMS</param>
        /// <param name="smsGatewayNumber">Provides the email gateway for sending data through SMS</param>
        public static void ResendFailedToSentMsgs(String uri, String email, String title, String smsGatewayNumber)
        {
            int initialCount = requireResendMsgList.Count;
            for (int i = 0; i < initialCount; i++)
            {
                // need a thread to do it because it's blocking. 
                MessageToSend newMessage = new MessageToSend(uri, requireResendMsgList[0].ClientNum, requireResendMsgList[0].MsgContent, email, title, smsGatewayNumber);
                Thread sendDataThread = new Thread(newMessage.startConnection);
                sendDataThread.Start();

                requireResendMsgList.RemoveAt(0);
            }
        }
    }


    // class for sending data through HTTP
    internal class MessageToSend
    {
        private String uri, clientNum, msgContent, email, title, smsGatewayNumber;
        public MessageToSend(String uri, String clientNum, String msgContent, String email, String title, String smsGatewayNumber)
        {
            this.uri = uri;
            this.clientNum = clientNum;
            this.msgContent = msgContent;
            this.email = email;
            this.title = title;
            this.smsGatewayNumber = smsGatewayNumber;
        }

        internal void startConnection()
        {
            bool sendSuccess = HttpPostDataManager.SendData(uri, clientNum, msgContent);

            if (!sendSuccess)
            {
                //use SMS if not connected.
                SMSManager smsMgr = new SMSManager("");
                smsMgr.sendData(email, title, msgContent, smsGatewayNumber);
            }
        }
    }
}
