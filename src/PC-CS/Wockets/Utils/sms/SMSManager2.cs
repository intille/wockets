using System;
//using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.IO;
using System.Threading;
using Microsoft.WindowsMobile.PocketOutlook;
using Microsoft.WindowsMobile.PocketOutlook.MessageInterception;
//using System.IO.Compression;
using Microsoft.Win32;

namespace Wockets.Utils.sms
{
    /// <summary>
    /// SMSLib is a library for sending messages and files over the SMS network.
    /// </summary>
    public class SMSManager2
    {
        /// <summary>
        /// the control prefix for sending data.
        /// </summary>
        internal Char receivingProjectCode, receivingProgramCode;

        public enum SMSErrorMessage {None, RecipientNumberFormatIncorrect, MessageTypeNotEqualTo3, InvalidProjectCode, InvalidProgramCode, MessageTooBig, InvalidCharInMessage};
        
        // total of 84 usable chars (Deducted single/double quotes)
        public Char[] usableCharset = { '@', '$','\n', '_', ' ', '!', '"','#', '%', '&', '\'' ,'(',')','*', '+', ',', '-', '.', '/', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', ':', ';', '<', 
        '=', '>', '?', 'A', 'B', 'C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z'};

        public Char[] numberCharset = { '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z' };

        /// <summary>
        /// message intercepter
        /// </summary>
        protected MessageInterceptor smsInterceptor = null;

        /// <summary>
        /// Delegate for event handler upon receiving anything.
        /// </summary>
        /// <param name="fullMessage">Received text</param>
        public delegate void MessageReceivedLogEventHandler(String receivedMsg);

        // An ID which uniquiely identifies this application.
        private String appId;

        private static String receiveControlPrefix;

        // for calculating text length
        private const int maxSMSLength = 128;

        // for testing
        //private const int maxSMSLength = 60;

        private int headerOverhead = 13;

        // keeping track of sentMessages
        private Dictionary<String, SentMessage> unfinishedSentMsgList;

        private System.Windows.Forms.Timer resendTimer;

        // resend if no response was heard over an hour
        private const int resendCheckInterval = 600000; // 10 minutes

        // for flow control
        private const int sendSMSPollingFreq = 15; // seconds
        private const int smsResendRetryTimes = 5;
        private Thread smsSendingMonitorThread;
        private List<MessageToSend> smsSendingQueue = new List<MessageToSend>();

        // for logging
        private StreamWriter logWriter;
        private bool enableLogging = false;

        public SMSManager2(Char receivingProjectCode, Char receivingProgramCode)
        {
            // check project code and program code availability.
            if (!arrayContains(usableCharset,receivingProjectCode))
                throw new ArgumentException("Project Code needs to be within accepted Charset");

            if (!arrayContains(usableCharset, receivingProgramCode))
                throw new ArgumentException("Program Code needs to be within accepted Charset");

            this.receivingProjectCode = receivingProjectCode;
            this.receivingProgramCode = receivingProgramCode;

            resendTimer = new System.Windows.Forms.Timer();

            /* Adds the event and the event handler for the method that will 
            process the timer event to the timer. */
            resendTimer.Tick += new EventHandler(ResendFailedToSentMsgs);

            // Timer runs every 10 minutes.
            resendTimer.Interval = resendCheckInterval;
            resendTimer.Enabled = true;

            unfinishedSentMsgList = new Dictionary<String, SentMessage>();

            // create monitoring thread
            smsSendingMonitorThread = new Thread(new ThreadStart(smsSendngMonitor));
            smsSendingMonitorThread.Start();
        }

        private void smsSendngMonitor()
        {
            while (true)
            {
                while (smsSendingQueue.Count > 0)
                {
                    MessageToSend messageToSend = smsSendingQueue[0];
                    if (Util.SendSMS(messageToSend.getClientNum(), messageToSend.getMsgContent()))
                    {
                        smsSendingQueue.RemoveAt(0);

                        if (enableLogging)
                        {
                            logWriter.WriteLine(DateTime.Now + "," + messageToSend.getClientNum() + "," + messageToSend.getMsgContent() + ", successfully sent.");
                            logWriter.Flush();
                        }
                    }
                    else
                    {

                        if (messageToSend.failedCount >= smsResendRetryTimes)
                        {
                            smsSendingQueue.RemoveAt(0);

                            if (enableLogging)
                            {
                                logWriter.WriteLine(DateTime.Now + "," + messageToSend.getClientNum() + "," + messageToSend.getMsgContent() + ", failed to send too many times. Giving up retrying.");
                                logWriter.Flush();
                            }
                        }
                        else
                        {
                            if (enableLogging)
                            {
                                logWriter.WriteLine(DateTime.Now + "," + messageToSend.getClientNum() + "," + messageToSend.getMsgContent() + ", message failed to send, retrying in " + sendSMSPollingFreq * (messageToSend.failedCount + 1) + " seconds.");
                                logWriter.Flush();
                            }

                            messageToSend.failedCount++;
                            Thread.Sleep(sendSMSPollingFreq * messageToSend.failedCount * 1000);
                        }
                    }
                }

                Thread.Sleep(sendSMSPollingFreq * 1000);
            }
        }

        /// <summary>
        /// Call this method to initialize message interceptor.
        /// </summary>
        /// <param name="applicationID">a unique id in the registry for identifying the message filter rule</param>
        public void initializeMsgInterceptor(String applicationID)
        {
            appId = applicationID;
            receiveControlPrefix = "SMS+" + receivingProjectCode + receivingProgramCode;
            // If the message interceptor is already enabled then
            // retrieve its current settings. Otherwise configure
            // a new instance

            if (MessageInterceptor.IsApplicationLauncherEnabled(appId))
            {
                // clean up the key
                RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Inbox\\Rules", true);
                rk.DeleteSubKeyTree(appId);
                rk.Close();
            }


            // We want to intercept messages that begin with "CKF:" within the
            // message body and delete these messages before they reach the
            // SMS inbox.
            smsInterceptor = new MessageInterceptor(InterceptionAction.NotifyAndDelete, false);
            smsInterceptor.MessageCondition = new MessageCondition(MessageProperty.Body,
                MessagePropertyComparisonType.StartsWith, receiveControlPrefix);

            // Enable the message interceptor, launch application when a certain condition met.
            smsInterceptor.EnableApplicationLauncher(appId);
            smsInterceptor.MessageReceived += SmsInterceptor_MessageReceived;
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

        public void enableLogger(StreamWriter logWriter)
        {
            this.logWriter = logWriter;
            
            if (logWriter != null)
                enableLogging = true;
        }

        private void ResendFailedToSentMsgs(Object myObject, EventArgs myEventArgs)
        {
            int initialCount = unfinishedSentMsgList.Count;
           
            foreach (KeyValuePair<String, SentMessage> entry in unfinishedSentMsgList)
            {
                // do something with entry.Value or entry.Key
                DateTime messageSentTime = entry.Value.getSentTime();
                DateTime currentTime = DateTime.Now;
                TimeSpan ts = currentTime.Subtract(messageSentTime);
                
                // resend message if it's been over an hour since its last been sent. 
                if (ts.Hours >= 1)
                {
                    String[] msgContentArray = entry.Value.getData();

                    for (int i = 0; i < msgContentArray.Length; i++)
                    {
                        String smsToSend = receiveControlPrefix + entry.Value.getSendDataType() + entry.Value.getMsgID()
                                        + entry.Value.getNumOfMessages() + convertPartNumberToChar(i+1) + "0"
                                        + msgContentArray[i];

                        char crcChar = getCRC86(smsToSend);

                        //insert CRC char
                        smsToSend = smsToSend.Remove(13, 1);
                        String msgContent = smsToSend.Insert(13, crcChar.ToString());


                        // resend message back to the server
                        MessageToSend messageToSend = new MessageToSend(entry.Value.getMsgRecipient(), msgContent);
                        smsSendingQueue.Add(messageToSend);
                    }
                }
            
            }
        }

        private void SmsInterceptor_MessageReceived(object sender, MessageInterceptorEventArgs me)
        {
            SmsMessage request = me.Message as SmsMessage;

            if (request != null)
            {
                // Look at the body of the SMS message to determine
                String incomeData = request.Body.Substring(receiveControlPrefix.Length);
                String msgType = incomeData.Substring(0, 3);
                String msgID = incomeData.Substring(3, 2);

                switch (msgType)
                {
                    case "srv": // all parts received.
                        unfinishedSentMsgList.Remove(msgID);
                        Console.WriteLine("message received: " + msgID);
                        break;
                    case "rty": // something to resend
                        if (unfinishedSentMsgList.ContainsKey(msgID))
                        {
                            // find the messages to resend
                            String msgsToResendPart = incomeData.Substring(5);

                            String[] unfinishedMsg = unfinishedSentMsgList[msgID].getData();

                            for (int i = 0; i < msgsToResendPart.Length; i++)
                            {
                                char resendPartChar = msgsToResendPart[i];

                                String smsToSend = receiveControlPrefix + unfinishedSentMsgList[msgID].getSendDataType() + unfinishedSentMsgList[msgID].getMsgID() 
                                    + unfinishedSentMsgList[msgID].getNumOfMessages() + resendPartChar + "0" 
                                    + unfinishedMsg[convertPartNumberCharToInt(resendPartChar) - 1];

                                char crcChar = getCRC86(smsToSend);

                                //insert CRC char
                                smsToSend = smsToSend.Remove(13, 1);
                                String msgContent = smsToSend.Insert(13, crcChar.ToString());

                                // resend message back to the server
                                MessageToSend messageToSend = new MessageToSend(request.From.Address, msgContent);
                                smsSendingQueue.Add(messageToSend);
                            }

                        }
                        else
                        {
                            String msgContent = "SMS-" + receivingProjectCode + receivingProgramCode + "ukn" + msgID;

                            // send a message-unknown 'ukn' back to the server
                            MessageToSend messageToSend = new MessageToSend(request.From.Address, msgContent);
                            smsSendingQueue.Add(messageToSend);
                        }
                        break;
                }

            }
        }

        /// <summary>
        /// Send Text Message that wil be controlled by the SMS protocol we defined.
        /// </summary>
        /// <param name="msgRecipient">10 digit phone number for the message recipient</param>
        /// <param name="receivingProjectCode">1 char for the project</param>
        /// <param name="receivingProgramCode">1 char for the program</param>
        /// <param name="msgType">3 chars for the msgType, developer can define it.</param>
        /// <param name="msg"></param>
        /// <param name="mustGoThrough"></param>
        /// <returns></returns>
        public SMSErrorMessage sendControlledSMS(String msgRecipient, Char receivingProjectCode, Char receivingProgramCode, String msgType, String msg, bool mustGoThrough)
        {

            String smsHeaderBeforeCRCPartNum = "";
            String smsHeader = "";

            // check msgRecipient
            if (msgRecipient.Length != 10)
                return SMSErrorMessage.RecipientNumberFormatIncorrect;

            // check message content for invalid chars
            if (!checkValidChars(msg))
                return SMSErrorMessage.InvalidCharInMessage;

            // deal with each parameter seperately.
            // first thing's first. Does the message need to go through?
            if (mustGoThrough)
            {
                smsHeader = "SMS+";
            }
            else
            {
                smsHeader = "SMS-";
            }

            smsHeaderBeforeCRCPartNum += smsHeader;

            String destinationInfo = "";

            // destination information
            // check project code and program code availability.
            if (!arrayContains(usableCharset, receivingProjectCode))
                return SMSErrorMessage.InvalidProjectCode;
            else
                destinationInfo += receivingProjectCode;

            if (!arrayContains(usableCharset, receivingProgramCode))
                return SMSErrorMessage.InvalidProgramCode;
            else
                destinationInfo += receivingProgramCode;

            smsHeaderBeforeCRCPartNum += destinationInfo;

            // msgType 3 chars
            // didn't really check the charactor availability for the msgtypes
            if (msgType.Length != 3)
                return SMSErrorMessage.MessageTypeNotEqualTo3;

            smsHeaderBeforeCRCPartNum += msgType;

            // removing the compression part for the time being because I can't find a way to decompress it in 
            // the Java server code.

            // compress the data first and see if it's shorter
            //byte[] compressedStr = CompressString(msg);

            //---convert the compressed text to base 64---
            //String compressedStrBase64 = System.Convert.ToBase64String(compressedStr, 0, compressedStr.Length);

            String msgID = "";
            Char numberOfParts = ',';
            String[] messagesToSend = null;

            //---if compressed text is larger than original text, send original text instead---
            // for the time being, as compression is not used, I am currently letting the system ALWAYS send 
            // uncompressed text.
            //if (compressedStrBase64.Length > msg.Length)
            if(true)
            {
                msgID = getMsgID(false);
                messagesToSend = splitMessage(msg);
            }
            else
            {
                //msgID = getMsgID(true);
                //messagesToSend = splitMessage(compressedStrBase64);
            }

            smsHeaderBeforeCRCPartNum += msgID;

            numberOfParts = convertPartNumberToChar(messagesToSend.Length);

            if (numberOfParts == '!')
            {
                return SMSErrorMessage.MessageTooBig;
            }

            smsHeaderBeforeCRCPartNum += numberOfParts;

            // start sending
            for (int i = 0; i < messagesToSend.Length; i++)
            {
                String smsToSend = smsHeaderBeforeCRCPartNum;
                smsToSend += convertPartNumberToChar(i + 1)+""; //let message number start with 1
                smsToSend += '0'; //initialize CRC char to 0 for CRC checksum
                smsToSend += messagesToSend[i];

                Char crcChar = getCRC86(smsToSend);
                
                //insert CRC char
                smsToSend = smsToSend.Remove(13, 1);
                String msgContent = smsToSend.Insert(13, crcChar.ToString());

                MessageToSend messageToSend = new MessageToSend(msgRecipient, msgContent);
                smsSendingQueue.Add(messageToSend);
            }

            // record messages sent
            if(mustGoThrough)
                unfinishedSentMsgList.Add(msgID, new SentMessage(msgRecipient, msgID, numberOfParts, msgType, false, messagesToSend, DateTime.Now));
            
            return SMSErrorMessage.None;
        }

        /// <summary>
        /// Send a regular sms, DON'T use this to send logs to server
        /// </summary>
        /// <param name="msgRecipient"></param>
        /// <param name="msg"></param>
        /// <returns></returns>
        public SMSErrorMessage sendRegularSMS(String msgRecipient, String msgContent)
        {
            // check msgRecipient
            if (msgRecipient.Length != 10)
                return SMSErrorMessage.RecipientNumberFormatIncorrect;

            MessageToSend messageToSend = new MessageToSend(msgRecipient, msgContent);
            smsSendingQueue.Add(messageToSend);

            return SMSErrorMessage.None;
        }

        private bool checkValidChars(String msg)
        {
            for (int i = 0; i < msg.Length; i++)
            {
                if (!arrayContains(usableCharset, Convert.ToChar(msg[i])))
                {
                    return false;
                }
            }

            return true;
        }

        private Char getCRC86(String stringToEncode)
        {
            Byte[] bytesOfMessage = StrToByteArray(stringToEncode);
            int checkValue = 0;

            for (int i = 0; i < bytesOfMessage.Length; i++)
            {
                checkValue = (bytesOfMessage[i] + checkValue) % (usableCharset.Length);
            }

            return usableCharset[checkValue];
        }

        // C# to convert a string to a byte array.
        public static byte[] StrToByteArray(string str)
        {
            System.Text.ASCIIEncoding encoding = new System.Text.ASCIIEncoding();
            return encoding.GetBytes(str);
        }

        private Char convertPartNumberToChar(int number)
        {
            if ((number > numberCharset.Length) || (number == 0))
            {
                return '!';
            }

            return numberCharset[number-1];
        }

        private int convertPartNumberCharToInt(char partNumber){
            return Array.IndexOf(numberCharset, partNumber) + 1;
	    }

        private String getMsgID(bool compression)
        {
            String msgID = "";

            // msgID, pick one randomly.
            Random random = new Random();
            int randomNumber = random.Next(0, usableCharset.Length - 1);

            // put first random char
            msgID += usableCharset[randomNumber];

            randomNumber = random.Next(0, usableCharset.Length - 1);

            Char secondChar = usableCharset[randomNumber];

            // put second random char based on compression
            if (compression)
            {
                while (true)
                {
                    randomNumber = random.Next(0, usableCharset.Length - 1);
                    Char randChar = usableCharset[randomNumber];
                    secondChar = (Char)(randChar & 255);
                    if (arrayContains(usableCharset, secondChar))
                    {
                        msgID += secondChar;
                        break;
                    }
                }
            }
            else
            {
                while (true)
                {
                    randomNumber = random.Next(0, usableCharset.Length - 1);
                    Char randChar = usableCharset[randomNumber];
                    secondChar = (Char)(randChar & 254);
                    if (arrayContains(usableCharset, secondChar))
                    {
                        msgID += secondChar;
                        break;
                    }
                }
            }

            // check if the msgID is used.
            if (unfinishedSentMsgList.ContainsKey(msgID))
            {
                // recursively to try find another one. 
                msgID = getMsgID(compression);
            }

            return msgID;
        }

        private bool arrayContains(char[] charArray, char itemToCheck)
        {
            for (int i = 0; i < charArray.Length; i++)
            {
                if (charArray[i] == itemToCheck)
                    return true;
            }

            return false;
        }

        private String[] splitMessage(String msgToSplit)
        {
            List<String> tmpString = new List<String>();
            while(msgToSplit.Length > 0){
                if (msgToSplit.Length > maxSMSLength - headerOverhead)
                {
                    tmpString.Add(msgToSplit.Substring(0, maxSMSLength - headerOverhead));
                    msgToSplit = msgToSplit.Substring(maxSMSLength - headerOverhead);
                }
                else
                {
                    tmpString.Add(msgToSplit);
                    msgToSplit = "";
                }
            }

            return tmpString.ToArray();
        }

        /*
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
        */
    }

    // class for sending text through SMS
    internal class MessageToSend2
    {
        private String clientNum, msgContent;
        public int failedCount = 0;

        public MessageToSend2(String clientNum, String msgContent)
        {
            this.clientNum = clientNum;
            this.msgContent = msgContent;
        }

        public String getClientNum()
        {
            return clientNum;
        }

        public String getMsgContent()
        {
            return msgContent;
        }
    }
}
