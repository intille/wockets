using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Threading;

namespace SMSLib
{
    internal class ReceivedMessage
    {
        private String msgID;
        private int numOfMessages;
        private String[] receivedMessage;
        private DateTime receivingStartTime;
        private TimeSpan acceptableWaitTime;
        private String msgSender;
        private bool msgAllReceived = false;

        //resend timeout
        private const int secondsAllowedForEachMessage = 8;

        public ReceivedMessage(String msgID, String sender, int numOfMessages)
        {
            this.msgID = msgID;
            this.numOfMessages = numOfMessages;
            this.msgSender = sender;
            this.receivedMessage = new String[numOfMessages];
            this.receivingStartTime = DateTime.Now;
            acceptableWaitTime = calculateAcceptableWaitTime(numOfMessages);

            Thread checkThread = new Thread(new ThreadStart(checkLoop));
            checkThread.Start();
        }
        private void checkLoop()
        {
            while (!msgAllReceived)
            {
                estimateResendNeed();
                Thread.Sleep(10000);
            }
        }

        private void estimateResendNeed()
        {
            // if waiting TOO long for the message to complete.
            if (((DateTime.Now - receivingStartTime) > acceptableWaitTime) && (!msgAllReceived))
            {
                String resendParts = "";

                //find missing parts
                for (int i = 0; i < numOfMessages; i++)
                {
                    if (receivedMessage[i] == null)
                    {
                        resendParts += i + ",";
                    }
                }

                if (resendParts != "")
                {
                    //clean up the last comma
                    resendParts = resendParts.Substring(0, resendParts.Length - 1);

                    //send resendCommand
                    //<msgID, r>
                    Util.SendSMS(msgSender, SMSManager.sendControlPrefix + "<" + msgID + ",r>" + resendParts);

                    //extend acceptable wait time 2 minutes so that if resend was not received, it will resend again.
                    acceptableWaitTime = acceptableWaitTime.Add(new TimeSpan(0, 2, 0));
                }

            }
        }

        // not taken part size into consideration yet.
        private TimeSpan calculateAcceptableWaitTime(int numOfMessages)
        {
            long totalTicksAllowed = secondsAllowedForEachMessage * numOfMessages * TimeSpan.TicksPerSecond;
            return new TimeSpan(totalTicksAllowed);
        }

        //add message and return true if all pieces are in place.
        public bool addMessage(int msgNum, String data)
        {
            //unlock to successfully receive messages.
            receivedMessage[msgNum] = data;

            for (int i = 0; i < numOfMessages; i++)
            {
                if (receivedMessage[i] == null)
                {
                    return false;
                }
            }
            msgAllReceived = true;

            //no missing parts! set off success message
            Util.SendSMS(msgSender, SMSManager.sendControlPrefix + "<" + msgID + ",s>");

            return true;
        }

        public String getFullMessage()
        {
            String fullMessage = "";
            for (int i = 0; i < numOfMessages; i++)
            {
                fullMessage += receivedMessage[i];
            }
            return fullMessage;
        }

        public String getMessageID()
        {
            return msgID;
        }

        public int getNumOfMessages()
        {
            return numOfMessages;
        }

        public void stopTimer()
        {
            msgAllReceived = true;
        }
    }
}
