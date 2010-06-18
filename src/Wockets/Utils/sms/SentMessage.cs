using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.sms
{
    class SentMessage
    {
        String msgID, type, msgRecipient;
        bool compressed;
        char numOfMessages;
        String[] data;
        DateTime sentTime;

        public SentMessage(String msgRecipient, String msgID, char numOfMessages, String type, bool compressed, String[] data, DateTime sentTime)
        {
            this.msgRecipient = msgRecipient;
            this.msgID = msgID;
            this.type = type;
            this.compressed = compressed;
            this.numOfMessages = numOfMessages;
            this.data = data;
            this.sentTime = sentTime;
        }

        public String getMsgRecipient()
        {
            return msgRecipient;
        }

        public String getMsgID()
        {
            return msgID;
        }

        public String getSendDataType()
        {
            return type;
        }

        public bool getCompressed()
        {
            return compressed;
        }

        public char getNumOfMessages()
        {
            return numOfMessages;
        }

        public String[] getData()
        {
            return data;
        }

        public DateTime getSentTime()
        {
            return sentTime;
        }
    }
}
