using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;

namespace SMSLib
{
    class SentMessage
    {
        String msgID, type, compressed;
        int numOfMessages;
        String[] data;

        public SentMessage(String msgID, int numOfMessages, String type, String compressed, String[] data)
        {
            this.msgID = msgID;
            this.type = type;
            this.compressed = compressed;
            this.numOfMessages = numOfMessages;
            this.data = data;
        }

        public String getMsgID()
        {
            return msgID;
        }

        public String getSendDataType()
        {
            return type;
        }

        public String getCompressed()
        {
            return compressed;
        }

        public int getNumOfMessages()
        {
            return numOfMessages;
        }

        public String[] getData()
        {
            return data;
        }
    }
}
