using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;

namespace SMSLib
{
    class MessageToResend
    {
        String clientNum, msgContent;
        public MessageToResend(String clientNum, String msgContent)
        {
            this.clientNum = clientNum;
            this.msgContent = msgContent;
        }

        public String ClientNum
        {
            get
            {
                return clientNum;
            }
        }

        public String MsgContent
        {
            get
            {
                return msgContent;
            }
        }
    }
}
