using System;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.IO;
using Microsoft.WindowsMobile.PocketOutlook;


namespace Wockets.Data.sms
{
    internal class Util
    {
        private static Thread m_SendSMSThread;
        private static string m_sRecipientPhone;
        private static string m_sSMSContent;

        private static void SendSMS()
        {
            bool bSuccess = SendSMSMessage(m_sRecipientPhone, m_sSMSContent, false) == 0;

            if (!bSuccess)
            {

             

                //SMSManager.requireResendMsgList.Add(new MessageToResend(m_sRecipientPhone, m_sSMSContent));

            }

            // Next.
            SMSManager.messageSendingFlag = true;
        }

        internal static void SendSMS(string recipient, string sContent)
        {
            m_sRecipientPhone = recipient;
            m_sSMSContent = sContent;
            m_SendSMSThread = new Thread(SendSMS);
            m_SendSMSThread.Start();
        }

        [DllImport("cemapi.dll", EntryPoint = "#48", SetLastError = true)]
        private static extern int SendSMSMessage(string RecipientAddress, string MessageText, bool DeliveryReportRequested);
    }
}
