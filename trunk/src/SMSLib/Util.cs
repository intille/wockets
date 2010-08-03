using System;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.IO;
using Microsoft.WindowsMobile.PocketOutlook;
using AppUpdater.Logging;

namespace SMSLib
{
    internal class Util
    {
        private static Thread m_SendSMSThread;
        private static string m_sRecipientPhone;
        private static string m_sSMSContent;

        private static void SendSMS()
        {
            int k = m_sSMSContent.Length;

            bool bSuccess = SendSMSMessage(m_sRecipientPhone, m_sSMSContent, false) == 0;

            if (!bSuccess)
            {

                // the following lines are specific for City Project. 

                // make a log of message not send here.
                Logger.LogError("Error sending text message :" + m_sSMSContent, false);

                SMSManager.requireResendMsgList.Add(new MessageToResend(m_sRecipientPhone, m_sSMSContent));

                // split the content and throw it into email for sending later.
                //String[] splittedContent = m_sSMSContent.Split('#');


                //if(splittedContent.Length == 3)
                //   EmailSender.SendEmailThroughInternet(splittedContent[0], splittedContent[1], splittedContent[2]);
                
                //MessageBox.Show("Error when sending  " + m_sSMSContent, "Error",
                //               MessageBoxButtons.OK, MessageBoxIcon.Asterisk, MessageBoxDefaultButton.Button1);
                
                
                // send the next message even when this one is NOT successfully sent.
                SMSManager.flowControlFlag = true;
            }
            else
            {
                // only send the next message when this one is successfully sent.
                SMSManager.flowControlFlag = true;
            }
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
