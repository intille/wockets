using System;
using System.Runtime.InteropServices;
using System.Text;
using System.IO;
using Microsoft.WindowsMobile.PocketOutlook;

namespace Wockets.Utils.sms
{
    internal class Util2
    {

        public static bool SendSMS(String m_sRecipientPhone,String m_sSMSContent)
        {
            bool bSuccess = SendSMSMessage(m_sRecipientPhone, m_sSMSContent, false) == 0;

            if (!bSuccess)
            {
                return false;
            }

            return true;
        }

        [DllImport("cemapi.dll", EntryPoint = "#48", SetLastError = true)]
        private static extern int SendSMSMessage(string RecipientAddress, string MessageText, bool DeliveryReportRequested);
    }
}
