using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Net;
using Microsoft.WindowsMobile.PocketOutlook;
using AppUpdater.Logging;

namespace SMSLib
{

    /// <summary>
    /// Emain Sender is temporarily being with SMS Manager because they serve similar purposes.
    /// </summary>
    public static class EmailSender
    {


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
                    string hostName = Dns.GetHostName();
                    IPHostEntry curHost = Dns.GetHostByName(hostName);
                    return curHost.AddressList[0].ToString() != IPAddress.Loopback.ToString();
                }
                catch(Exception ex)
                {
                    Logger.LogError(ex, false);
                    return false;
                }
            }
        }


        /// <summary>
        /// Send Email through the internet by the data network.  
        /// User should verify if the data network exists or not first by IsDatanetworkConnected. 
        /// Note that the Email message will be queued in the Outbox for a while until the next batch send
        /// from Pocket Outlook. 
        /// </summary>
        /// <param name="emailAddress">Recipient email address</param>
        /// <param name="title">Email title</param>
        /// <param name="msg">Email body</param>
        public static bool SendEmailThroughInternet(String emailAddress, String title, String msg)
        {
            EmailMessage email = new EmailMessage();
            email.To.Add(new Recipient(emailAddress));
            email.Subject = title;
            email.BodyText = msg;

            // send email message
            using (OutlookSession session = new OutlookSession())
            {
                // account number bigger than one because the first one is the ActiveSync account. 
                if (session.EmailAccounts.Count > 1)
                {
                    // select the email account to send, messages will be queued in the outbox first. 
                    session.EmailAccounts[1].Send(email);

                    Logger.LogDebug("Email queued for transmission. ");
                    return true;
                }
                else
                {
                    Logger.LogError("No account for sending?", false);
                    return false;
                }
            };
        }
    }

}
