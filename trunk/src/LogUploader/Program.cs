using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils;
using System.Collections.Specialized;
using Wockets;
using System.Net;
using  Wockets.Utils.Http;
using System.IO;
using System.Collections;

namespace LogUploader
{
    class Program
    {
        static void Main(string[] args)
        {

            String getUri = "http://wockets.media.mit.edu/LogStatus.php";
            SynchronizedLogger.Load();
            ArrayList toRemove = new ArrayList();
            //foreach (string filename in sortedFiles)
            foreach (String line in SynchronizedLogger._Lines)
            {
                string[] tokens = line.Split(new char[] { ',' });
                if (tokens != null)
                {
                    if (tokens.Length == 10)
                    {

                        NameValueCollection getData = new NameValueCollection();
                        getData.Add("imei", CurrentPhone._IMEI);
                        getData.Add("sender_date", tokens[0]);
                        getData.Add("phone_battery", tokens[1]);
                        getData.Add("mainmemory", tokens[2]);
                        getData.Add("sdmemory", tokens[3]);
                        getData.Add("battery1", tokens[4]);
                        getData.Add("transmitted_bytes1", tokens[5]);
                        getData.Add("received_bytes1", tokens[6]);
                        getData.Add("battery2", tokens[7]);
                        getData.Add("transmitted_bytes2", tokens[8]);
                        getData.Add("received_bytes2", tokens[9]);
                        String checkresponse = "";
                        using (WebResponse response = FileUploader.Get(new Uri(getUri), getData))
                        {

                            StreamReader reader = null;
                            try
                            {
                                reader = new StreamReader(response.GetResponseStream());
                                string str = reader.ReadLine();
                                if (str != null)
                                    checkresponse += str;
                                while (str != null)
                                {
                                    str = reader.ReadLine();
                                    if (str != null)
                                        checkresponse += str;
                                }
                            }
                            catch
                            {

                            }
                            finally
                            {
                                if (reader != null) reader.Close();
                                if (response != null) response.Close();
                            }
                        }

                        if (checkresponse == "success")
                            toRemove.Add(line);
                    }

                    else if (tokens.Length == 4) //Activity count token
                    {


                        NameValueCollection getData = new NameValueCollection();
                        getData.Add("imei", CurrentPhone._IMEI);
                        getData.Add("wocket_id", tokens[0]);
                        getData.Add("sender_date", tokens[1]);
                        getData.Add("mac_address", tokens[2]);
                        getData.Add("activity_count", tokens[3]);
                        String checkresponse = "";
                        using (WebResponse response = FileUploader.Get(new Uri(getUri), getData))
                        {

                            StreamReader reader = null;
                            try
                            {
                                reader = new StreamReader(response.GetResponseStream());
                                string str = reader.ReadLine();
                                if (str != null)
                                    checkresponse += str;
                                while (str != null)
                                {
                                    str = reader.ReadLine();
                                    if (str != null)
                                        checkresponse += str;
                                }
                            }
                            catch
                            {

                            }
                            finally
                            {
                                if (reader != null) reader.Close();
                                if (response != null) response.Close();
                            }
                        }

                        if (checkresponse == "success")
                            toRemove.Add(line);
                    }
                }

            }

            SynchronizedLogger.Remove(toRemove);            
        }
    }
}
        
   
                
