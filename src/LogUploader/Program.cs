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
            
            
            int count = 0;
            while (count < SynchronizedLogger._Lines.Count)
            {
                String sender_date = "";
                String phone_battery = "";
                String mainmemory = "";
                String sdmemory = "";
                String battery1 = "";
                String transmitted_bytes1 = "";
                String received_bytes1 = "";

                String battery2 = "";
                String transmitted_bytes2 = "";
                String received_bytes2 = "";

                String sender_date1 = "";
                String wocket_id = "";
                String mac_address = "";
                String activity_count = "";
                ArrayList removeBatch1 = new ArrayList();
                ArrayList removeBatch2 = new ArrayList();
                for (int i = 0; (i < 20); i++)
                {
                    String line = (String) SynchronizedLogger._Lines[count];
                    string[] tokens = line.Split(new char[] { ',' });
                    if (tokens != null)
                    {
                        if (tokens.Length == 10)
                        {                            
                            sender_date+= tokens[0]+",";
                            phone_battery += tokens[1] + ",";
                            mainmemory += tokens[2] + ",";
                            sdmemory += tokens[3] + ",";
                            battery1 += tokens[4] + ",";
                            transmitted_bytes1 += tokens[5] + ",";
                            received_bytes1 += tokens[6] + ",";
                            battery2 += tokens[7] + ",";
                            transmitted_bytes2 += tokens[8] + ",";
                            received_bytes2 += tokens[9] + ",";
                            removeBatch1.Add(line);
                        }
                        else if (tokens.Length == 4) //Activity count token
                        {
                            wocket_id += tokens[0] + ",";
                            sender_date1+= tokens[1]+",";
                            mac_address+= tokens[2]+",";
                            activity_count+=tokens[3]+",";
                            removeBatch2.Add(line);
                        }
                        
                    }


                    count++;
                    if (count >= SynchronizedLogger._Lines.Count)
                        break;
                }

                //do the get
                NameValueCollection getData = new NameValueCollection();
                getData.Add("imei", CurrentPhone._IMEI);
                getData.Add("sender_date", sender_date);
                getData.Add("phone_battery", phone_battery);
                getData.Add("mainmemory", mainmemory);
                getData.Add("sdmemory", sdmemory);
                getData.Add("battery1", battery1);
                getData.Add("transmitted_bytes1", transmitted_bytes1);
                getData.Add("received_bytes1", received_bytes1);
                getData.Add("battery2", battery2);
                getData.Add("transmitted_bytes2", transmitted_bytes2);
                getData.Add("received_bytes2", received_bytes2);
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
                    toRemove.AddRange(removeBatch1);


                getData = new NameValueCollection();
                getData.Add("imei", CurrentPhone._IMEI);
                getData.Add("wocket_id", wocket_id);
                getData.Add("sender_date", sender_date1);
                getData.Add("mac_address", mac_address);
                getData.Add("activity_count", activity_count);
                checkresponse = "";
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
                    toRemove.AddRange(removeBatch2);
            }

            SynchronizedLogger.Remove(toRemove);  

            /* m,,

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
             */
        }
    }
}
        
   
                
