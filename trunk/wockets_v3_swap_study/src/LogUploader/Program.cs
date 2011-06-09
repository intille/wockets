using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using Wockets.Utils;
using System.Collections.Specialized;
using Wockets;
using System.Net;
using Wockets.Utils.Http;
using System.IO;
using System.Collections;
using System.Threading;


namespace LogUploader
{

    class Program
    {




        static void Main(string[] args)
        {

            
            PreventWocketsSuspension();


            String getUri = "http://wockets.media.mit.edu/LogStatus.php";
            UploadSynchronizedLogger.Load();
            ArrayList toRemove = new ArrayList();



            //Read Phone Identification Tokens
            String SubjectID = "0";
            String IMEI = "0";


            if (File.Exists("\\Program Files\\wockets\\updater_id.txt"))
            {
                StreamReader tr = new StreamReader("\\Program Files\\wockets\\updater_id.txt");
                string rline;

                if ((rline = tr.ReadLine()) != null)
                {
                    if (rline.Trim().Length > 0)
                    {
                        IMEI = rline;

                        if ((rline = tr.ReadLine()) != null)
                            if (rline.Trim().Length > 0)
                                SubjectID = rline;
                    }
                }
            }

            //Check here that SIM card is always active
            if( IMEI.CompareTo(CurrentPhone._IMEI) == 0 )
            {

                int count = 0;
                while (count < UploadSynchronizedLogger._Lines.Count)
                {

                    //Tokens For Phone Logs
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

                    //Tokens for Wockets Summary Data
                    String sender_date1 = "";
                    String wocket_id = "";
                    String mac_address = "";
                    String activity_count = "";


                    //Tokens for Event Data
                    String SwapTime = "";
                    String SwapEvent = "";
                    String RestartEvent = "";
                    String LocationChangeEvent = "";
                    String SensorSetID = "";
                    String NumberOfSensors = "";
                    String SensorID0 = "";
                    String SensorPlacement0 = "";
                    String SensorLabel0 = "";
                    String SensorID1 = "";
                    String SensorPlacement1 = "";
                    String SensorLabel1 = "";
                    String SensorID2 = "";
                    String SensorPlacement2 = "";
                    String SensorLabel2 = "";


                    // Tokens for QA Data
                    // PromptTime,PromptType,ResponseTime,ResponseIntervalStart,ResponseIntervalEnd,
                    // Categories,PrimaryActivity,AlternateActivities
                    String PromptTime = "";
                    String PromptType = "";
                    String ResponseTime = "";
                    String ResponseIntervalStart = "";
                    String ResponseIntervalEnd = "";
                    String Categories = "";
                    String PrimaryActivity = "";
                    String AlternateActivities = "";

                    //Batches of Lines that Were NOT Sent
                    ArrayList removeBatch1 = new ArrayList();
                    ArrayList removeBatch2 = new ArrayList();
                    ArrayList removeBatch_EventLogs = new ArrayList();
                    ArrayList removeBatch_QA = new ArrayList();


                    bool is_phone_data = false;
                    bool is_wockets_data = false;
                    bool is_event_data = false;
                    bool is_qa_data = false;

                    //Get the first 20 Lines of Information
                    for (int i = 0; (i < 20); i++)
                    {

                        String line = (String)UploadSynchronizedLogger._Lines[count];
                        string[] tokens = line.Split(new char[] { ',' });


                        if (tokens != null)
                        {

                            //Phone Tokens
                            if (tokens.Length == 10)
                            {

                                sender_date += tokens[0] + ",";
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
                                is_phone_data = true;

                            }
                            //Activity count token
                            else if (tokens.Length == 4)
                            {
                                wocket_id += tokens[0] + ",";
                                sender_date1 += tokens[1] + ",";
                                mac_address += tokens[2] + ",";
                                activity_count += tokens[3] + ",";

                                removeBatch2.Add(line);
                                is_wockets_data = true;

                            }
                            //Swap Events Tokens
                            else if (tokens.Length == 15)
                            {
                                SwapTime += tokens[0] + ",";
                                SwapEvent += tokens[1] + ",";
                                RestartEvent += tokens[2] + ",";
                                LocationChangeEvent += tokens[3] + ",";
                                SensorSetID += tokens[4] + ",";
                                NumberOfSensors += tokens[5] + ",";
                                SensorID0 += tokens[6] + ",";
                                SensorPlacement0 += tokens[7] + ",";
                                SensorLabel0 += tokens[8] + ",";
                                SensorID1 += tokens[9] + ",";
                                SensorPlacement1 += tokens[10] + ",";
                                SensorLabel1 += tokens[11] + ",";
                                SensorID2 += tokens[12] + ",";
                                SensorPlacement2 += tokens[13] + ",";
                                SensorLabel2 += tokens[14] + ",";

                                removeBatch_EventLogs.Add(line);
                                is_event_data = true;

                            }
                            //Swap QA Tokens
                            else if (tokens.Length == 8)
                            {
                                PromptTime += tokens[0] + ",";
                                PromptType += tokens[1] + ",";
                                ResponseTime += tokens[2] + ",";
                                ResponseIntervalStart += tokens[3] + ",";
                                ResponseIntervalEnd += tokens[4] + ",";
                                Categories += tokens[5] + ",";
                                PrimaryActivity += tokens[6] + ",";
                                AlternateActivities += tokens[7] + ",";

                                removeBatch_QA.Add(line);
                                is_qa_data = true;
                            }

                        }


                        count++;
                        if (count >= UploadSynchronizedLogger._Lines.Count)
                            break;

                    }


                    String checkresponse = "";
                    NameValueCollection getData;


                    #region do the get for Phone Tokens

                    if (is_phone_data)
                    {
                        getData = new NameValueCollection();
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

                    }

                    #endregion


                    #region do the get for Wockets Tokens

                    if (is_wockets_data)
                    {
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

                    #endregion


                    #region do the get for Events Tokens

                    if (is_event_data)
                    {
                        getData = new NameValueCollection();
                        getData.Add("imei", CurrentPhone._IMEI);
                        getData.Add("subject_id", SubjectID);
                        getData.Add("swap_time", SwapTime);
                        getData.Add("swap_event", SwapEvent);
                        getData.Add("restart_event", RestartEvent);
                        getData.Add("location_change_event", LocationChangeEvent);
                        getData.Add("sensor_set_id", SensorSetID);
                        getData.Add("number_of_sensors", NumberOfSensors);
                        getData.Add("sensor_id0", SensorID0);
                        getData.Add("sensor_placement0", SensorPlacement0);
                        getData.Add("sensor_label0", SensorLabel0);
                        getData.Add("sensor_id1", SensorID1);
                        getData.Add("sensor_placement1", SensorPlacement1);
                        getData.Add("sensor_label1", SensorLabel1);
                        getData.Add("sensor_id2", SensorID2);
                        getData.Add("sensor_placement2", SensorPlacement2);
                        getData.Add("sensor_label2", SensorLabel2);

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
                            toRemove.AddRange(removeBatch_EventLogs);

                    }

                    #endregion


                    #region do the get for QA Tokens

                    if (is_qa_data)
                    {

                        getData = new NameValueCollection();
                        getData.Add("imei", CurrentPhone._IMEI);
                        getData.Add("subject_id", SubjectID);
                        getData.Add("prompt_time", PromptTime);
                        getData.Add("prompt_type", PromptType);
                        getData.Add("response_time", ResponseTime);
                        getData.Add("response_interval_start", ResponseIntervalStart);
                        getData.Add("response_interval_end", ResponseIntervalEnd);
                        getData.Add("categories", Categories);
                        getData.Add("primary_activity", PrimaryActivity);
                        getData.Add("alternate_activities", AlternateActivities);

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
                            toRemove.AddRange(removeBatch_QA);

                    }

                    #endregion


                }


                UploadSynchronizedLogger.Remove(toRemove);


                #region commented
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


                #endregion commented


            }
            else
            {
                //IMEI not found, phone disconnected, logs were not uploaded
            }


            PermitWocketsSuspension();

        }


        #region Suspend Prevention

        const string WOCKETS_SUSPEND_LOCK_FOLDER = @"\Lockets\";
        const string WOCKETS_SUSPEND_LOCK_EXTENSION = @".lckt";

        // Call this to prevent the Wockets code from suspending the phone
        public static void PreventWocketsSuspension()
        {
            string appNameOnly = "loguploader"; 
            string locketFileName = appNameOnly + WOCKETS_SUSPEND_LOCK_EXTENSION;
            string locketFullPath = System.IO.Path.Combine(WOCKETS_SUSPEND_LOCK_FOLDER, locketFileName);
            if (!Directory.Exists(WOCKETS_SUSPEND_LOCK_FOLDER))
                try { Directory.CreateDirectory(WOCKETS_SUSPEND_LOCK_FOLDER); }
                catch { }
            if (File.Exists(locketFullPath))
                try { File.Delete(locketFullPath); }
                catch { }
            try { File.Create(locketFullPath).Dispose(); }
            catch { }
        }

        // Call this when you are ready to allow the Wockets code to suspend the phone
        public static void PermitWocketsSuspension()
        {
            string appNameOnly = "loguploader"; 
            string locketFileName = appNameOnly + WOCKETS_SUSPEND_LOCK_EXTENSION;
            string locketFullPath = System.IO.Path.Combine(WOCKETS_SUSPEND_LOCK_FOLDER, locketFileName);
            if (File.Exists(locketFullPath))
                try { File.Delete(locketFullPath); }
                catch { }
        }

        #endregion

    }
}
        
   
                
