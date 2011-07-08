using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Threading;
using System.Globalization;

using HousenCS.MITes;
using System.Collections;
using System.Text.RegularExpressions;
using Wockets.Data.Annotation;
using Wockets;
using Wockets.Data.Configuration;






namespace DataMerger
{


    public partial class Form1 : Form
    {
        
        
        ProgressForm progressForm;
        private static Form2 other_sensors_form = null;

        public Form1()
        {
            InitializeComponent();
            progressForm = new ProgressForm();
            progressForm.Show();


        }



        #region Initialize and Check If the Sensors Files Exist



        
        private void button2_Click(object sender, EventArgs e)
        {
            DialogResult result = this.folderBrowserDialog1.ShowDialog();
            
            
            if (result == DialogResult.OK)
            {
                this.textBox1.Text = this.folderBrowserDialog1.SelectedPath;


                //Check if all the files that we are looking for exist
                try
                {
                    string[] file;

                    #region Delete Older Files

                    if (Directory.Exists(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY))
                    {
                        this.progressForm.AppendLog("Older Merged MITes CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*MITes*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged Wockets CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*Wocket*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged Actigraph CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*Actigraph*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);


                        this.progressForm.AppendLog("Older Merged Sensewear CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*Sensewear*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged Zephyr CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*Zephyr*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged Oxycon CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*Oxycon*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged Omron CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*Omron*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged Columbia CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*columbia*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged GPS CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*gps*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                        this.progressForm.AppendLog("Older Merged RTI CSVs .....................Deleting\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MERGED_SUBDIRECTORY, "*rti*.csv");
                        foreach (string filename in file)
                            File.Delete(filename);

                    }
                    #endregion


                    #region Search for annotation files

                  
                    if (File.Exists(this.textBox1.Text + "\\" + ANNOTATION_SUBDIRECTORY + "\\audioannotation" + "\\AnnotationIntervals.xml"))
                    {
                        this.progressForm.AppendLog("Annotation File in Audio Folder................Found\r\n");
                        ANNOTATION_SUBDIRECTORY = ANNOTATION_DIRECTORY + "\\audioannotation";
                        annotation_subdirectory_list.Add(ANNOTATION_SUBDIRECTORY);
                        annotation_intervals_file_list.Add("AnnotationIntervals.xml");
                    }
                    else 
                    {
                       bool annotation_file_exist = false;

                       if (File.Exists(this.textBox1.Text + "\\" + ANNOTATION_DIRECTORY + "\\PhoneAnnotation" + "\\" + ANNOTATION_INTERVALS_FILE))
                       {
                           this.progressForm.AppendLog("Annotation File in Phone Folder.....................Found\r\n");
                           ANNOTATION_SUBDIRECTORY = ANNOTATION_DIRECTORY + "\\PhoneAnnotation";
                           annotation_subdirectory_list.Add(ANNOTATION_SUBDIRECTORY);
                           annotation_intervals_file_list.Add("AnnotationIntervals.xml");
                           annotation_file_exist = true;
                       }

                       if (Directory.Exists(this.textBox1.Text + "\\" + ANNOTATION_DIRECTORY + "\\videoannotation"))
                       {
                          string dpath = this.textBox1.Text + "\\" + ANNOTATION_DIRECTORY + "\\videoannotation" + "\\";
                          file = Directory.GetFileSystemEntries( dpath, "*"+ ANNOTATION_INTERVALS_FILE);

                          if (file.Length > 0)
                          {
                              this.progressForm.AppendLog("Annotation File in Video Folder.....................Found\r\n");
                              ANNOTATION_SUBDIRECTORY = ANNOTATION_DIRECTORY + "\\videoannotation";
                              

                              for (int i = 0; i < file.Length; i++)
                              {
                                  annotation_subdirectory_list.Add(ANNOTATION_SUBDIRECTORY);
                                  annotation_intervals_file_list.Add(file[i].Substring(dpath.Length)); 
                              }

                              annotation_file_exist = true;
                          }
                          
                       }
                       
                       if (File.Exists(this.textBox1.Text + "\\" + ANNOTATION_DIRECTORY + "\\tabletannotation\\" + ANNOTATION_INTERVALS_FILE))
                       {
                           this.progressForm.AppendLog("Annotation File in Tablet Folder.....................Found\r\n");
                           ANNOTATION_SUBDIRECTORY = ANNOTATION_DIRECTORY + "\\tabletannotation";
                           annotation_subdirectory_list.Add(ANNOTATION_SUBDIRECTORY);
                           annotation_intervals_file_list.Add("AnnotationIntervals.xml");
                           annotation_file_exist = true;
                       } 

                       if ( annotation_subdirectory_list.Count >0 )
                            this.progressForm.AppendLog("Annotation File ..................... Not Found\r\n");

                    }

                    #endregion 


                    #region Load Wockets-MITES Files

                    //activity labels for annotations (Wockets)
                    if (File.Exists(this.textBox1.Text + "\\" + WOCKETS_SUBDIRECTORY + "\\ActivityLabelsRealtime.xml"))
                        this.progressForm.AppendLog("Activity Labels File .....................Found\r\n");
                    else
                        this.progressForm.AppendLog("Activity Labels File .....................Not Found\r\n");


                    try
                    {
                        if (File.Exists("Configuration.xml"))
                            File.Copy("Configuration.xml", this.textBox1.Text + "\\" + WOCKETS_SUBDIRECTORY + "\\Configuration.xml", true);
                    }
                    catch
                    {
                        this.progressForm.AppendLog("Wockets Configuration File .....................Not Found\r\n");
                    }

                    #endregion 


                    #region Load Other Sensor Files

                    //Sensewear
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-sensewear*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Sensewear File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Sensewear File ..................... Not Found\r\n");         


                    //actigraph
                    file = Directory.GetFileSystemEntries(this.textBox1.Text+"\\"+OTHER_SUBDIRECTORY, "*-actigraph*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("1 Actigraph File .....................Found\r\n");
                    else if (file.Length == 2)
                        this.progressForm.AppendLog("2 Actigraph Files .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Actigraph File ..................... Not Found\r\n");


                    //oxycon
                    #region commented oxycon read from othersensors
                    /*
                    if (File.Exists(this.textBox1.Text+"\\"+ OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt"))
                    {
                        this.progressForm.AppendLog("Oxycon Synchronization File .....................Found\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-oxycon.dat");
                        if (file.Length == 1)
                            this.progressForm.AppendLog("Oxycon PC File .....................Found\r\n");
                        else if (file.Length == 0)
                            this.progressForm.AppendLog("Oxycon PC File .....................Not Found\r\n");


                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-flashcard.dat");
                        if (file.Length == 1)
                            this.progressForm.AppendLog("Oxycon Flash File .....................Found\r\n");
                        else if (file.Length == 0)
                        {
                            file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-flash.dat");
                            if (file.Length == 1)
                            {
                                this.progressForm.AppendLog("Oxycon Flash.dat wrong name .....................Renaming\r\n");
                                File.Copy(file[0], file[0].Replace("-flash.dat", "-flashcard.dat"));
                            }
                            else
                                this.progressForm.AppendLog("Oxycon Flash file not found.... manual inspection needed\r\n");
                        }
                    }
                    else
                        this.progressForm.AppendLog("Oxycon Synchronization File ....................Not Found\r\n");
                    */
                    #endregion

                    if( File.Exists(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt") )
                    {
                        if (!File.Exists(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt"))
                        { 
                            File.Move(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt", 
                                      this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt"); 
                        }
                    }
                    
                    
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-oxycon.dat");
                    FileInfo finfo;
                    if (file.Length == 0)
                    {   
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\", "*-oxycon.dat");
                        for(int i= 0; i < file.Length; i++)
                        {
                            finfo = new FileInfo(file[i]);
                            File.Move(file[i], this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\" + finfo.Name); 
                        }   
                     }

                     file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-flashcard*");
                     if (file.Length == 0)
                     {
                         file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\", "*-flashcard*");
                         for (int i = 0; i < file.Length; i++)
                         {
                            finfo = new FileInfo(file[i]);
                            File.Move(file[i], this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\" + finfo.Name);
                         }
                    }


                    if (File.Exists(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\RTITime.txt"))
                    {
                        this.progressForm.AppendLog("RTI Synchronization File .....................Found\r\n");
                    }
                    
                    
                    
                    // check oxycon files from MITES directory
                    if (File.Exists(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt"))
                    {
                        this.progressForm.AppendLog("Oxycon Synchronization File .....................Found\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-oxycon.dat");
                        if (file.Length == 1)
                            this.progressForm.AppendLog("Oxycon PC File .....................Found\r\n");
                        else if (file.Length == 0)
                            this.progressForm.AppendLog("Oxycon PC File .....................Not Found\r\n");


                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-flashcard.dat");
                        if (file.Length == 1)
                            this.progressForm.AppendLog("Oxycon Flash File .....................Found\r\n");
                        else if (file.Length == 0)
                        {
                            file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-flash.dat");
                            if (file.Length == 1)
                            {
                                this.progressForm.AppendLog("Oxycon Flash.dat wrong name .....................Renaming\r\n");
                                File.Copy(file[0], file[0].Replace("-flash.dat", "-flashcard.dat"));
                            }
                            else
                                this.progressForm.AppendLog("Oxycon Flash file not found.... manual inspection needed\r\n");
                        }
                    }
                    else
                    { this.progressForm.AppendLog("Oxycon Synchronization File ....................Not Found\r\n"); }
                    


                    //omron
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-omron.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Omron File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Omron File ..................... Not Found\r\n");

                    //zephyr
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-zephyr*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Zephyr File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Zephyr File ..................... Not Found\r\n");


                    //Columbia
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-columbia*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Columbia File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Columbia File ..................... Not Found\r\n");


                    //GPS
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-gps*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("GPS File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("GPS File ..................... Not Found\r\n");


                    //RTI
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY, "*-rti*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("RTI File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("RTI File ..................... Not Found\r\n");

                    //MITes
                    //configuration files
                    if (File.Exists(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\Configuration.xml"))
                        this.progressForm.AppendLog("Configuration.xml File .....................Found\r\n");

                    if (File.Exists(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\SensorData.xml"))
                        this.progressForm.AppendLog("SensorData.xml File .....................Found\r\n");

                    if (File.Exists(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\SensorData.xml"))
                        this.progressForm.AppendLog("SensorData.xml File .....................Found\r\n");

                    if (Directory.Exists(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\data\\raw\\PLFormat"))
                        this.progressForm.AppendLog("PLFormat Data Directory .....................Found\r\n");
                    else //Attempt to Fix
                    {
                        this.progressForm.AppendLog("Non PLFormat Data Directory .....................Fixing\r\n");
                        if (Directory.Exists(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\data\\raw"))
                        {
                            file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\data\\raw", "*.PLFormat");                    
                            if (file.Length == 1)
                            {

                                string timestamp = file[0].Substring(file[0].IndexOf("MITesAccelBytes.") + 16);
                                timestamp = timestamp.Substring(0, timestamp.IndexOf(".PLFormat"));
                                string[] times = timestamp.Split('-');
                                string date = times[0] + "-" + Convert.ToInt32(times[1]).ToString("00") + "-" + Convert.ToInt32(times[2]).ToString("00");
                                string hour = Convert.ToInt32(times[3]).ToString();

                                Directory.CreateDirectory(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\data\\raw\\PLFormat\\" + date);
                                Directory.CreateDirectory(this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\data\\raw\\PLFormat\\" + date + "\\" + hour);
                                File.Copy(file[0], this.textBox1.Text + "\\" + MITES_SUBDIRECTORY + "\\data\\raw\\PLFormat\\" + date + "\\" + hour + "\\" + file[0].Substring(file[0].IndexOf("MITesAccelBytes.")));
                            }
                            else
                                throw new Exception("Old Format: More than 1 file ....................manual fix needed\r\n");
                        }
                    }

                    
                    #endregion



                    #region Search for other sensors files
                  
                    file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\" + OTHER_SUBDIRECTORY + "\\" );
                   
                     if (file.Length > 1)
                     {
                           other_sensors_form = new Form2(this.textBox1.Text);
                           other_sensors_form.Show();
                     }
               
                  #endregion 


                }
                catch (Exception ex)
                {
                    MessageBox.Show("Error: " + ex.Message);
                    Application.Exit();
                }

                this.button1.Enabled = true;
            }

        }



        #endregion



        #region Thread that checks for the process status


        private Thread aConversionThread;
        private bool converted = false;


        private void ConversionThread()
        {
            string[] filter = new string[2];
            filter[0] = "annotation";
            filter[1] = "setup";


            try
            {

                string session_directory = this.textBox1.Text;

                //delete previous results files
                if (File.Exists(session_directory + "\\result.html"))
                    File.Delete(session_directory + "\\result.html");

                if( annotation_subdirectory_list.Count >0 )
                {

                   
                    //scan trough annotation folders
                    for (int i = 0; i < annotation_subdirectory_list.Count; i++)
                    { 
                        ANNOTATION_SUBDIRECTORY = annotation_subdirectory_list[i];
                        ANNOTATION_INTERVALS_FILE = annotation_intervals_file_list[i];


                        string annotation_header = "RESULTS: " +
                                                   ANNOTATION_SUBDIRECTORY.Substring((ANNOTATION_DIRECTORY + "\\").Length) +
                                                   ", Coder: ";


                        if (ANNOTATION_SUBDIRECTORY.Contains("video"))
                        {
                            MERGED_SUBDIRECTORY = "merged_" + "video_" + ANNOTATION_INTERVALS_FILE.Split('.')[0];
                            annotation_header += ANNOTATION_INTERVALS_FILE.Split('.')[0];
                        }
                        else if (ANNOTATION_SUBDIRECTORY.Contains("Phone"))
                        {
                            MERGED_SUBDIRECTORY = "merged";
                            annotation_header += "phone";
                        }
                        // for tablet annotations
                        else if( ANNOTATION_SUBDIRECTORY.Contains("audio"))
                        {
                            MERGED_SUBDIRECTORY = "merged";
                            annotation_header += "audio";
                        }
                        else if (ANNOTATION_SUBDIRECTORY.Contains("tablet"))
                        {
                            MERGED_SUBDIRECTORY = "merged";
                            annotation_header += "tablet";
                        }
                        else
                        {
                            MERGED_SUBDIRECTORY = "merged";
                            annotation_header += "audio";
                        }
                        

                        if (!Directory.Exists(session_directory + "\\" + MERGED_SUBDIRECTORY))
                            Directory.CreateDirectory(session_directory + "\\" + MERGED_SUBDIRECTORY);
                        else
                        {
                            string[] mfiles = Directory.GetFileSystemEntries(session_directory + "\\" + MERGED_SUBDIRECTORY);
                            
                            for (int j = 0; j < mfiles.Length; j++)
                                File.Delete(mfiles[i]);
                        }



                        
                        TextWriter tw = new StreamWriter(session_directory + "\\result.html", true);
                        tw.WriteLine("\n<p>&nbsp;</p>\n");
                        tw.WriteLine("<HTML><hr></hr><h2><Font Color=#5FB404>" + annotation_header + "</Font></h2></HTML>");
                        tw.WriteLine("\n<p>&nbsp;</p>\n");
                        tw.Flush();
                        tw.Close();

                        try
                        {
                            toCSV(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter);

                            try
                            { toQualityHTML(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter); }
                            catch (Exception ee)
                            {
                                MessageBox.Show("Error: Generating the quality report " + ee.StackTrace);
                            }
                        }
                        catch (Exception e)
                        {
                            MessageBox.Show("Error: Generating the CSV file for " + ANNOTATION_INTERVALS_FILE + ". Trace: " + e.StackTrace);
                        }   
                    }
                }
                else
                {
                    
                    toCSV(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter);


                    try
                    {  
                        toQualityHTML(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter);
                    }
                    catch (Exception ee)
                    {
                        MessageBox.Show("Error: Format error in the result file " + ee.StackTrace);
                    }
                }

            }
            catch (Exception e)
            {
                MessageBox.Show("Error: Format error in the CSV files " + e.StackTrace);
                Environment.Exit(0);
            }


            converted = true;

        }







        private void button1_Click(object sender, EventArgs e)
        {
            if (converted == true)
            {
                Application.Exit();
                Environment.Exit(0);
            }

            this.button1.Text = "Converting";
            this.button1.Enabled = false;
            this.button2.Enabled = false;
            this.label2.Text = "";
            this.label2.Visible = true;
            this.timer1.Enabled = true;
            aConversionThread = new Thread(new ThreadStart(ConversionThread));
            aConversionThread.Start();



        }


        #endregion 



        #region Timer


        private void timer1_Tick(object sender, EventArgs e)
        {
            if (CSVProgress.Length > 0)
            {
                this.label2.Text = CSVProgress;
                CSVProgress = "";
            }

            if (converted)
            {
                this.button1.Text = "Done";
                this.button1.Enabled = true;
                this.label2.Text = "Conversion Completed!";
            }
        }


        #endregion 



        #region Generate the Results File with the Statistical Analysis Of the Data 




      public static void toQualityHTML(string aDataDirectory, string masterDirectory, int maxControllers, string[] filter)
      {
            
            int ACCELEROMETER_STATISTICS_LENGTH=16;
            //int WOCKETS_SR = 92;
            int MITES_SR = 45;


            if (CSVProgress == "")
                CSVProgress = "Generating Quality Assessment Summary in HTML";


            #region ===================  Load the MITES/Wockets DATA ==============================

            //Calculate Data Gaps
            WocketsController wc = new WocketsController("", "", "");
            CurrentWockets._Controller = wc;
            wc.FromXML(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY +"\\SensorData.xml");
            for (int r = 0; (r < wc._Decoders.Count); r++)
                wc._Decoders[r].Initialize();


            SXML.Reader sreader = null;            
            SXML.SensorAnnotation sannotation = null;

            try
            {
                sreader = new SXML.Reader(masterDirectory, aDataDirectory + "\\" + MITES_SUBDIRECTORY);
                sannotation = sreader.parse(maxControllers);
                
                //remove the HR sensor
                for (int i = 0; (i < sannotation.Sensors.Count); i++)
                    if ((Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[i]).ID) == 0))
                    {
                        sannotation.Sensors.RemoveAt(i);
                        break;
                    }
            }
            catch 
            {
                //if there is not mites data, catch the error and continue
            }


            #endregion



            #region ============== Load Annotation Intervals =======================================

            Session session = new Session();
            session.FromXML(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\" + ANNOTATION_INTERVALS_FILE); 
            int numPostures = 0;
            Hashtable postures = new Hashtable();
            int k = 0;


            //Think how to handle this when there are more than one activity type
            Hashtable means_per_class = new Hashtable();
            Hashtable std_per_class = new Hashtable();
            Hashtable freq_per_class = new Hashtable();
            Hashtable min_per_class = new Hashtable();
            Hashtable max_per_class = new Hashtable();


            //Check if the "unknown" class is specified
            bool is_unknown_specified = false;




            //If two categories are available
            if (session.OverlappingActivityLists.Count == 2)
            {
                numPostures = session.OverlappingActivityLists[0].Count * session.OverlappingActivityLists[1].Count + 1;
                
                //Go through the activity list for the two categories
                //This list will generate all combinations of postures-activities
                for (int i = 0; (i < session.OverlappingActivityLists[1].Count); i++)
                    for (int j = 0; (j < session.OverlappingActivityLists[0].Count); j++)
                    {
                        postures.Add(session.OverlappingActivityLists[1][i]._Name + "_" + session.OverlappingActivityLists[0][j]._Name, k);
                        k++;
                    }
            }
            else if (session.OverlappingActivityLists.Count == 1)
            {

                numPostures = session.OverlappingActivityLists[0].Count + 1;

                //Go through the activity list for the available category
                //This list will simply pass the elements in the category list to the postures data structure
                for (int i = 0; (i < session.OverlappingActivityLists[0].Count); i++)
                {
                    if (session.OverlappingActivityLists[0][i]._Name.CompareTo("unknown") == 0)
                        is_unknown_specified = true;

                    postures.Add(session.OverlappingActivityLists[0][i]._Name, k);
                    k++;

                    //initialize the class stats structure
                    means_per_class.Add(session.OverlappingActivityLists[0][i]._Name, (double)0.0);
                    std_per_class.Add(session.OverlappingActivityLists[0][i]._Name, (double)0.0);
                    freq_per_class.Add(session.OverlappingActivityLists[0][i]._Name, (int)0);
                    min_per_class.Add(session.OverlappingActivityLists[0][i]._Name, (double)10000.0);
                    max_per_class.Add(session.OverlappingActivityLists[0][i]._Name, (double)0.0);
                }


            }
            // TODO if four categories present
                
            else if (session.OverlappingActivityLists.Count == 4)
            {                
                numPostures = session.OverlappingActivityLists[0].Count * session.OverlappingActivityLists[1].Count + 1;

                //Go through the activity list for the two categories
                //This list will generate all combinations of postures-activities
                for (int i = 0; (i < session.OverlappingActivityLists[1].Count); i++)
                    for (int j = 0; (j < session.OverlappingActivityLists[0].Count); j++)
                    {
                        postures.Add(session.OverlappingActivityLists[1][i]._Name + "_" + session.OverlappingActivityLists[0][j]._Name, k);
                        k++;
                    }
            }



            //Check if postures contain the "unknown" label, otherwise add it
            if (!is_unknown_specified)
            {
                postures.Add("unknown", k);

                //initialize the class stats structure
                means_per_class.Add("unknown", (double)0.0);
                std_per_class.Add("unknown", (double)0.0);
                freq_per_class.Add("unknown", (int)0);
                min_per_class.Add("unknown", (double)10000.0);
                max_per_class.Add("unknown", (double)0.0);
            }



            #endregion




            #region  ================= Compute Statistics based on Postures  ===========================



            #region Create Data Structures & Variables


            int[] timeLostPostureSensorCounter = new int[numPostures];
            int[] wocketsSR = new int[wc._Sensors.Count];
            int[] trueWocketsSR = new int[wc._Sensors.Count];
            int[][] modeWocketsSR = new int[wc._Sensors.Count][];
            
            
            bool[] disconnected = new bool[wc._Sensors.Count];
            int[] zeroWocketsSR = new int[wc._Sensors.Count];
            int[] numDisconnected = new int[wc._Sensors.Count];
            ArrayList[] disconnectionDistribution = new ArrayList[wc._Sensors.Count];
            int[] disconnectionTimer = new int[wc._Sensors.Count];
            int[] numDisconnections = new int[wc._Sensors.Count];
            int[] meanDisconnection = new int[wc._Sensors.Count];
            int[] sdDisconnection = new int[wc._Sensors.Count];

            int[][] timeLostPostureSensorDistribution = new int[wc._Sensors.Count][];
            int[][] percentLostPostureSensorDistribution = new int[wc._Sensors.Count][];            
            int[][] percentLostPostureSensorCounter= new int[wc._Sensors.Count][];                       

            int mitesCount=0;
            if (sannotation!=null)
                mitesCount=sannotation.Sensors.Count;
            int[] mitesSR= new int[mitesCount];
            int[] trueMitesSR = new int[mitesCount];
            int[][] modeMITesSR = new int[mitesCount][];
            Hashtable annotatedPostures=new Hashtable();


            #endregion


            #region Initialize Variables


            // int[] wocketsCounter = new int[wc._Sensors.Count];
            // int[] mitesCounter = new int[sannotation.Sensors.Count];
            int numSeconds = 0;
            for (int i = 0; (i < mitesCount); i++)
            {
                mitesSR[i]=0;
                trueMitesSR[i] = 0;
                modeMITesSR[i] = new int[1000];                
            }



            int mitesStartIndex=3+session.OverlappingActivityLists.Count;
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                wocketsSR[i]=0;
                trueWocketsSR[i] = 0;
                modeWocketsSR[i] = new int[1000];
                disconnected[i] = false;
                disconnectionDistribution[i] = new ArrayList();
                disconnectionTimer[i] = 0;
                timeLostPostureSensorDistribution[i] = new int[numPostures];
                percentLostPostureSensorDistribution[i] = new int[numPostures];
                //timeLostPostureSensorCounter[i] = new int[numPostures];
            }


            int wocketsStartIndex = mitesStartIndex + (ACCELEROMETER_STATISTICS_LENGTH * mitesCount);

            //no heart mites rate
            if (mitesCount == 0)
                wocketsStartIndex = wocketsStartIndex - 1;


            #endregion


            #region Initialize Annotations & Compute Descripte Statistics

            int numCategories = session.OverlappingActivityLists.Count;
            int currentAnnotation = 0;

            //Get the number of annotations
            int annotationsLength = session.Annotations.Count;

            //Get the overall session time
            double startTime = session.Annotations[0]._StartUnix;
            double endTime = session.Annotations[annotationsLength - 1]._EndUnix;

            string name = "";
            double duration_secs = 0.0;



            //Scan annotations and compute the duration min/max stats
            try
            {
                for (int c1 = 0; c1 < annotationsLength; c1++)
                {
                    name = session.Annotations[c1].Activities[0]._Name;
                    freq_per_class[name] = ((int)freq_per_class[name]) + 1;

                    //compute the duration of the label
                    duration_secs = (session.Annotations[c1]._EndUnix - session.Annotations[c1]._StartUnix) / 1000;

                    means_per_class[name] = ((double)means_per_class[name]) + duration_secs;

                    if (duration_secs < ((double)min_per_class[name]))
                        min_per_class[name] = duration_secs;

                    if (duration_secs > ((double)max_per_class[name]))
                        max_per_class[name] = duration_secs;
                }


                //compute the mean for each class
                for (int c2 = 0; c2 < means_per_class.Count; c2++)
                {
                    if (c2 < session.OverlappingActivityLists[0].Count)
                    {
                        name = session.OverlappingActivityLists[0][c2]._Name;
                        means_per_class[name] = ((double)means_per_class[name]) / ((int)freq_per_class[name]);
                    }
                }


                //Compute the standard deviation of durations for each class
                for (int c3 = 0; c3 < annotationsLength; c3++)
                {
                    name = session.Annotations[c3].Activities[0]._Name;

                    //compute the duration of the label
                    duration_secs = (session.Annotations[c3]._EndUnix - session.Annotations[c3]._StartUnix) / 1000;

                    std_per_class[name] = ((double)std_per_class[name]) + Math.Pow((duration_secs - ((double)means_per_class[name])), 2.0);
                }


                for (int c4 = 0; c4 < means_per_class.Count; c4++)
                {
                    if (c4 < session.OverlappingActivityLists[0].Count)
                    {
                        name = session.OverlappingActivityLists[0][c4]._Name;
                        std_per_class[name] = Math.Sqrt(((double)std_per_class[name]) / ((int)freq_per_class[name]));
                    }
                }

            }
            catch
            {  //The computation of the descriptive stats of annotations has failed
            }

            #endregion






            #region Open the Summary CSV File

            TextReader tr = new StreamReader(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITesSummaryData.csv");
            string line = "";
            tr.ReadLine();

            #endregion



         //Scan the Annotation Intervals and Summary File to Access the Sensors Statistics
         while ((line = tr.ReadLine()) != null)
         {
                
                //Read Line of Summary File (Sensor Reading)
                string[] tokens = line.Split(',');
                double currentTime = Convert.ToDouble(tokens[0]);
                string posture = tokens[2];
                string current_posture = "unknown";


                #region Determine if the sensor reading is within the annotation interval & compute its metrics
                
                
                try
                {

                    // If the sensor reading happens after the end of the annotation interval, 
                    // advance to the next annotation
                    if (  (currentAnnotation < session.Annotations.Count - 1) && 
                          (session.Annotations[currentAnnotation]._EndUnix < currentTime) )
                        currentAnnotation++;

                  
                    // If the sensor reading happens within the annotation interval,
                    // proceed to compute the metrics
                    if ((currentTime >= session.Annotations[currentAnnotation]._StartUnix) &&
                        (currentTime <= session.Annotations[currentAnnotation]._EndUnix))
                    {

                        #region Get the Label Name, Add it to the Hash Table, and Add the Annotated Seconds

                        // If we have more than one category,
                        // make the check for the second category (activities)
                        if (session.Annotations[currentAnnotation].Activities.Count > 1)
                        {
                            //If it is NOT a valid label, replace it for "unknown"
                            if ((session.Annotations[currentAnnotation].Activities[1]._Name == "none") || 
                                (session.Annotations[currentAnnotation].Activities[1]._Name == "")     || 
                                (session.Annotations[currentAnnotation].Activities[1]._Name == "-"))
                                     session.Annotations[currentAnnotation].Activities[1]._Name = "unknown";
                        }


                        //Make the check for all the first category (postures)
                        if ((session.Annotations[currentAnnotation].Activities[0]._Name == "none") || 
                            (session.Annotations[currentAnnotation].Activities[0]._Name == "")     || 
                            (session.Annotations[currentAnnotation].Activities[0]._Name == "-"))
                                   session.Annotations[currentAnnotation].Activities[0]._Name = "unknown";


                        //Get the name of the annotation label 
                        if (session.Annotations[currentAnnotation].Activities.Count > 1)                        
                            current_posture = session.Annotations[currentAnnotation].Activities[1]._Name + "_" + session.Annotations[currentAnnotation].Activities[0]._Name;
                        else
                            current_posture = session.Annotations[currentAnnotation].Activities[0]._Name;


                        // Search in the hash table the name of the current label,
                        // If it doesn't exists, add it to the list of annotated postures
                        // If it exists, add the number of seconds in the annotation
                        if (!annotatedPostures.ContainsKey(current_posture))
                            annotatedPostures.Add(current_posture, 1);
                        else
                        {
                            int annotatedSeconds = (int)annotatedPostures[current_posture] + 1;
                            annotatedPostures[current_posture] = annotatedSeconds;
                        }


                        #endregion

                    }




                     #region  Calculate quality metrics on data that has been annotated only
                

                        //If the sensor reading falls within the start-end of the session
                        if ((currentTime >= startTime) && (currentTime <= endTime))
                        {
                             #region Calculate Metrics


                                #region  mites SR
                                
                                for (int i = 0; (i < mitesCount); i++)
                                {
                                    int sr = Convert.ToInt32(tokens[mitesStartIndex + (ACCELEROMETER_STATISTICS_LENGTH * i)]);
                                    mitesSR[i] += sr;
                                    modeMITesSR[i][sr] = modeMITesSR[i][sr] + 1;
                                }

                            #endregion



                                #region  The number of seconds in a particular posture (adds to the global counter)

                                int currentPostureIndex = 0;
                                    currentPostureIndex = (int)postures[current_posture];
                                    timeLostPostureSensorCounter[currentPostureIndex] = timeLostPostureSensorCounter[currentPostureIndex] + 1;
                                
                                #endregion



                                #region  wockets SR

                                for (int i = 0; (i < wc._Sensors.Count); i++)
                                {

                                    //Compute Wockets Sampling Rate
                                    int sr = 0;
                                    try
                                    {
                                        sr = Convert.ToInt32(tokens[wocketsStartIndex + (ACCELEROMETER_STATISTICS_LENGTH * i)]);
                                        wocketsSR[i] += sr;
                                        modeWocketsSR[i][sr] = modeWocketsSR[i][sr] + 1;
                                    }
                                    catch (Exception e)
                                    {
                                    }
                                    
                                    
                                    //Add the samples collected per activity
                                    timeLostPostureSensorDistribution[i][currentPostureIndex] = timeLostPostureSensorDistribution[i][currentPostureIndex] + sr;


                                    //Compute the number of disconnections
                                    if (sr == 0)
                                    {
                                        zeroWocketsSR[i] = zeroWocketsSR[i] + 1;
                                        if (zeroWocketsSR[i] == 5)
                                        {
                                            disconnected[i] = true;
                                            numDisconnected[i] = numDisconnected[i] + 1;
                                        }
                                        disconnectionTimer[i]++;
                                    }
                                    else
                                    {
                                        if (disconnectionTimer[i] >= 5)
                                            disconnectionDistribution[i].Add(disconnectionTimer[i]);
                                        zeroWocketsSR[i] = 0;
                                        disconnected[i] = false;
                                        disconnectionTimer[i] = 0;
                                    }
                                }

                            #endregion


                                numSeconds++;


                            #endregion

                        } //end of the if

                   
                    #endregion

            
            }//end of try
            catch (Exception e)
            {
               //Launch exception when there is a index mistmatch in the ActivityIntervals.xml file
            }

        
          #endregion


         }//end of while


        
      
        #region  Calculate time lost, % data lost, burstiness



            #region Wockets Loss Calculation


            //The total session duration
            int totalSeconds = (int)((endTime - startTime) / 1000.0);
           

            //initialize variables
            int expectedMITesSamples = MITES_SR * totalSeconds;
            int[] wocketsSecondsLost = new int[wc._Sensors.Count];
            int[] mitesSecondsLost = new int[mitesCount];
            int[] wocketsPercentLost = new int[wc._Sensors.Count];
            int[] mitesPercentLost = new int[mitesCount];

     

            //Compute Loss Based on Sampling Rate and Number of Samples
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                int expectedWocketsSamples = wc._Sensors[i]._SamplingRate * totalSeconds;
                if (wocketsSR[i] < expectedWocketsSamples)
                {
                    wocketsSecondsLost[i] = (int)Math.Ceiling((double)(expectedWocketsSamples - wocketsSR[i]) / wc._Sensors[i]._SamplingRate);
                    wocketsPercentLost[i] = (int)(((double)wocketsSecondsLost[i] / (double)totalSeconds) * 100.0);
                }


                if (disconnectionTimer[i] >= 5)
                    disconnectionDistribution[i].Add(disconnectionTimer[i]);

            }


            #endregion Wockets Loss Calculation






          #region Wockets per Activity Loss Calculation


            //Scan through the list of annotated postures
            for (int i = 0; (i < timeLostPostureSensorCounter.Length); i++)
            {

                //Scan through the list of sensors
                for (int j = 0; (j < wc._Sensors.Count); j++)
                {

                    //expected samples
                    int expectedWocketsSamples = wc._Sensors[j]._SamplingRate * timeLostPostureSensorCounter[i];


                    //compute loss
                    if (timeLostPostureSensorDistribution[j][i] < expectedWocketsSamples)
                    {
                        timeLostPostureSensorDistribution[j][i] = (int)Math.Floor((expectedWocketsSamples - timeLostPostureSensorDistribution[j][i]) / (double)wc._Sensors[j]._SamplingRate);
                        percentLostPostureSensorDistribution[j][i] = (int)Math.Floor((((double)timeLostPostureSensorDistribution[j][i] / (double)timeLostPostureSensorCounter[i]) * 100.0));
                    }
                    else
                    {
                        timeLostPostureSensorDistribution[j][i] = 0;
                        percentLostPostureSensorDistribution[j][i] = 0;
                    }

                }

            }
           

            #endregion Wockets per Activity Loss Calculation





            #region MEAN and SD Calculation

            //Iterate through sensors
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
               numDisconnections[i]=disconnectionDistribution[i].Count;
               meanDisconnection[i] = 0;

               
               for (int j = 0; (j < disconnectionDistribution[i].Count); j++)               
                   meanDisconnection[i] = meanDisconnection[i] + (int)disconnectionDistribution[i][j];    
                

                if (numDisconnections[i]>0)
                    meanDisconnection[i] = (meanDisconnection[i]-1) / numDisconnections[i];
                

               for (int j = 0; (j < disconnectionDistribution[i].Count); j++)               
                   sdDisconnection[i] = sdDisconnection[i]  + (int) Math.Pow( ( (double) (int)disconnectionDistribution[i][j]- meanDisconnection[i]),2.0);


               if (disconnectionDistribution[i].Count > 1)
                   sdDisconnection[i] = (int)Math.Sqrt(sdDisconnection[i] / (disconnectionDistribution[i].Count - 1));
               else
                   sdDisconnection[i] = -1;

           }


           #endregion MEAN and SD Calculation






            #region MITes Loss Calculation
            

            for (int i = 0; (i < mitesCount); i++)
            {
               if (mitesSR[i] < expectedMITesSamples)
                   mitesSecondsLost[i] = (expectedMITesSamples - mitesSR[i]) / MITES_SR;
               
               mitesPercentLost[i] = (int)(((double)mitesSecondsLost[i] / (double)totalSeconds) * 100.0);
            }


            
            #endregion MITes Loss Calculation



            tr.Close();





            #region Percent Maxedout MITES


            int[] mitesMaxedOut = null;

            if (sannotation!=null)
                mitesMaxedOut=new int[sannotation.MaximumSensorID + 1];

            int[] mitesSamplesCount = null;
            
            if (sannotation!=null)
                mitesSamplesCount=new int[sannotation.MaximumSensorID + 1];
            
     

            try
            {
                MITesDecoder aMITesDecoder = new MITesDecoder();
                MITesLoggerReader aMITesLoggerReader = new MITesLoggerReader(aMITesDecoder, aDataDirectory + "\\" + MITES_SUBDIRECTORY);
                bool isData = true;
                do
                {
                    //decode the frame
                    int i = aMITesDecoder.GetSomeMITesData()[0].channel;
                    int x = aMITesDecoder.GetSomeMITesData()[0].x;
                    int y = aMITesDecoder.GetSomeMITesData()[0].y;
                    int z = aMITesDecoder.GetSomeMITesData()[0].z;
                    mitesSamplesCount[i] = mitesSamplesCount[i] + 1;
                    if ((x >= 1023) || (y >= 1023) || (z >= 1023))
                        mitesMaxedOut[i] = mitesMaxedOut[i] + 1;

                } while (isData = aMITesLoggerReader.GetSensorData(10));
            }catch
            {
            }


            #endregion



            #region Percent Maxed Out Wockets


            int[] maxedOut = new int[wc._Sensors.Count];
            int[] samplesCount = new int[wc._Sensors.Count];

          

            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                       
                wc._Sensors[i]._RootStorageDirectory = aDataDirectory+"\\"+ WOCKETS_SUBDIRECTORY + "\\data\\raw\\PLFormat\\";
                try
                {

                    int lastDecodedIndex = 0;
                    
                    
                    while (wc._Sensors[i].Load())
                    {

                        samplesCount[i] = samplesCount[i] + 1;

                        if (wc._Sensors[i]._Decoder._Head == 0)
                            lastDecodedIndex = wc._Sensors[i]._Decoder._Data.Length - 1;
                        else
                            lastDecodedIndex = wc._Sensors[i]._Decoder._Head - 1;   
                   

                        Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[lastDecodedIndex];
                        
                        
                        if ((data._X >= 1023) || (data._Y >= 1023) || (data._Z >= 1023))
                            maxedOut[i] = maxedOut[i] + 1;
                    
                    }
                }
                catch (Exception e)
                {
                }
     
            }

            #endregion Percent Maxed Out Wockets




            #region Write Results to HTML


            string summary = "<h3><Font Color=#585858>MITes and Wockets Data Loss, Disconnections and Maxing out Statistics </Font></h3><TABLE border=\"1\">\n";
            int numRows = wc._Sensors.Count - 1 + mitesCount;
            string[] rows = new string[numRows];
            string header="<TR>\n";
       

            string[] hlabels= new string[]{"Placement\\Metric","Data Loss (seconds)","% Data Loss","Num Disconnections","Mean Disconnection (seconds)","SD Disconnection (seconds)","Num Maxed Out","% Maxed Out"};            

            for (int i=0;(i<hlabels.Length);i++)
                header += "<TD><div align=\"center\"><strong>" + hlabels[i] + "</strong></div></TD>\n";
            

            header+="</TR>\n";
            summary+=header;
     


            #region Statistics Table for MITES

            for (int i = 0; (i < mitesCount); i++)
            {

                string row="<TR>\n";
                row += "<TD><div align=\"center\"><strong>MITes " + ((SXML.Sensor)sannotation.Sensors[i]).Location + "</strong></div></TD>\n";

                if (mitesPercentLost[i] >= 20)
                {
                    row += "<TD bgcolor=\"#FF0000\"><div align=\"center\">" + mitesSecondsLost[i].ToString() + "</div></TD>\n"; ;
                    row += "<TD bgcolor=\"#FF0000\"><div align=\"center\">" + mitesPercentLost[i].ToString() + "%" + "</div></TD>\n";
                }
                else
                {
                    row += "<TD><div align=\"center\">" + mitesSecondsLost[i].ToString() + "</div></TD>\n"; ;
                    row += "<TD><div align=\"center\">" + mitesPercentLost[i].ToString() + "%" + "</div></TD>\n"; 
                }


                int percent = 0;
                
                if (mitesSamplesCount[Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[i]).ID)]>0)
                    percent=(int)(((double)mitesMaxedOut[Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[i]).ID)] / (double)mitesSamplesCount[Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[i]).ID)]) * 100.0);
                row += "<TD><div align=\"center\">" + "N/A" + "</div></TD>\n";
                row += "<TD><div align=\"center\">" + "N/A" + "</div></TD>\n";
                row += "<TD><div align=\"center\">" + "N/A" + "</div></TD>\n";
                row += "<TD><div align=\"center\">" + mitesMaxedOut[Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[i]).ID)] + "</div></TD>\n";
                row += "<TD><div align=\"center\">" + percent + "% </div></TD>\n";
                row+="</TR>\n";                
                summary+=row;


            }


            summary += "<TR><TD colspan=\"8\"></TD></TR><TR>\n";



            #endregion



            #region Statistics Table for Wockets


            for (int i = 0; (i < wc._Sensors.Count); i++)
            {

                if (wc._Receivers[i] is Wockets.Receivers.RFCOMMReceiver)
                {
                    string row = "<TR>\n";
                    row += "<TD><div align=\"center\"><strong>Wocket " + wc._Sensors[i]._Location + "</strong></div></TD>\n";

                    if (wocketsPercentLost[i] >= 20)
                    {
                        row += "<TD bgcolor=\"#FF0000\"><div align=\"center\">" + wocketsSecondsLost[i].ToString() + "</div></TD>\n";
                        row += "<TD bgcolor=\"#FF0000\"><div align=\"center\">" + wocketsPercentLost[i].ToString() + "%" + "</div></TD>\n";
                    }
                    else
                    {
                        row += "<TD><div align=\"center\">" + wocketsSecondsLost[i].ToString() + "</div></TD>\n";
                        row += "<TD><div align=\"center\">" + wocketsPercentLost[i].ToString() + "%" + "</div></TD>\n";
                    }
                    row += "<TD><div align=\"center\">" + numDisconnections[i].ToString() + "</div></TD>\n";
                    row += "<TD><div align=\"center\">" + meanDisconnection[i].ToString() + "</div></TD>\n";
                    if (sdDisconnection[i] >= 0)
                        row += "<TD><div align=\"center\">" + sdDisconnection[i].ToString() + "</div></TD>\n";
                    else
                        row += "<TD><div align=\"center\">N/A</div></TD>\n";
                    row += "<TD><div align=\"center\">" + maxedOut[i].ToString() + "</div></TD>\n";
                    if (samplesCount[i] > 0)
                        row += "<TD><div align=\"center\">" + ((int)(((double)maxedOut[i] / (double)samplesCount[i]) * 100.0)).ToString() + "% </div></TD>\n";
                    else
                        row += "<TD><div align=\"center\">0% </div></TD>\n";
                    row += "</TR>\n";
                    summary += row;
                }

            }

            summary += "</TABLE>\n";


            summary = "<HTML><HEAD></HEAD><BODY>" + summary + "</BODY></HTML>";
            TextWriter tw = new StreamWriter(aDataDirectory + "\\result.html", true);
            tw.WriteLine(summary);
            tw.WriteLine("\n<p>&nbsp;</p>\n");



            #endregion



            #region Statistics per Activity Table


            summary = "<h3><Font Color=#585858>Wockets Data Loss by Posture and Activity Statistics</Font></h3><TABLE border=\"1\">\n";
            numRows =numPostures;
            rows = new string[numRows];
            header = "<TR>\n<td><div align=\"center\"><strong>Activity</strong></div></td><td><div align=\"center\"><strong>Posture</strong></div></td><td><strong>Total Seconds Annotated</strong></td>\n";
            for (int j = 0; (j < wc._Sensors.Count); j++)
                header += "<TD><div align=\"center\"><strong>" + wc._Sensors[j]._Location + "</br>(Seconds Lost|% Lost)</strong></div></TD>\n";
            header += "</TR>\n";
            summary += header;


     
           
            int m = 0;
            if (session.OverlappingActivityLists.Count > 1)
            {
                for (int i = 0; (i < session.OverlappingActivityLists[1].Count); i++)
                    for (int j = 0; (j < session.OverlappingActivityLists[0].Count); j++)
                    {
                        if (annotatedPostures.ContainsKey(session.OverlappingActivityLists[1][i]._Name + "_" + session.OverlappingActivityLists[0][j]._Name))
                        {
                            string row = "<TR>\n";
                            row += "<TD><div align=\"center\"><strong>" + session.OverlappingActivityLists[1][i]._Name + "</strong></div></TD><TD><div align=\"center\"><strong>" + session.OverlappingActivityLists[0][j]._Name + "</strong></div></TD>\n";
                            row += "<TD><div>" + (int)annotatedPostures[session.OverlappingActivityLists[1][i]._Name + "_" + session.OverlappingActivityLists[0][j]._Name] + "</TD>\n";
                            for (int r = 0; (r < wc._Sensors.Count - 1); r++)
                                if (percentLostPostureSensorDistribution[r][m] > 20)
                                    row += "<TD bgcolor=\"#FF0000\"><div align=\"center\">" + timeLostPostureSensorDistribution[r][m].ToString() + " | " + percentLostPostureSensorDistribution[r][m].ToString() + "%" + "</div></TD>\n";
                                else
                                    row += "<TD ><div align=\"center\">" + timeLostPostureSensorDistribution[r][m].ToString() + " | " + percentLostPostureSensorDistribution[r][m].ToString() + "%" + "</div></TD>\n";

                            row += "</TR>\n";
                            summary += row;
                        }
                        m++;
                    }
            }
            else
            {

                for (int j = 0; (j < session.OverlappingActivityLists[0].Count); j++)
                {
                    if (annotatedPostures.ContainsKey(session.OverlappingActivityLists[0][j]._Name))
                    {
                        string row = "<TR>\n";
                        row += "<TD><div align=\"center\"><strong>" + session.OverlappingActivityLists[0][j]._Name + "</strong></div></TD><TD><div align=\"center\"><strong>" + session.OverlappingActivityLists[0][j]._Name + "</strong></div></TD>\n";
                        row += "<TD><div>" + (int)annotatedPostures[session.OverlappingActivityLists[0][j]._Name] + "</TD>\n";
                        for (int r = 0; (r < wc._Sensors.Count); r++)
                            if (percentLostPostureSensorDistribution[r][m] > 20)
                                row += "<TD bgcolor=\"#FF0000\"><div align=\"center\">" + timeLostPostureSensorDistribution[r][m].ToString() + " | " + percentLostPostureSensorDistribution[r][m].ToString() + "%" + "</div></TD>\n";
                            else
                                row += "<TD ><div align=\"center\">" + timeLostPostureSensorDistribution[r][m].ToString() + " | " + percentLostPostureSensorDistribution[r][m].ToString() + "%" + "</div></TD>\n";

                        row += "</TR>\n";
                        summary += row;
                    }
                    m++;
                }
            }

            tw.WriteLine(summary + "</TABLE>\n");


            #endregion



            #region Other Sensors Statistics Table

            string[] ofiles = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY + "\\");

            if (ofiles.Length > 1)
            {

                summary = "<h3><Font Color=#585858>Other Sensors Statistics</Font></h3><TABLE border=\"1\">\n";
                header = "<TR>\n<td><div align=\"center\"><strong>Sensor Type</strong></div></td><td><div align=\"center\"><strong>Start Time</strong></div></td><td><strong>Data Present</strong></td><td><strong>Num Samples</strong></td><td><strong>Percent Loss</strong></td></TR>\n";
                header += "</TR>\n";
                summary += header;

                int expectedOxyconRecords = totalSeconds / 5;
                double oxyconLoss = 0;
                if (oxyconRecords < expectedOxyconRecords)
                    oxyconLoss = 100 - (((double)oxyconRecords / expectedOxyconRecords) * 100.0);

                summary += "<TR>\n<td><div align=\"center\"><strong>Oxycon</strong></div></td><td>" + (oxyconStart == null ? "&nbsp;" : oxyconStart) + "</td><td>" + (hasOxycon ? "Yes" : "No") + "</td><td>" + oxyconRecords + "</td><td>" + oxyconLoss.ToString("0") + "%</td></TR>\n";


                double sensewearLoss = 0;
                if (sensewearRecords < totalSeconds)
                    sensewearLoss = 100 - (((double)sensewearRecords / totalSeconds) * 100.0);

                summary += "<TR>\n<td><div align=\"center\"><strong>Sensewear</strong></div></td><td>" + (sensewearStart == null ? "&nbsp;" : sensewearStart) + "</td><td>" + (hasSensewear ? "Yes" : "No") + "</td><td>" + sensewearRecords + "</td><td>" + sensewearLoss.ToString("0") + "%</td></TR>\n";

                summary += "<TR>\n<td><div align=\"center\"><strong>Actigraph</strong></div></td><td>" + (actigraphStart == null ? "&nbsp;" : actigraphStart) + "</td><td>" + (hasActigraph ? "Yes" : "No") + "</td><td>";

                for (int r = 0; (r < actigraphData.Length); r++)
                {
                    summary += actigraphData[r].Count;
                    if (r != (actigraphData.Length - 1))
                        summary += " | ";
                }
                summary += "</td><td>";

                for (int r = 0; (r < actigraphData.Length); r++)
                {
                    double actigraphLoss = 0;
                    if (actigraphData[r].Count < totalSeconds)
                        actigraphLoss = 100 - (((double)actigraphData[r].Count / totalSeconds) * 100.0);
                    summary += actigraphLoss.ToString("0") + " %";
                    if (r != (actigraphData.Length - 1))
                        summary += " | ";
                }
                summary += "</td></TR>\n";

                double zephyrLoss = 0;
                if (zephyrRecords < totalSeconds)
                    zephyrLoss = 100 - (((double)zephyrRecords / totalSeconds) * 100.0);
                summary += "<TR>\n<td><div align=\"center\"><strong>Zephyr</strong></div></td><td>" + (zephyrStart == null ? "&nbsp;" : zephyrStart) + "</td><td>" + (hasZephyr ? "Yes" : "No") + "</td><td>" + zephyrRecords + "</td><td>" + zephyrLoss.ToString("0") + "%</td></TR>\n";

                double rtiLoss = 0;
                if (rtiRecords < totalSeconds)
                    rtiLoss = 100 - (((double)rtiRecords / totalSeconds) * 100.0);
                summary += "<TR>\n<td><div align=\"center\"><strong>RTI</strong></div></td><td>" + (rtiStart == null ? "&nbsp;" : rtiStart) + "</td><td>" + (hasRTI ? "Yes" : "No") + "</td><td>" + rtiRecords + "</td><td>" + rtiLoss.ToString("0") + "%</td></TR>\n";

                double columbiaLoss = 0;
                if (columbiaRecords < totalSeconds)
                    columbiaLoss = 100 - (((double)columbiaRecords / totalSeconds) * 100.0);
                summary += "<TR>\n<td><div align=\"center\"><strong>Columbia</strong></div></td><td>" + (columbiaStart == null ? "&nbsp;" : columbiaStart) + "</td><td>" + (hasColumbia ? "Yes" : "No") + "</td><td>" + columbiaRecords + "</td><td>" + columbiaLoss.ToString("0") + "%</td></TR>\n";

                double gpsLoss = 0;
                if (gpsRecords < totalSeconds)
                    gpsLoss = 100 - (((double)gpsRecords / totalSeconds) * 100.0);
                summary += "<TR>\n<td><div align=\"center\"><strong>GPS</strong></div></td><td>" + (gpsStart == null ? "&nbsp;" : gpsStart) + "</td><td>" + (hasGPS ? "Yes" : "No") + "</td><td>" + gpsRecords + "</td><td>" + gpsLoss.ToString("0") + "%</td></TR>\n";


                tw.WriteLine(summary + "</TABLE>\n");
            }

            #endregion



            tw.WriteLine("</HTML>");
            tw.Flush();
            tw.Close();


            #endregion



            #region Add the Annotations Summary


            tw = new StreamWriter(aDataDirectory + "\\result.html", true);
            
                summary = "";
                summary += "<h3><Font Color=#585858>Annotation Summary</Font></h3>\n";


                //If the annotation summary file exists, add it to current summary
                //If it doesn't exist, add the HTML to summary 
                if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationSummary.html"))
                {
                    try
                    {
                        TextReader ttr = new StreamReader(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationSummary.html");
                        summary += ttr.ReadToEnd();
                        ttr.Close();
                    }
                    catch (Exception ee)
                    { 
                    }
                }
                else
                {
                    
                    #region Create HTML content with stats for Autism Data

                    try
                    {
                        //Create Table & Headers
                        summary += "<table border=\"1\">\n";

                        TimeSpan ttime = new TimeSpan(0, 0, totalSeconds);
                        //Session total time
                        summary += "<tr> <td><div align=\"center\"><strong>Session Total Time (hh:mm:ss.ms)</strong></div></td>" +
                                        "<td>" + String.Format("{0:HH mm ss ff}", ttime) + "</td>" +
                                   "</tr>";


                        //Headers for annotation metrics
                        summary += "<tr>" + "<td><div align=\"center\"><strong> Label </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> Duration in Seconds </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> %Occurrence </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> Frequency </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> Mean (sec) </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> STD (sec) </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> Min (sec) </strong></div></td>" +
                                            "<td><div align=\"center\"><strong> Max (sec) </strong></div></td>" +
                                   "</tr>";


                        //Scan through labels
                        int total_secs_activity = 0;
                        double percent_duration = 0.0;




                        for (int j = 0; j < session.OverlappingActivityLists[0].Count; j++)
                        {

                            name = session.OverlappingActivityLists[0][j]._Name;

                            if (annotatedPostures.ContainsKey(name))
                            {
                                total_secs_activity = (int)annotatedPostures[name];
                                percent_duration = ((double)total_secs_activity / totalSeconds) * 100.0;

                                summary += "<tr>\n" +
                                       "<td><div align=\"center\"><strong>" + name + "</strong></div></td>" +
                                       "<td>" + total_secs_activity.ToString() + "</td>" +
                                       "<td>" + String.Format("{0:0.0}%", percent_duration) + "</td>" +
                                       "<td>" + String.Format("{0:0}", freq_per_class[name]) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", means_per_class[name]) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", std_per_class[name]) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", min_per_class[name]) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", max_per_class[name]) + "</td>" +
                                       "</tr>";
                            }
                            else
                            {
                                
                                summary += "<tr>\n" +
                                       "<td><div align=\"center\"><strong>" + name + "</strong></div></td>" +
                                       "<td>" + String.Format("{0:0}", 0)    + "</td>" +
                                       "<td>" + String.Format("{0:0.0}%", 0) + "</td>" +
                                       "<td>" + String.Format("{0:0}", 0)    + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", 0) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", 0) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", 0) + "</td>" +
                                       "<td>" + String.Format("{0:0.00}", 0) + "</td>" +
                                       "</tr>";
                            
                            }



                        }



                        //Close table
                        summary += "</table>";

                        //Generate the colors code for Autistic Labels
                        SaveLabelsColorsToFile(aDataDirectory, session.OverlappingActivityLists.Count, session.OverlappingActivityLists);

                    }
                    catch(Exception ee)
                    {
                        summary += "</HTML>";

                        try
                        {
                            if (tw != null)
                            {
                                tw.WriteLine(summary);
                                tw.Close();
                            }
                        }
                        catch(Exception ex)
                        {
                            //cannot write to file
                        }

                    }



                    #endregion
                    
                }


                summary += "</HTML>";

        #endregion 



        tw.WriteLine(summary);
        tw.Close();


       

    #endregion

    #endregion



 }

           


     //--- This colors assigned to the annotation bar in the viewer are protocol specific  ----
     //Check how I can make it more general
     private static void SaveLabelsColorsToFile(string aDataDirectory, int number_of_categories, ConcurrentActivityLists list_of_activities)
     {
            TextWriter labels_colors_csv;
            
            
            string label = "";
            string csv = "";
            string color = "";
            string argb = "";
            string category_name = "";


            //Load the list according the number of activity categories 
            for (int i = 0; i < number_of_categories; i++)
            {

                #region create a csv file for each category

                //if (i == 0)
                //{
                //    //Category 1
                //    if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_1.csv"))
                //    { File.Delete(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_1.csv"); }
                //    labels_colors_csv = new StreamWriter(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_1.csv");

                //    //Write headers
                //    labels_colors_csv.WriteLine("Category,Label,Color,ARGB");
                //}
                //else 
                //{
                //    //Category 2
                //    if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_2.csv"))
                //    { File.Delete(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_2.csv"); }
                //    labels_colors_csv = new StreamWriter(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_2.csv");

                //    //Write headers
                //    labels_colors_csv.WriteLine("Category,Label,Color,ARGB");
                //}

                if(File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_" + (i+1) + ".csv"))
                {
                    File.Delete(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_" + (i+1) + ".csv");
                }
                labels_colors_csv = new StreamWriter(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_" + (i+1) + ".csv");
                //Write Headers
                labels_colors_csv.WriteLine("Category,Label,Color,ARGB");

                #endregion


                #region assign color to each label

                if (list_of_activities.Count > i)
                {
                    category_name = list_of_activities[i]._Name;

                    //load labels for each category
                    for (int j = 0; j < list_of_activities[i].Count; j++)
                    {

                        label = list_of_activities[i][j]._Name;
                        csv = "";
                        color = "";
                        argb = "";


                        Color[,] labelcolors; int[,] labelrgb;
                        AssignLabelColors(out labelcolors, out labelrgb);


                        if (label.Trim().CompareTo("") != 0)
                        {
                            csv = category_name + "," + label + ",";

                           
                            if (label.CompareTo("unknown") == 0)
                            {
                                color = Color.Gainsboro.Name;
                                argb = Color.Gainsboro.ToArgb().ToString();

                            }
                           else
                            {
                                int color_id = 0;
                                Math.DivRem(j, NumberColorCategories, out color_id);
                                color = labelcolors[i, color_id].Name;
                                argb = labelrgb[i, color_id].ToString();

                            }

                            //save to file 
                            labels_colors_csv.WriteLine(csv + color + "," + argb);

                        }//ends if
                    }//ends for
                }
                #endregion 


                #region close csv files
                    labels_colors_csv.Flush();
                    labels_colors_csv.Close();
                #endregion

            } //ends if for overlapping activity lists


            
        }


     private static int NumberColorCategories = 10;
     private static void AssignLabelColors(out Color[,] labelcolors, out int[,] labelrgb)
     {
       //  labelcolors = new Color[2, NumberColorCategories];
       //  labelrgb = new int[2, NumberColorCategories];
         labelcolors = new Color[4, NumberColorCategories];
         labelrgb = new int[4, NumberColorCategories];

       ////Default Colors for First Category
         labelcolors[0, 0] = Color.Plum; labelrgb[0, 0] = -2252579;
         labelcolors[0, 1] = Color.Green; labelrgb[0, 1] = -424804561;
         labelcolors[0, 2] = Color.Orange; labelrgb[0, 2] = -256;
         labelcolors[0, 3] = Color.DeepSkyBlue; labelrgb[0, 3] = Color.FromArgb(200, Color.DeepSkyBlue).ToArgb();
         labelcolors[0, 4] = Color.Blue; labelrgb[0, 4] = 1677721855;
         labelcolors[0, 5] = Color.YellowGreen; labelrgb[0, 5] = -1264923342;
         labelcolors[0, 6] = Color.Violet; labelrgb[0, 6] = -1146130;
         labelcolors[0, 7] = Color.Turquoise; labelrgb[0, 7] = -12525360;
         labelcolors[0, 8] = Color.Tomato; labelrgb[0, 8] = -419495936;
         labelcolors[0, 9] = Color.Violet; labelrgb[0, 9] = -923893010;

         //Default Colors for Second Category
         labelcolors[1, 0] = Color.Plum; labelrgb[1, 0] = -2252579;
         labelcolors[1, 1] = Color.LightBlue; labelrgb[1, 1] = 838861055;
         labelcolors[1, 2] = Color.Blue; labelrgb[1, 2] = 1677721855;
         labelcolors[1, 3] = Color.YellowGreen; labelrgb[1, 3] = -1264923342;
         labelcolors[1, 4] = Color.Violet; labelrgb[1, 4] = -1146130;
         labelcolors[1, 5] = Color.Turquoise; labelrgb[1, 5] = -12525360;
         labelcolors[1, 6] = Color.Tomato; labelrgb[1, 6] = -419495936;
         labelcolors[1, 7] = Color.Orange; labelrgb[1, 7] = -256;
         labelcolors[1, 8] = Color.Green; labelrgb[1, 8] = -424804561;
         labelcolors[1, 9] = Color.Violet; labelrgb[1, 9] = -923893010;

         //Default Colors for Third category     
         labelcolors[2, 0] = Color.Green; labelrgb[2, 0] =-424804561;
         labelcolors[2, 1] = Color.Plum; labelrgb[2, 1] = -2252579;
         labelcolors[2, 2] = Color.Violet; labelrgb[2, 2] = -1146130;
         labelcolors[2, 3] = Color.Violet; labelrgb[2, 3] = -923893010;
         labelcolors[2, 4] = Color.YellowGreen; labelrgb[2, 4] = -1264923342;
         labelcolors[2, 5] = Color.Blue; labelrgb[2, 5] = 1677721855; 
         labelcolors[2, 6] = Color.Orange; labelrgb[2, 6] = -256;
         labelcolors[2, 7] = Color.Tomato; labelrgb[2, 7] = -419495936;
         labelcolors[2, 8] = Color.Turquoise; labelrgb[2, 8] = -12525360;
         labelcolors[2, 9] = Color.DeepSkyBlue; labelrgb[2, 9] = Color.FromArgb(200, Color.DeepSkyBlue).ToArgb(); 

         //Default Colors for Fourth category    
         labelcolors[3, 0] = Color.Orange; labelrgb[3, 0] = -256;         
         labelcolors[3, 1] = Color.Turquoise; labelrgb[3, 1] = -12525360;
         labelcolors[3, 2] = Color.Blue; labelrgb[3, 2] = 1677721855; 
         labelcolors[3, 3] = Color.Violet; labelrgb[3, 3] = -923893010;
         labelcolors[3, 4] = Color.Plum; labelrgb[3, 4] = -2252579;
         labelcolors[3, 5] = Color.Tomato; labelrgb[3, 5] = -419495936;
         labelcolors[3, 6] = Color.Violet; labelrgb[3, 6] = -1146130;
         labelcolors[3, 7] = Color.Green; labelrgb[3, 7] = -424804561;
         labelcolors[3, 8] = Color.DeepSkyBlue; labelrgb[3, 8] = Color.FromArgb(200, Color.DeepSkyBlue).ToArgb();
         labelcolors[3, 9] = Color.YellowGreen; labelrgb[3, 9] = -1264923342;
             

        

        

        
     }


        #endregion




     #region Declare Variables

     public static string MITES_SUBDIRECTORY = "mites";
        public static string WOCKETS_SUBDIRECTORY = "wockets";
        public static string OTHER_SUBDIRECTORY = "othersensors";
        public static string MERGED_SUBDIRECTORY = "merged";
        public static string ANNOTATION_SUBDIRECTORY = "annotation";
        public static string ANNOTATION_DIRECTORY = "annotation";
        public static string ANNOTATION_INTERVALS_FILE = "AnnotationIntervals.xml";
        private List<string> annotation_intervals_file_list = new List<string>();
        private List<string> annotation_subdirectory_list = new List<string>();

        //JPN: Declare array for storing previous summary data value for PLOT WRAC
        private static string[] prevWRACPlotDataLine;

        //JPN: Declare array for storing previous summary data value for PLOT WFAC
        private static string[] prevWFACPlotDataLine; 

        //JPN: TEMP: store previous SR for PLOT WRAC
        private static string[] prevWRACPlotSampleCount;

        public static string CSVProgress = "";
        public static bool hasActigraph = false;
        public static bool hasOxycon = false;
        public static bool hasSensewear = false;
        public static bool hasRTI = false;
        public static bool hasZephyr = false;
        public static bool hasColumbia = false;
        public static bool hasGPS = false;

        public static int actigraphRecords = 0;
        public static int oxyconRecords = 0;
        public static int sensewearRecords = 0;
        public static int rtiRecords = 0;
        public static int zephyrRecords = 0;
        public static int columbiaRecords = 0;
        public static int gpsRecords = 0;


        public static string summaryStart = null;
        public static string actigraphStart = null;
        public static string oxyconStart = null;
        public static string sensewearStart = null;
        public static string rtiStart = null;
        public static string zephyrStart = null;
        public static string columbiaStart = null;
        public static string gpsStart = null;


        //Actigraph
        static TextWriter[] actigraphCSV;
        static Hashtable[] actigraphData;
        static string[] actigraphType;
        public static string[] prevActLine;
        public static string[] prevActXYZ;
        public static int prevActAC_XYZ;
        

        //Actigraph Raw Data Constants
        public static double ACTRANGE = 12;
        public static double WKTBITS = 10;
        public static double WKTRANGE = Math.Pow(2, WKTBITS);
        public static double ACTWKTNORM = ACTRANGE / WKTRANGE;

       

        #endregion



        #region Generate the Summary Files

        private static double[] prevUnixTime;
        private static double[] summaryStartUnixTime;

        private static TextWriter[] wWFACSummaryCSV;
        private static Hashtable[] wWFACData;

        //JPN: Declare textwriter array for outputting WRAC values
        private static TextWriter[] wWRACSummaryCSV;

        //JPN: Declare array to store the running total of AUC summations for WRAC calculations
        private static int[] wWRACSummation;

        //JPN: Declare hashtable array for storing WRAC sampling rates for each minute
        static Hashtable[] wWRACSamplingRate;

        //JPN: Declare hashtable array for storing Wockets Raw Activity Count (WRAC) values to be inserted into CSV file
        static Hashtable[] wWRACData;
        
                public static void toCSV(string aDataDirectory, string masterDirectory, int maxControllers, string[] filter)
        {


            #region Declare Variables

            //double previousUnixTime = -1;


            //------ Annotation Variables ------//


            /**** MITes,wockets Variables ****/

            //Variables that average raw values
            int[] averageX = null;
            int[] averageY = null;
            int[] averageZ = null;

            int[] averageRawX = null;
            int[] averageRawY = null;
            int[] averageRawZ = null;

            //variables for older activity count calculation
            int[] prevX = null;
            int[] prevY = null;
            int[] prevZ = null;
            int[] acCounters = null;

            //Variables to store raw data,running mean and areas under curve
            int[, ,] rawData = null; //channel,axis ->data            
            long[,] timeData = null; //channel ->timestamp

            int[,] AUC = null;
            double[] VMAG = null;
            int[] head = null; //channel ->pointer to the head (circular)
            double[] RMX = null;
            double[] RMY = null;
            double[] RMZ = null;
            int[] RMSize = null;


            //CSV files that store data                    
            TextWriter[] activityCountCSVs = null; //old activity count files
            TextWriter[] aucCSVs = null; //AUC files
            TextWriter[] vmagCSVs = null; //AUC files
            TextWriter[] rmCSVs = null; //Running mean files
            TextWriter[] samplingCSVs = null; //Sample Rate CSV       
            TextWriter[] averagedRaw = null;  //Raw signal CSV

            TextWriter[] wactivityCountCSVs = null; //old activity count files
            TextWriter[] waucCSVs = null; //AUC files
            TextWriter[] wvmagCSVs = null; //AUC files
            TextWriter[] wrmCSVs = null; //Running mean files
            TextWriter[] wsamplingCSVs = null; //Sample Rate CSV       
            TextWriter[] waveragedRaw = null;  //Raw signal CSV




            //Variables that average raw values
            int[] waverageX = null;
            int[] waverageY = null;
            int[] waverageZ = null;
            int[] waverageRawX = null;
            int[] waverageRawY = null;
            int[] waverageRawZ = null;

            //variables for older activity count calculation
            int[] wprevX = null;
            int[] wprevY = null;
            int[] wprevZ = null;
            int[] wacCounters = null;

            //JPN: Declare array to track number of samples per minute for WRAC
            int[] wWRACCounterMinute = null;

            //Variables to store raw data,running mean and areas under curve
            int[, ,] wrawData = null; //channel,axis ->data            
            long[,] wtimeData = null; //channel ->timestamp
            int[,] wAUC = null;

            //JPN: Declare array to store combined AUC used in calculating WRAC
            int[] wAUCXYZ = null;

            double[] wVMAG = null;
            int[] whead = null; //channel ->pointer to the head (circular)
            double[] wRMX = null;
            double[] wRMY = null;
            double[] wRMZ = null;
            int[] wRMSize = null;


            TextWriter masterCSV;      //Master CSV
            TextWriter hrCSV = null;       //HR CSV


            //Zephyr
            TextWriter zephyrCSV = null;
            TextReader zephyrReader = null;
            double zephyrUnixTime = 0;
            DateTime zephyrTime = new DateTime();
            Hashtable zephyrData = new Hashtable();

            //Omron
            TextWriter omronCSV = null;
            TextReader omronReader = null;
            double omronUnixTime = 0;
            DateTime omronTime = new DateTime();
            Hashtable omronData = new Hashtable();

            //Oxycon 
            TextWriter oxyconCSV = null;
            TextReader oxyconReader = null;
            double oxyconUnixTime = 0;
            DateTime oxyconTime = new DateTime();
            Hashtable oxyconData = new Hashtable();


            //Sensewear
            TextWriter sensewearCSV = null;
            TextReader sensewearReader = null;
            int sensewearSR = 0;
            double sensewearTrans = 0;
            double sensewearLong = 0;
            double sensewearForAcc = 0;
            DateTime sensewearTime = new DateTime();
            DateTime prevSensewearTime = new DateTime();
            double sensewearUnixTime = 0;

            //Sensewear vanderbilt
            string vanderbiltSensewearDataLine = "";
            Hashtable sensewearData = new Hashtable();

            //Columbia
            TextWriter columbiaCSV = null;
            TextReader columbiaReader = null;
            double columbiaX = 0;
            double columbiaY = 0;
            double columbiaZ = 0;
            double columbiaFlow = 0;
            int columbiaValve = 0;
            double columbiaUnixTime = 0;
            DateTime columbiaTime = new DateTime();
            Hashtable columbiaData = new Hashtable();

            //GPS
            TextWriter gpsCSV = null;
            TextReader gpsReader = null;
            double gpsLatitude = 0;
            double gpsLongitude = 0;
            double gpsSpeed = 0;
            double gpsAltitude = 0;
            double gpsUnixTime = 0;
            DateTime gpsTime = new DateTime();
            Hashtable gpsData = new Hashtable();

            //RTI
            TextWriter rtiCSV = null;
            TextReader rtiReader = null;
            double rtiX = 0;
            double rtiY = 0;
            double rtiZ = 0;
            double[] rtiPrevX = new double[5];
            double[] rtiPrevY = new double[5];
            double[] rtiPrevZ = new double[5];
            int[] rtiPrevCounts = new int[5];
            double rtiRMX = 0;
            double rtiRMY = 0;
            double rtiRMZ = 0;
            int rtiTotalCount = 0;

            double rtiUnixTime = 0;
            DateTime rtiTime = new DateTime();
            Hashtable rtiData = new Hashtable();



            //RT3
            TextWriter rt3CSV = null;
            TextReader rt3Reader = null;
            int rt3SR = 0;
            double rt3UnixTime = 0;
            DateTime rt3Time = new DateTime();
            Hashtable rt3Data = new Hashtable();
            string rt3_dataline = "";





            int sumHR = 0;
            int hrCount = 0;
            string[] tokens;


            //CSV Files headers
            string csv_line1 = "UnixTimeStamp,TimeStamp,X,Y,Z";
            string csv_line2 = "UnixTimeStamp,TimeStamp,Sampling";
            string csv_line3 = "";
            string csv_line4 = "";
            string csv_line5 = "";
            string csv_line6 = "UnixTimeStamp,TimeStamp,VectorMagnitude";
            string hr_csv_header = "UnixTimeStamp,TimeStamp,HR";
            string actigraph_csv_header = "UnixTimeStamp,TimeStamp,Actigraph";
            string summary_csv_header = "UnixTimeStamp,TimeStamp,ActivityCount";
            string actigraph_csv_header_gt1m = "UnixTimeStamp,TimeStamp,ActigraphX,ActigraphY";
            string actigraph_csv_header_gtx = "UnixTimeStamp,TimeStamp,ActigraphX,ActigraphY,ActigraphZ";
            string sensewear_csv_header = "UnixTimeStamp,TimeStamp,SensewearSR,Sensewear_AVTranAcc,Senserwear_AVLongAcc,Sensewear_AVForAcc";
            string sensewear_csv_header_vanderbilt = "UnixTimeStamp,TimeStamp,SensewearSR,Sensewear_numpeaks_accelerometer_transverse,Sensewear_numpeaks_accelerometer_longitudinal,Sensewear_heat_flux_average_original_rate,Sensewear_skin_temp_average_original_rate,Sensewear_transverse_accelerometer_average,Sensewear_longitudinal_accelerometer_average,Sensewear_cover_temp_average,Sensewear_transverse_accelerometer_MAD_graphable,Sensewear_longitudinal_accelerometer_MAD_graphable,Sensewear_STEPS,Sensewear_gsr_average,Sensewear_energy_expenditure_per_minute";
            string zephyr_csv_header = "UnixTimeStamp,TimeStamp,ZephyrHeart Rate Data,ZephyrECG - Amplitude Data,ZephyrECG - Noise Data,ZephyrRES - Breathing Wave Amplitude (V) Data,ZephyrRES - Respiration Rate Data,ZephyrTEM - Skin Temperature Data,ZephyrBAT - Battery Voltage (V) Data,ZephyrPOS - Posture Data,ZephyrACC - Activity Data,ZephyrACC - Peak Acceleration (g) Data,ZephyrACC - Vertical Acc Minimum (g) Data,ZephyrACC - Vertical Acc Peak (g) Data,ZephyrACC - Lateral Acc Minimum (g) Data,ZephyrACC - Lateral Acc Peak (g) Data,ZephyrACC - Sagittal Acc Minimum (g) Data,ZephyrACC - Sagittal Acc Peak (g)";
            string oxycon_csv_header = "UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2,OxyconVO2kg,OxyconMET,OxyconEE,OxyconRER";
            string omron_csv_header = "UnixTimeStamp,TimeStamp,Steps";
            string columbia_csv_header = "UnixTimeStamp,TimeStamp,ColumbiaX,ColumbiaY,ColumbiaZ,ColumbiaFlow,ColumbiaValve";
            string gps_csv_header = "UnixTimeStamp,TimeStamp,GPSLatitude,GPSLongitude,GPSSpeed,GPSAltitude";
            string rti_csv_header = "UnixTimeStamp,TimeStamp,RTIX,RTIY,RTIZ,RTI_AUC_X,RTI_AUC_Y,RTI_AUC_Z,RTI_AUC_XYZ";
            string rt3_csv_header = "UnixTimeStamp,TimeStamp,RT3_SR,RT3_Total_Calories,RT3_Activity_Calories,RT3_VM,RT3_ActCntsX,RT3_ActCntsY,RT3_ActCntsZ";
            string master_csv_header = "UnixTimeStamp,TimeStamp";

            //files found
            bool sensewearFound = false;
            bool sensewearVanderbiltFound = false;
            bool zephyrFound = false;
            bool oxyconFound = false;
            bool omronFound = false;
            bool columbiaFound = false;
            bool gpsFound = false;
            bool rtiFound = false;
            bool rt3Found = false;


            //Sensor Offsets
            //double actigraphOffset = 0;
            double sensewearOffset = 0;
            double zephyrOffset = 0;
            double columbiaOffset = 0;
            double rtiOffset = 0;
            double oxyconOffset = 0;
            //for upto 6 actigraphs
            double[] actigraphOffset = new double[] { 0, 0, 0, 0, 0, 0 };


            double annotationsOffset = 0;
            double mitesOffset = 0;
            double gpsOffset = 0;

            DateTime[] actigraphEndTimes = new DateTime[6];
            DateTime[] actigraphStartTimes = new DateTime[6];

            if (other_sensors_form != null)
            {
                //actigraphOffset = other_sensors_form._ActigraphSeconds;
                sensewearOffset = other_sensors_form._SensewearSeconds;
                zephyrOffset = other_sensors_form._ZephyrSeconds;
                columbiaOffset = other_sensors_form._ColumbiaSeconds;
                rtiOffset = other_sensors_form._RTISeconds;
                oxyconOffset = other_sensors_form._OxyconSeconds;

                annotationsOffset = other_sensors_form._AnnotationsSeconds;
                mitesOffset = other_sensors_form._MitesSeconds;
                gpsOffset = other_sensors_form._GpsSeconds;

                //actigraph offsets - upt0 6 actigraphs
                int totalActigraphs = other_sensors_form._TotalActigraphs;
                for (int i = 0; i < totalActigraphs; i++)
                {
                    actigraphOffset[i] = other_sensors_form._ActigraphSeconds[i];
                }

                actigraphEndTimes = new DateTime[totalActigraphs];
                actigraphStartTimes = new DateTime[totalActigraphs];
            }


            #endregion


            #region Load Wockets Configuration File

            WocketsConfiguration configuration = new WocketsConfiguration();
            try
            {
                configuration.FromXML(aDataDirectory + "\\wockets\\Configuration.xml");
            }
            catch
            {
                //   configuration.FromXML(aDataDirectory + "\\Configuration.xml");
            }
            CurrentWockets._Configuration = configuration;


            #endregion Load Wockets Configuration File


            #region Read RTI data
            string[] file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-rti*.csv");




            string rti_line = "";

            try
            {
                if (file.Length == 1)
                {
                    if (CSVProgress == "")
                        CSVProgress = "Processing RTI Data";
                    rtiReader = new StreamReader(file[0]);
                    DateTime rtiOriginTime = new DateTime();
                    bool rtiOriginFound = false;
                    if (File.Exists(aDataDirectory + "\\" + OTHER_SUBDIRECTORY + "\\RTISynchronizationTime.txt"))
                    {
                        TextReader rtiOriginTR = new StreamReader(aDataDirectory + "\\" + OTHER_SUBDIRECTORY + "\\RTISynchronizationTime.txt");
                        string originRTI = rtiOriginTR.ReadLine();

                        try
                        {
                            tokens = originRTI.Split(',');
                            tokens = tokens[0].Split('.');
                            rtiOriginTR.Close();
                            UnixTime.GetDateTime(Convert.ToInt64(tokens[0]), out rtiOriginTime);
                        }
                        catch (Exception e)
                        {
                            throw new Exception("RTI Synchronization: Parsing failed " + e.Message);
                        }

                        rtiOriginTime = rtiOriginTime.AddSeconds(rtiOffset);
                        rtiOriginFound = true;
                    }

                    //skip first 25 lines
                    for (int k = 0; (k < 7); k++)
                        rti_line = rtiReader.ReadLine();

                    string prevRTIKey = "";
                    double xRTI = 0;
                    double yRTI = 0;
                    double zRTI = 0;
                    double xAUCRTI = 0;
                    double yAUCRTI = 0;
                    double zAUCRTI = 0;
                    int rtiCount = 0;
                    int rtiPrevIndex = 0;
                    int runningMeanSize = 0;
                    int rti_sample_counter = 0;
                    rtiTime = rtiOriginTime;
                    while ((rti_line = rtiReader.ReadLine()) != null)
                    {
                        tokens = rti_line.Split(',');
                        if (tokens.Length >= 4)
                        {

                            if (!rtiOriginFound)
                            {
                                string[] dateTokens = tokens[0].Split(new char[] { ' ', '\t' });
                                string[] timeTokens = null;
                                if (dateTokens[1].Contains("/"))
                                    timeTokens = dateTokens[0].Split('.');
                                else
                                    timeTokens = dateTokens[1].Split('.');

                                int mseconds = Convert.ToInt32(timeTokens[1]);
                                timeTokens = timeTokens[0].Split(':');

                                if (dateTokens[1].Contains("/"))
                                    dateTokens = dateTokens[1].Split('/');
                                else
                                    dateTokens = dateTokens[0].Split('/');
                                if (dateTokens[2].Length == 2)
                                    dateTokens[2] = "20" + dateTokens[2];
                                rtiTime = new DateTime(Convert.ToInt32(dateTokens[2]), Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]), mseconds);
                                rtiTime = rtiTime.AddSeconds(rtiOffset);
                            }
                            if ((rtiOriginFound) && (rti_sample_counter == 20))
                            {
                                rtiTime = rtiTime.AddSeconds(1.0);
                                rti_sample_counter = 0;
                            }
                            rti_sample_counter++;


                            //if (isPM)
                            //    rtiTime.AddHours(12.0);


                            rtiUnixTime = UnixTime.GetUnixTime(rtiTime);
                            string rtiKey = rtiTime.Year + "-" + rtiTime.Month + "-" + rtiTime.Day + "-" + rtiTime.Hour + "-" + rtiTime.Minute + "-" + rtiTime.Second;
                            string rtiLine = "";
                            if (rtiStart == null)
                                rtiStart = rtiTime.Year + "/" + rtiTime.Month + "/" + rtiTime.Day + " " + rtiTime.Hour + ":" + rtiTime.Minute + ":" + rtiTime.Second;

                            if (prevRTIKey == "")
                                prevRTIKey = rtiKey;


                            //save previous data
                            if (prevRTIKey != rtiKey)
                            {

                                if (runningMeanSize >= 5)
                                {
                                    rtiLine += ((double)(xRTI / (double)rtiCount)).ToString("0.00");
                                    rtiLine += ",";
                                    rtiLine += ((double)(yRTI / (double)rtiCount)).ToString("0.00");
                                    rtiLine += ",";
                                    rtiLine += ((double)(zRTI / (double)rtiCount)).ToString("0.00");
                                    rtiLine += ",";
                                    rtiLine += (xAUCRTI).ToString("0.00");
                                    rtiLine += ",";
                                    rtiLine += (yAUCRTI).ToString("0.00");
                                    rtiLine += ",";
                                    rtiLine += (zAUCRTI).ToString("0.00");
                                    rtiLine += ",";
                                    rtiLine += ((double)(Math.Abs(xAUCRTI) + Math.Abs(yAUCRTI) + Math.Abs(zAUCRTI))).ToString("0.00");

                                }
                                else
                                    rtiLine += ",,,,,,";

                                rtiRMX = 0;
                                rtiRMY = 0;
                                rtiRMZ = 0;
                                for (int m = 0; (m < 5); m++)
                                {
                                    rtiRMX += rtiPrevX[m];
                                    rtiRMY += rtiPrevY[m];
                                    rtiRMZ += rtiPrevZ[m];
                                    rtiTotalCount += rtiPrevCounts[m];
                                }

                                rtiRMX = rtiRMX / rtiTotalCount;
                                rtiRMY = rtiRMY / rtiTotalCount;
                                rtiRMZ = rtiRMZ / rtiTotalCount;

                                rtiPrevCounts[rtiPrevIndex] = rtiCount;
                                rtiPrevX[rtiPrevIndex] = xRTI;
                                rtiPrevY[rtiPrevIndex] = yRTI;
                                rtiPrevZ[rtiPrevIndex++] = zRTI;
                                rtiPrevIndex = (rtiPrevIndex % 5);


                                if (runningMeanSize < 5)
                                    runningMeanSize++;


                                if (rtiData.Contains(prevRTIKey) == false)
                                    rtiData.Add(prevRTIKey, rtiLine);

                                xRTI = 0;
                                yRTI = 0;
                                zRTI = 0;
                                rtiCount = 0;
                                xAUCRTI = 0;
                                yAUCRTI = 0;
                                zAUCRTI = 0;
                                rtiTotalCount = 0;
                            }


                            xRTI += Convert.ToDouble(tokens[1]);
                            yRTI += Convert.ToDouble(tokens[2]);
                            zRTI += Convert.ToDouble(tokens[3]);
                            xAUCRTI += Math.Abs(Convert.ToDouble(tokens[1]) - rtiRMX);
                            yAUCRTI += Math.Abs(Convert.ToDouble(tokens[2]) - rtiRMY);
                            zAUCRTI += Math.Abs(Convert.ToDouble(tokens[3]) - rtiRMZ);
                            rtiCount++;
                            prevRTIKey = rtiKey;
                        }
                    }

                    rtiFound = true;

                }
            }
            catch (Exception e)
            {
                throw new Exception("RTI: Parsing failed " + e.Message);
            }


            hasRTI = (rtiData.Count > 0);
            rtiRecords = rtiData.Count;
            #endregion Read RTI data


            #region Read Columbia data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-columbia*.csv");

            string columbia_line = "";
            try
            {
                if (file.Length == 1)
                {
                    if (CSVProgress == "")
                        CSVProgress = "Processing Columbia Data";
                    columbiaReader = new StreamReader(file[0]);

                    //skip first 25 lines
                    for (int k = 0; (k < 25); k++)
                        columbia_line = columbiaReader.ReadLine();


                    while ((columbia_line = columbiaReader.ReadLine()) != null)
                    {
                        tokens = columbia_line.Split(',');
                        if (tokens.Length == 14)
                        {

                            string[] dateTokens = tokens[1].Split('/');
                            string[] timeTokens = tokens[2].Split(':');
                            columbiaTime = new DateTime(Convert.ToInt32("20" + dateTokens[2]), Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));

                            // if (columbiaOffset > 0)
                            columbiaTime = columbiaTime.AddSeconds(columbiaOffset);

                            columbiaUnixTime = UnixTime.GetUnixTime(columbiaTime);
                            string columbiaKey = columbiaTime.Year + "-" + columbiaTime.Month + "-" + columbiaTime.Day + "-" + columbiaTime.Hour + "-" + columbiaTime.Minute + "-" + columbiaTime.Second;
                            string columbiaLine = "";

                            if (columbiaStart == null)
                                columbiaStart = columbiaTime.Year + "/" + columbiaTime.Month + "/" + columbiaTime.Day + " " + columbiaTime.Hour + ":" + columbiaTime.Minute + ":" + columbiaTime.Second;

                            if (tokens[3].Length > 0)
                                columbiaLine += Convert.ToDouble(tokens[3]);
                            columbiaLine += ",";
                            if (tokens[4].Length > 0)
                                columbiaLine += Convert.ToDouble(tokens[4]);
                            columbiaLine += ",";
                            if (tokens[5].Length > 0)
                                columbiaLine += Convert.ToDouble(tokens[5]);
                            columbiaLine += ",";
                            if (tokens[6].Length > 0)
                                columbiaLine += Convert.ToDouble(tokens[6]);
                            columbiaLine += ",";
                            if (tokens[7].Length > 0)
                                columbiaLine += Convert.ToInt32(tokens[7]);

                            if (columbiaData.Contains(columbiaKey) == false)
                                columbiaData.Add(columbiaKey, columbiaLine);
                        }
                    }

                    columbiaFound = true;
                    hasColumbia = true;
                    columbiaRecords = columbiaData.Count;
                }
            }
            catch (Exception e)
            {
                throw new Exception("Columbia: Parsing failed " + e.Message);
            }
            #endregion Read Columbia data


            #region Read GPS data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-gps*.csv");

            string gps_line = "";
            try
            {
                if (file.Length == 1)
                {
                    if (CSVProgress == "")
                        CSVProgress = "Processing GPS Data";
                    gpsReader = new StreamReader(file[0]);

                    //skip first line
                    gps_line = gpsReader.ReadLine();


                    while ((gps_line = gpsReader.ReadLine()) != null)
                    {
                        tokens = gps_line.Split(',');
                        if (tokens.Length == 7)
                        {

                            string[] dateTokens = tokens[1].Split('-');
                            string[] timeTokens = tokens[2].Split(':');
                            gpsTime = new DateTime(Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(dateTokens[2]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));

                            //add gps offset
                            gpsTime = gpsTime.AddSeconds(gpsOffset);

                            gpsUnixTime = UnixTime.GetUnixTime(gpsTime);


                            string gpsKey = gpsTime.Year + "-" + gpsTime.Month + "-" + gpsTime.Day + "-" + gpsTime.Hour + "-" + gpsTime.Minute + "-" + gpsTime.Second;
                            string gpsLine = "";

                            if (gpsStart == null)
                                gpsStart = gpsTime.Year + "/" + gpsTime.Month + "/" + gpsTime.Day + " " + gpsTime.Hour + ":" + gpsTime.Minute + ":" + gpsTime.Second;

                            if (tokens[3].Length > 0)
                                gpsLine += Convert.ToDouble(tokens[3]);
                            gpsLine += ",";
                            if (tokens[4].Length > 0)
                                gpsLine += Convert.ToDouble(tokens[4]);
                            gpsLine += ",";
                            if (tokens[5].Length > 0)
                                gpsLine += Convert.ToDouble(tokens[5]);
                            gpsLine += ",";
                            if (tokens[6].Length > 0)
                                gpsLine += Convert.ToDouble(tokens[6]);
                            // gpsLine += ",";

                            if (gpsData.Contains(gpsKey) == false)
                                gpsData.Add(gpsKey, gpsLine);
                        }
                    }

                    gpsFound = true;
                    hasGPS = true;
                    gpsRecords = gpsData.Count;
                }
            }
            catch (Exception e)
            {
                throw new Exception("GPS: Parsing failed " + e.Message);
            }
            #endregion Read GPS data


            #region Read Omron data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-omron.csv");
            string omron_line = "";
            try
            {
                if (file.Length == 1)
                {
                    if (CSVProgress == "")
                        CSVProgress = "Processing Omron Data";
                    omronReader = new StreamReader(file[0]);
                    for (int j = 0; (j < 3); j++)
                        omron_line = omronReader.ReadLine();//skip first 3 lines
                    omron_line = omronReader.ReadLine();
                    tokens = omron_line.Split(',');
                    string[] omronDate = tokens[0].Split('/');
                    for (int i = 0; (i < 24); i++)
                    {
                        omronTime = new DateTime(Convert.ToInt32(omronDate[2]), Convert.ToInt32(omronDate[0]), Convert.ToInt32(omronDate[1]), i, 59, 59);
                        string omronKey = omronTime.Year + "-" + omronTime.Month + "-" + omronTime.Day + "-" + omronTime.Hour + "-" + omronTime.Minute + "-" + omronTime.Second;
                        omronData.Add(omronKey, Convert.ToInt32(tokens[i + 7]));
                    }
                    omronFound = true;
                }

            }
            catch (Exception e)
            {
                throw new Exception("Omron: Parsing failed " + e.Message);
            }
            #endregion Read Omron data


            #region Read Actigraph data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-actigraph*.csv");
            actigraphCSV = new TextWriter[file.Length];
            actigraphData = new Hashtable[file.Length];
            actigraphType = new string[file.Length];
            prevActLine = new string[file.Length];
            for (int i = 0; i < prevActLine.Length; i++)
            {
                prevActLine[i] = "0,0,0";
            }
            prevActXYZ = new string[3];
            for (int i = 0; i < prevActXYZ.Length; i++)
            {
                prevActXYZ[i] = "0";
            }

            try
            {
                for (int i = 0; (i < file.Length); i++)
                    actigraphData[i] = new Hashtable();
                for (int i = 0; (i < file.Length); i++)
                {
                    if (CSVProgress == "")
                        CSVProgress = "Processing Actigraph Data " + (i + 1);
                    TextReader actigraphReader = null;
                    string actigraph_line = "";
                    double actigraphUnixTime = 0;
                    DateTime actigraphTime = new DateTime();
                    DateTime actigraphEndTime = new DateTime();

                    actigraphReader = new StreamReader(file[i]);
                    actigraph_line = actigraphReader.ReadLine();//read first line
                    if (actigraph_line.Contains("\""))
                    {
                        actigraph_line = actigraph_line.Replace("\"", "");
                    }
                    if (actigraph_line.Contains("ActiSoft"))
                    {
                        actigraphType[i] = "ActiSoft";
                        Match m;
                        do
                        {
                            actigraph_line = actigraphReader.ReadLine();
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            tokens = actigraph_line.Split(',');
                            m = Regex.Match(tokens[0].Trim(), "^[0-9]+/[0-9]+/[0-9]+$");
                        } while (m.Success == false);


                        tokens = actigraph_line.Split(',');
                        Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));


                        //if (actigraphOffset > 0)
                        actigraphTime = actigraphTime.AddSeconds(actigraphOffset[i]);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            tokens = actigraph_line.Split(',');
                            if (tokens[0].Length > 1)
                            {
                                m1 = Regex.Match(tokens[0], "([0-9]+)/([0-9]+)/([0-9]+)");
                                m2 = Regex.Match(tokens[1], "([0-9]+):([0-9]+):([0-9]+)");
                                actigraphTime = new DateTime(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                                //if (actigraphOffset > 0)
                                actigraphTime = actigraphTime.AddSeconds(actigraphOffset[i]);
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
                                if (actigraphStart == null)
                                    actigraphStart = actigraphTime.Year + "/" + actigraphTime.Month + "/" + actigraphTime.Day + " " + actigraphTime.Hour + ":" + actigraphTime.Minute + ":" + actigraphTime.Second;
                                string actigraphLine = "" + Convert.ToInt32(tokens[2]);
                                actigraphData[i].Add(actigraphKey, actigraphLine);
                            }
                        } while ((actigraph_line = actigraphReader.ReadLine()) != null);
                    }
                    else if (actigraph_line.Contains("GT1M"))
                    {
                        actigraphType[i] = "GT1M";
                        Match m;
                        int actihour = 0, actiminute = 0, actisecond = 0, actiyear = 0, actiday = 0, actimonth = 0;
                        do
                        {
                            actigraph_line = actigraphReader.ReadLine();
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            if (actigraph_line.Contains("Start Time"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                                actihour = Convert.ToInt32(m.Groups[1].Value);
                                actiminute = Convert.ToInt32(m.Groups[2].Value);
                                actisecond = Convert.ToInt32(m.Groups[3].Value);
                            }
                            else if (actigraph_line.Contains("Start Date"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                                actimonth = Convert.ToInt32(m.Groups[1].Value);
                                actiday = Convert.ToInt32(m.Groups[2].Value);
                                actiyear = Convert.ToInt32(m.Groups[3].Value);
                            }
                            tokens = actigraph_line.Split(',');
                        } while (tokens.Length != 3);


                        tokens = actigraph_line.Split(',');
                        //Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        //Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(actiyear, actimonth, actiday, actihour, actiminute, actisecond);//(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                        // if (actigraphOffset > 0)
                        actigraphTime = actigraphTime.AddSeconds(actigraphOffset[i]);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            tokens = actigraph_line.Split(',');
                            if (tokens.Length == 3)
                            {
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
                                string actigraphLine = Convert.ToInt32(tokens[0]) + "," + Convert.ToInt32(tokens[1]);
                                if (actigraphStart == null)
                                    actigraphStart = actigraphTime.Year + "/" + actigraphTime.Month + "/" + actigraphTime.Day + " " + actigraphTime.Hour + ":" + actigraphTime.Minute + ":" + actigraphTime.Second;
                                actigraphData[i].Add(actigraphKey, actigraphLine);
                                actigraphTime = actigraphTime.AddSeconds(1.0);

                                //if (actigraphLine.Contains("144,92"))
                                //  Console.Write("");
                            }
                        } while ((actigraph_line = actigraphReader.ReadLine()) != null);

                    }
                    else if (actigraph_line.Contains("GT3X+"))
                    {
                        actigraphType[i] = "GT3X+";
                        Match m;
                        int actihour = 0, actiminute = 0, actisecond = 0, actiyear = 0, actiday = 0, actimonth = 0;
                        int actiEndHour = 0, actiEndMinute = 0, actiEndSecond = 0, actiEndYear = 0, actiEndDay = 0, actiEndMonth = 0;
                        do
                        {
                            actigraph_line = actigraphReader.ReadLine();
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            if (actigraph_line.Contains("Start Time"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                                actihour = Convert.ToInt32(m.Groups[1].Value);
                                actiminute = Convert.ToInt32(m.Groups[2].Value);
                                actisecond = Convert.ToInt32(m.Groups[3].Value);
                            }
                            else if (actigraph_line.Contains("Start Date"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                                actimonth = Convert.ToInt32(m.Groups[1].Value);
                                actiday = Convert.ToInt32(m.Groups[2].Value);
                                actiyear = Convert.ToInt32(m.Groups[3].Value);
                            }
                            else if (actigraph_line.Contains("Download Time"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                                actiEndHour = Convert.ToInt32(m.Groups[1].Value);
                                actiEndMinute = Convert.ToInt32(m.Groups[2].Value);
                                actiEndSecond = Convert.ToInt32(m.Groups[3].Value);
                            }
                            else if (actigraph_line.Contains("Download Date"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                                actiEndMonth = Convert.ToInt32(m.Groups[1].Value);
                                actiEndDay = Convert.ToInt32(m.Groups[2].Value);
                                actiEndYear = Convert.ToInt32(m.Groups[3].Value);
                            }
                            tokens = actigraph_line.Split(',');
                        } while (tokens.Length != 5);


                        tokens = actigraph_line.Split(',');
                        //Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        //Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(actiyear, actimonth, actiday, actihour, actiminute, actisecond);//(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                        //if (actigraphOffset > 0)
                        actigraphTime = actigraphTime.AddSeconds(actigraphOffset[i]);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        actigraphEndTime = new DateTime(actiEndYear, actiEndMonth, actiEndDay, actiEndHour, actiEndMinute, actiEndSecond);
                        actigraphEndTime = actigraphEndTime.AddSeconds(actigraphOffset[i]);

                        actigraphStartTimes[i] = actigraphTime;
                        actigraphEndTimes[i] = actigraphEndTime;

                        do
                        {
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            tokens = actigraph_line.Split(',');
                            if (tokens.Length == 5)
                            {
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
                                string actigraphLine = Convert.ToInt32(tokens[0]) + "," + Convert.ToInt32(tokens[1]) + "," + Convert.ToInt32(tokens[2]);
                                if (actigraphStart == null)
                                    actigraphStart = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + " " + actigraphTime.Hour + ":" + actigraphTime.Minute + ":" + actigraphTime.Second;
                                actigraphData[i].Add(actigraphKey, actigraphLine);
                                actigraphTime = actigraphTime.AddSeconds(1.0);
                            }
                        } while ((actigraph_line = actigraphReader.ReadLine()) != null);
                    }
                    else if (actigraph_line.Contains("GT3X"))
                    {
                        actigraphType[i] = "GT3X";
                        Match m;
                        int actihour = 0, actiminute = 0, actisecond = 0, actiyear = 0, actiday = 0, actimonth = 0;
                        do
                        {
                            actigraph_line = actigraphReader.ReadLine();
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            if (actigraph_line.Contains("Start Time"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                                actihour = Convert.ToInt32(m.Groups[1].Value);
                                actiminute = Convert.ToInt32(m.Groups[2].Value);
                                actisecond = Convert.ToInt32(m.Groups[3].Value);
                            }
                            else if (actigraph_line.Contains("Start Date"))
                            {
                                tokens = actigraph_line.Split(' ');
                                m = Regex.Match(tokens[2].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                                actimonth = Convert.ToInt32(m.Groups[1].Value);
                                actiday = Convert.ToInt32(m.Groups[2].Value);
                                actiyear = Convert.ToInt32(m.Groups[3].Value);
                            }
                            tokens = actigraph_line.Split(',');
                        } while (tokens.Length != 5);


                        tokens = actigraph_line.Split(',');
                        //Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        //Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(actiyear, actimonth, actiday, actihour, actiminute, actisecond);//(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                        //if (actigraphOffset > 0)
                        actigraphTime = actigraphTime.AddSeconds(actigraphOffset[i]);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            if (actigraph_line.Contains("\""))
                            {
                                actigraph_line = actigraph_line.Replace("\"", "");
                            }
                            tokens = actigraph_line.Split(',');
                            if (tokens.Length == 5)
                            {
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
                                string actigraphLine = Convert.ToInt32(tokens[0]) + "," + Convert.ToInt32(tokens[1]) + "," + Convert.ToInt32(tokens[2]);
                                if (actigraphStart == null)
                                    actigraphStart = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + " " + actigraphTime.Hour + ":" + actigraphTime.Minute + ":" + actigraphTime.Second;
                                actigraphData[i].Add(actigraphKey, actigraphLine);
                                actigraphTime = actigraphTime.AddSeconds(1.0);
                            }
                        } while ((actigraph_line = actigraphReader.ReadLine()) != null);
                    }
                    actigraphReader.Close();
                }
            }
            catch (Exception e)
            {
                throw new Exception("Actigraphs: Parsing failed " + e.Message);
            }
            for (int r = 0; (r < actigraphData.Length); r++)
            {
                if (hasActigraph == false)
                    hasActigraph = (actigraphData[r].Count > 0);
                actigraphRecords += actigraphData[r].Count;
            }
            #endregion Read Actigraph data


            #region Read Zephyr data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-zephyr*.csv");

            string zephyr_line = "";
            try
            {
                if (file.Length == 1)
                {
                    if (CSVProgress == "")
                        CSVProgress = "Processing Zephyr Data";
                    zephyrReader = new StreamReader(file[0]);
                    zephyr_line = zephyrReader.ReadLine();//skip two lines
                    zephyr_line = zephyrReader.ReadLine();


                    while ((zephyr_line = zephyrReader.ReadLine()) != null)
                    {
                        tokens = zephyr_line.Split(',');
                        if (tokens.Length <= 18)
                        {
                            string[] tokens1 = tokens[0].Split(' ');
                            string[] dateTokens = tokens1[0].Split('/');
                            string[] timeTokens = (tokens1[1].Split('.'))[0].Split(':');
                            zephyrTime = new DateTime(Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(dateTokens[2]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));

                            // if (zephyrOffset > 0)
                            zephyrTime = zephyrTime.AddSeconds(zephyrOffset);
                            zephyrUnixTime = UnixTime.GetUnixTime(zephyrTime);


                            string zephyrKey = zephyrTime.Year + "-" + zephyrTime.Month + "-" + zephyrTime.Day + "-" + zephyrTime.Hour + "-" + zephyrTime.Minute + "-" + zephyrTime.Second;
                            string zephyrLine = "";
                            if (zephyrStart == null)
                                zephyrStart = zephyrTime.Year + "/" + zephyrTime.Month + "/" + zephyrTime.Day + " " + zephyrTime.Hour + ":" + zephyrTime.Minute + ":" + zephyrTime.Second;

                            if (tokens[1].Length > 0)
                                zephyrLine += Convert.ToInt32(tokens[1]);
                            zephyrLine += ",";
                            if (tokens[2].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[2]);
                            zephyrLine += ",";
                            if (tokens[3].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[3]);
                            zephyrLine += ",";
                            if (tokens[4].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[4]);
                            zephyrLine += ",";
                            if (tokens[5].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[5]);
                            zephyrLine += ",";
                            if (tokens[6].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[6]);
                            zephyrLine += ",";
                            if (tokens[7].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[7]);
                            zephyrLine += ",";
                            if (tokens[8].Length > 0)
                                zephyrLine += Convert.ToInt32(tokens[8]);
                            zephyrLine += ",";
                            if (tokens[9].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[9]);
                            zephyrLine += ",";
                            if (tokens[10].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[10]);
                            zephyrLine += ",";
                            if (tokens[11].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[11]);
                            zephyrLine += ",";
                            if (tokens[12].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[12]);
                            zephyrLine += ",";
                            if (tokens[13].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[13]);
                            zephyrLine += ",";
                            if (tokens[14].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[14]);
                            zephyrLine += ",";
                            if (tokens[15].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[15]);
                            zephyrLine += ",";
                            if (tokens[16].Length > 0)
                                zephyrLine += Convert.ToDouble(tokens[16]);
                            if (zephyrData.Contains(zephyrKey) == false)
                                zephyrData.Add(zephyrKey, zephyrLine);
                        }
                    }

                    zephyrFound = true;
                    hasZephyr = true;
                    zephyrRecords = zephyrData.Count;
                }
            }
            catch (Exception e)
            {
                throw new Exception("Zephyr: Parsing failed " + e.Message);
            }
            #endregion Read Zephyr data


            #region Read Oxycon data

            if (File.Exists(aDataDirectory + "\\" + OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt"))
            {

                file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-oxycon-flashcard.dat");
                if (file.Length == 1)
                {

                    TextReader oxyconOriginTR = new StreamReader(aDataDirectory + "\\" + OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt");
                    string originOxycon = oxyconOriginTR.ReadLine();
                    DateTime oxyconOriginTime = new DateTime();
                    try
                    {
                        tokens = originOxycon.Split(',');
                        tokens = tokens[0].Split('.');
                        oxyconOriginTR.Close();
                        UnixTime.GetDateTime(Convert.ToInt64(tokens[0]), out oxyconOriginTime);
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Synchronization: Parsing failed " + e.Message);
                    }

                    //Synchronize Both files to find a matching point and pick the time stamps
                    int oxyconAdjustment = 0;
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-oxycon.dat");
                    string oxycon_line = "";
                    Hashtable oxyconData1 = new Hashtable();
                    int checkCount = 0;
                    try
                    {
                        if (file.Length == 1)
                        {
                            oxyconReader = new StreamReader(file[0]);
                            for (int j = 0; (j < 8); j++)
                                oxycon_line = oxyconReader.ReadLine();//skip first 8 lines

                            while ((oxycon_line = oxyconReader.ReadLine()) != null)
                            {
                                oxycon_line = oxycon_line.Trim();
                                RegexOptions options = RegexOptions.None;
                                Regex regex = new Regex(@"[ ]{2,}", options);

                                oxycon_line = regex.Replace(oxycon_line, @" ");
                                regex = new Regex(@"[\t]", options);
                                oxycon_line = regex.Replace(oxycon_line, @" ");

                                tokens = oxycon_line.Split(' ');
                                string[] timeTokens = tokens[0].Split(':');
                                int oxyconSeconds = 0;

                                if (timeTokens.Length >= 2)
                                {
                                    string oxyconKey = "";

                                    if (timeTokens.Length == 2) //always mins:seconds
                                        oxyconSeconds = Convert.ToInt32(timeTokens[0]) * 60 + Convert.ToInt32(timeTokens[1]);
                                    else //3 tokens can either include minutes or hours can be mins:secs:00 or hrs:mins:secs
                                        oxyconSeconds = Convert.ToInt32(timeTokens[0]) * 60 * 60 + Convert.ToInt32(timeTokens[1]) * 60 + Convert.ToInt32(timeTokens[2]);



                                    if ((tokens[2].Length > 0) && (tokens[2] != "-"))
                                        oxyconKey += Convert.ToInt32(tokens[2]);
                                    oxyconKey += ",";
                                    if ((tokens[3].Length > 0) && (tokens[3] != "-"))
                                        oxyconKey += Convert.ToInt32(tokens[3]);
                                    oxyconKey += ",";

                                    if ((tokens[4].Length > 0) && (tokens[4] != "-"))
                                        oxyconKey += Convert.ToInt32(tokens[4]);
                                    oxyconKey += ",";
                                    if ((tokens[5].Length > 0) && (tokens[5] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[5]);
                                    oxyconKey += ",";

                                    if ((tokens[6].Length > 0) && (tokens[6] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[6]);
                                    oxyconKey += ",";
                                    if ((tokens[7].Length > 0) && (tokens[7] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[7]);
                                    oxyconKey += ",";
                                    if ((tokens[8].Length > 0) && (tokens[8] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[8]);
                                    oxyconKey += ",";
                                    if (oxyconData1.ContainsKey(oxyconKey) == false)
                                        oxyconData1.Add(oxyconKey, oxyconSeconds);
                                }
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon PC File: Parsing failed " + e.Message);
                    }


                    //find first 3 matching lines with the same differnece in time
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-oxycon-flashcard.dat");
                    try
                    {
                        if (file.Length == 1)
                        {
                            oxyconReader = new StreamReader(file[0]);
                            for (int j = 0; (j < 8); j++)
                                oxycon_line = oxyconReader.ReadLine();//skip first 8 lines

                            while ((oxycon_line = oxyconReader.ReadLine()) != null)
                            {
                                oxycon_line = oxycon_line.Trim();
                                RegexOptions options = RegexOptions.None;
                                Regex regex = new Regex(@"[ ]{2,}", options);
                                oxycon_line = regex.Replace(oxycon_line, @" ");

                                tokens = oxycon_line.Split(' ');
                                string[] timeTokens = tokens[0].Split(':');
                                int oxyconSeconds = 0;

                                if (timeTokens.Length >= 2)
                                {
                                    string oxyconKey = "";

                                    if (timeTokens.Length == 2) //always mins:seconds
                                        oxyconSeconds = Convert.ToInt32(timeTokens[0]) * 60 + Convert.ToInt32(timeTokens[1]);
                                    else //3 tokens can either include minutes or hours can be mins:secs:00 or hrs:mins:secs
                                        oxyconSeconds = Convert.ToInt32(timeTokens[0]) * 60 * 60 + Convert.ToInt32(timeTokens[1]) * 60 + Convert.ToInt32(timeTokens[2]);



                                    if ((tokens[2].Length > 0) && (tokens[2] != "-"))
                                        oxyconKey += Convert.ToInt32(tokens[2]);
                                    oxyconKey += ",";
                                    if ((tokens[3].Length > 0) && (tokens[3] != "-"))
                                        oxyconKey += Convert.ToInt32(tokens[3]);
                                    oxyconKey += ",";

                                    if ((tokens[4].Length > 0) && (tokens[4] != "-"))
                                        oxyconKey += Convert.ToInt32(tokens[4]);
                                    oxyconKey += ",";
                                    if ((tokens[5].Length > 0) && (tokens[5] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[5]);
                                    oxyconKey += ",";

                                    if ((tokens[6].Length > 0) && (tokens[6] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[6]);
                                    oxyconKey += ",";
                                    if ((tokens[7].Length > 0) && (tokens[7] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[7]);
                                    oxyconKey += ",";
                                    if ((tokens[8].Length > 0) && (tokens[8] != "-"))
                                        oxyconKey += Convert.ToDouble(tokens[8]);
                                    oxyconKey += ",";
                                    if (oxyconData1.ContainsKey(oxyconKey))
                                    {
                                        int flashTime = oxyconSeconds;
                                        int pcTime = (int)oxyconData1[oxyconKey];
                                        if (pcTime <= flashTime)
                                        {
                                            int difference = flashTime - pcTime;
                                            if (difference == oxyconAdjustment)
                                                checkCount++;
                                            else
                                                checkCount = 0;

                                            oxyconAdjustment = difference;

                                            //break when the same oxycon adjustment is seen 3 times
                                            if (checkCount == 3)
                                                break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Flash: Parsing failed 1 " + e.Message);
                    }

                    oxyconData1.Clear();


                    //Load Oxycon data
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*oxycon-flashcard.dat");
                    try
                    {
                        if (file.Length == 1)
                        {
                            if (CSVProgress == "")
                                CSVProgress = "Processing Oxycon Data";
                            oxyconReader = new StreamReader(file[0]);
                            for (int j = 0; (j < 8); j++)
                                oxycon_line = oxyconReader.ReadLine();//skip first 8 lines

                            while ((oxycon_line = oxyconReader.ReadLine()) != null)
                            {
                                oxycon_line = oxycon_line.Trim();
                                RegexOptions options = RegexOptions.None;
                                Regex regex = new Regex(@"[ ]{2,}", options);
                                oxycon_line = regex.Replace(oxycon_line, @" ");

                                tokens = oxycon_line.Split(' ');
                                string[] timeTokens = tokens[0].Split(':');

                                if (timeTokens.Length >= 2)
                                {

                                    if (timeTokens.Length == 2) //always mins:seconds
                                    {
                                        oxyconTime = oxyconOriginTime.AddMinutes(Convert.ToDouble(timeTokens[0]));
                                        oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[1]));
                                    }
                                    else //3 tokens can either include minutes or hours can be mins:secs:00 or hrs:mins:secs
                                    {

                                        //OXYCON BUG: The oxycon output files are very buggy
                                        // sometimes they report min:sec:00 and sometimes hr:min:sec

                                        if (Convert.ToDouble(timeTokens[0]) >= 24) //this is min:sec:00
                                        {
                                            oxyconTime = oxyconOriginTime.AddMinutes(Convert.ToDouble(timeTokens[0]));
                                            oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[1]));
                                        }
                                        else  //this is hr:min:sec
                                        {
                                            oxyconTime = oxyconOriginTime.AddHours(Convert.ToDouble(timeTokens[0]));
                                            oxyconTime = oxyconTime.AddMinutes(Convert.ToDouble(timeTokens[1]));
                                            oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[2]));
                                        }

                                    }


                                    oxyconTime = oxyconTime.AddSeconds(-1.0 * oxyconAdjustment);
                                    oxyconTime = oxyconTime.AddSeconds(oxyconOffset);
                                    oxyconUnixTime = UnixTime.GetUnixTime(oxyconTime);


                                    string oxyconKey = oxyconTime.Year + "-" + oxyconTime.Month + "-" + oxyconTime.Day + "-" + oxyconTime.Hour + "-" + oxyconTime.Minute + "-" + oxyconTime.Second;
                                    string oxyconLine = "";

                                    if (oxyconStart == null)
                                        oxyconStart = oxyconTime.Year + "/" + oxyconTime.Month + "/" + oxyconTime.Day + " " + oxyconTime.Hour + ":" + oxyconTime.Minute + ":" + oxyconTime.Second;
                                    //if (oxyconTime.Day >= 10)
                                    //  Console.Write("");
                                    if ((tokens[1].Length > 0) && (tokens[1] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[1]);
                                    oxyconLine += ",";

                                    if ((tokens[2].Length > 0) && (tokens[2] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[2]);
                                    oxyconLine += ",";

                                    if ((tokens[3].Length > 0) && (tokens[3] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[3]);
                                    oxyconLine += ",";
                                    if ((tokens[4].Length > 0) && (tokens[4] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[4]);
                                    oxyconLine += ",";

                                    if ((tokens[5].Length > 0) && (tokens[5] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[5]);
                                    oxyconLine += ",";
                                    if ((tokens[6].Length > 0) && (tokens[6] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[6]);
                                    oxyconLine += ",";
                                    if ((tokens[7].Length > 0) && (tokens[7] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[7]);
                                    oxyconLine += ",";
                                    if ((tokens[8].Length > 0) && (tokens[8] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[8]);
                                    //oxyconLine += ",";
                                    if (oxyconData.ContainsKey(oxyconKey) == false)
                                        oxyconData.Add(oxyconKey, oxyconLine);
                                }
                            }

                            oxyconFound = true;
                        }
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Flash: Parsing failed 2 " + e.Message);
                    }

                }
                else if (file.Length == 2) //sometimes 2 oxycon sessions were recorded
                {

                    TextReader oxyconOriginTR = new StreamReader(aDataDirectory + "\\" + OTHER_SUBDIRECTORY + "\\OxyconSyncronizationTime.txt");
                    string originOxycon = oxyconOriginTR.ReadLine();
                    DateTime oxyconOriginTime = new DateTime();
                    try
                    {
                        tokens = originOxycon.Split(',');
                        tokens = tokens[0].Split('.');
                        UnixTime.GetDateTime(Convert.ToInt64(tokens[0]), out oxyconOriginTime);
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Synchronization: Parsing failed " + e.Message);
                    }


                    string oxycon_line = "";
                    //Load Oxycon data
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-flashcard.1.dat");
                    try
                    {
                        if (file.Length == 1)
                        {
                            if (CSVProgress == "")
                                CSVProgress = "Processing Flashcard1";
                            oxyconReader = new StreamReader(file[0]);
                            for (int j = 0; (j < 8); j++)
                                oxycon_line = oxyconReader.ReadLine();//skip first 8 lines

                            while ((oxycon_line = oxyconReader.ReadLine()) != null)
                            {
                                oxycon_line = oxycon_line.Trim();
                                RegexOptions options = RegexOptions.None;
                                Regex regex = new Regex(@"[ ]{2,}", options);
                                oxycon_line = regex.Replace(oxycon_line, @" ");

                                tokens = oxycon_line.Split(' ');
                                string[] timeTokens = tokens[0].Split(':');

                                if (timeTokens.Length >= 2)
                                {

                                    if (timeTokens.Length == 2) //always mins:seconds
                                    {
                                        oxyconTime = oxyconOriginTime.AddMinutes(Convert.ToDouble(timeTokens[0]));
                                        oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[1]));
                                    }
                                    else //3 tokens can either include minutes or hours can be mins:secs:00 or hrs:mins:secs
                                    {


                                        if (Convert.ToDouble(timeTokens[0]) >= 24) //this is min:sec:00
                                        {
                                            oxyconTime = oxyconOriginTime.AddMinutes(Convert.ToDouble(timeTokens[0]));
                                            oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[1]));
                                        }
                                        else  //this is hr:min:sec
                                        {
                                            oxyconTime = oxyconOriginTime.AddHours(Convert.ToDouble(timeTokens[0]));
                                            oxyconTime = oxyconTime.AddMinutes(Convert.ToDouble(timeTokens[1]));
                                            oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[2]));
                                        }


                                    }




                                    oxyconUnixTime = UnixTime.GetUnixTime(oxyconTime);
                                    oxyconTime = oxyconTime.AddSeconds(oxyconOffset);
                                    string oxyconKey = oxyconTime.Year + "-" + oxyconTime.Month + "-" + oxyconTime.Day + "-" + oxyconTime.Hour + "-" + oxyconTime.Minute + "-" + oxyconTime.Second;
                                    string oxyconLine = "";

                                    if (oxyconStart == null)
                                        oxyconStart = oxyconTime.Year + "/" + oxyconTime.Month + "/" + oxyconTime.Day + " " + oxyconTime.Hour + ":" + oxyconTime.Minute + ":" + oxyconTime.Second;

                                    if ((tokens[1].Length > 0) && (tokens[1] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[1]);
                                    oxyconLine += ",";

                                    if ((tokens[2].Length > 0) && (tokens[2] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[2]);
                                    oxyconLine += ",";

                                    if ((tokens[3].Length > 0) && (tokens[3] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[3]);
                                    oxyconLine += ",";
                                    if ((tokens[4].Length > 0) && (tokens[4] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[4]);
                                    oxyconLine += ",";

                                    if ((tokens[5].Length > 0) && (tokens[5] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[5]);
                                    oxyconLine += ",";
                                    if ((tokens[6].Length > 0) && (tokens[6] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[6]);
                                    oxyconLine += ",";
                                    if ((tokens[7].Length > 0) && (tokens[7] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[7]);
                                    oxyconLine += ",";
                                    if ((tokens[8].Length > 0) && (tokens[8] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[8]);
                                    //oxyconLine += ",";
                                    if (oxyconData.ContainsKey(oxyconKey) == false)
                                        oxyconData.Add(oxyconKey, oxyconLine);
                                }
                            }

                            oxyconFound = true;
                        }
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Flash: Parsing failed 2 " + e.Message);
                    }







                    originOxycon = oxyconOriginTR.ReadLine();
                    oxyconOriginTime = new DateTime();
                    try
                    {
                        tokens = originOxycon.Split(',');
                        tokens = tokens[0].Split('.');
                        oxyconOriginTR.Close();
                        UnixTime.GetDateTime(Convert.ToInt64(tokens[0]), out oxyconOriginTime);
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Synchronization: Parsing failed " + e.Message);
                    }



                    //Load Oxycon data
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-flashcard.2.dat");
                    try
                    {
                        if (file.Length == 1)
                        {
                            if (CSVProgress == "")
                                CSVProgress = "Processing Flashcard1";
                            oxyconReader = new StreamReader(file[0]);
                            for (int j = 0; (j < 8); j++)
                                oxycon_line = oxyconReader.ReadLine();//skip first 8 lines

                            while ((oxycon_line = oxyconReader.ReadLine()) != null)
                            {
                                oxycon_line = oxycon_line.Trim();
                                RegexOptions options = RegexOptions.None;
                                Regex regex = new Regex(@"[ ]{2,}", options);
                                oxycon_line = regex.Replace(oxycon_line, @" ");

                                tokens = oxycon_line.Split(' ');
                                string[] timeTokens = tokens[0].Split(':');

                                if (timeTokens.Length >= 2)
                                {

                                    if (timeTokens.Length == 2) //always mins:seconds
                                    {
                                        oxyconTime = oxyconOriginTime.AddMinutes(Convert.ToDouble(timeTokens[0]));
                                        oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[1]));
                                    }
                                    else //3 tokens can either include minutes or hours can be mins:secs:00 or hrs:mins:secs
                                    {



                                        if (Convert.ToDouble(timeTokens[0]) >= 24) //this is min:sec:00
                                        {
                                            oxyconTime = oxyconOriginTime.AddMinutes(Convert.ToDouble(timeTokens[0]));
                                            oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[1]));
                                        }
                                        else  //this is hr:min:sec
                                        {
                                            oxyconTime = oxyconOriginTime.AddHours(Convert.ToDouble(timeTokens[0]));
                                            oxyconTime = oxyconTime.AddMinutes(Convert.ToDouble(timeTokens[1]));
                                            oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[2]));
                                        }

                                    }




                                    oxyconUnixTime = UnixTime.GetUnixTime(oxyconTime);
                                    oxyconTime = oxyconTime.AddSeconds(oxyconOffset);
                                    string oxyconKey = oxyconTime.Year + "-" + oxyconTime.Month + "-" + oxyconTime.Day + "-" + oxyconTime.Hour + "-" + oxyconTime.Minute + "-" + oxyconTime.Second;
                                    string oxyconLine = "";
                                    if (oxyconStart == null)
                                        oxyconStart = oxyconTime.Year + "/" + oxyconTime.Month + "/" + oxyconTime.Day + " " + oxyconTime.Hour + ":" + oxyconTime.Minute + ":" + oxyconTime.Second;
                                    if (oxyconStart == null)
                                        oxyconStart = oxyconTime.Year + "/" + oxyconTime.Month + "/" + oxyconTime.Day + " " + oxyconTime.Hour + ":" + oxyconTime.Minute + ":" + oxyconTime.Second;

                                    if ((tokens[1].Length > 0) && (tokens[1] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[1]);
                                    oxyconLine += ",";

                                    if ((tokens[2].Length > 0) && (tokens[2] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[2]);
                                    oxyconLine += ",";

                                    if ((tokens[3].Length > 0) && (tokens[3] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[3]);
                                    oxyconLine += ",";
                                    if ((tokens[4].Length > 0) && (tokens[4] != "-"))
                                        oxyconLine += Convert.ToInt32(tokens[4]);
                                    oxyconLine += ",";

                                    if ((tokens[5].Length > 0) && (tokens[5] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[5]);
                                    oxyconLine += ",";
                                    if ((tokens[6].Length > 0) && (tokens[6] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[6]);
                                    oxyconLine += ",";
                                    if ((tokens[7].Length > 0) && (tokens[7] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[7]);
                                    oxyconLine += ",";
                                    if ((tokens[8].Length > 0) && (tokens[8] != "-"))
                                        oxyconLine += Convert.ToDouble(tokens[8]);
                                    // oxyconLine += ",";
                                    if (oxyconData.ContainsKey(oxyconKey) == false)
                                        oxyconData.Add(oxyconKey, oxyconLine);
                                }
                            }

                            oxyconFound = true;
                        }
                    }
                    catch (Exception e)
                    {
                        throw new Exception("Oxycon Flash: Parsing failed 2 " + e.Message);
                    }

                }
            }

            hasOxycon = (oxyconData.Count > 0);
            oxyconRecords = oxyconData.Count;
            #endregion Read Oxycon data


            #region Read Sensewear data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-sensewear*.csv");
            string sensewear_line = "";
            Hashtable SSR = new Hashtable();
            Hashtable STrans = new Hashtable();
            Hashtable SLong = new Hashtable();
            Hashtable SAcc = new Hashtable();


            try
            {
                if (file.Length == 1)
                {
                    sensewearReader = new StreamReader(file[0]);
                    sensewear_line = sensewearReader.ReadLine(); //skip first line
                    if (sensewear_line.Contains("numpeaks_"))
                        sensewearVanderbiltFound = true;
                    else
                        sensewearFound = true;


                    sensewearSR = 1;

                    while ((sensewear_line = sensewearReader.ReadLine()) != null)
                    {
                        tokens = sensewear_line.Split(',');
                        string[] tsTokens = tokens[0].Split(' ');

                        //2009-08-24 14:32:00.000
                        if (tsTokens.Length > 1)
                        {
                            string[] dateTokens = tsTokens[0].Split('-');
                            string[] timeTokens = tsTokens[1].Split('.');
                            timeTokens = timeTokens[0].Split(':');
                            sensewearTime = new DateTime(Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(dateTokens[2]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));

                            //if (sensewearOffset > 0)
                            sensewearTime = sensewearTime.AddSeconds(sensewearOffset);
                            sensewearUnixTime = UnixTime.GetUnixTime(sensewearTime);
                        }
                        else
                        { //unix time
                            TimeZone localZone = TimeZone.CurrentTimeZone;
                            DaylightTime daylight = localZone.GetDaylightChanges(DateTime.Now.Year);
                            sensewearUnixTime = Convert.ToInt64(tokens[0].Trim()) - (8 * 60 * 60 * 1000);
                            UnixTime.GetDateTime((long)sensewearUnixTime, out sensewearTime);

                            if (!TimeZone.IsDaylightSavingTime(new DateTime(sensewearTime.Year, sensewearTime.Month, sensewearTime.Day), daylight))
                                sensewearUnixTime = Convert.ToInt64(tokens[0].Trim()) - (8 * 60 * 60 * 1000);
                            else
                                sensewearUnixTime = Convert.ToInt64(tokens[0].Trim()) - (7 * 60 * 60 * 1000);

                            //if (sensewearOffset > 0)                           
                            UnixTime.GetDateTime((long)sensewearUnixTime, out sensewearTime);
                            sensewearTime = sensewearTime.AddSeconds(sensewearOffset);
                        }

                        if (sensewearStart == null)
                            sensewearStart = sensewearTime.Year + "/" + sensewearTime.Month + "/" + sensewearTime.Day + " " + sensewearTime.Hour + ":" + sensewearTime.Minute + ":" + sensewearTime.Second;

                        if (sensewearFound)
                        {
                            if ((sensewearTime.Day == prevSensewearTime.Day) && (sensewearTime.Hour == prevSensewearTime.Hour) &&
                                (sensewearTime.Minute == prevSensewearTime.Minute) && (sensewearTime.Second == prevSensewearTime.Second))
                            {
                                sensewearSR++;
                                if (tokens[5].Length > 0)
                                    sensewearTrans += Convert.ToDouble(tokens[5]);
                                if (tokens[6].Length > 0)
                                    sensewearLong += Convert.ToDouble(tokens[6]);
                                if (tokens[11].Length > 0)
                                    sensewearForAcc += Convert.ToDouble(tokens[11]);
                            }
                            else
                            {
                                string time = prevSensewearTime.Year + "-" + prevSensewearTime.Month + "-" + prevSensewearTime.Day + "-" + prevSensewearTime.Hour + "-" + prevSensewearTime.Minute + "-" + prevSensewearTime.Second;
                                SSR.Add(time, sensewearSR);
                                STrans.Add(time, sensewearTrans);
                                SLong.Add(time, sensewearLong);
                                SAcc.Add(time, sensewearForAcc);

                                sensewearSR = 1;
                                sensewearTrans = Convert.ToDouble(tokens[5]);
                                sensewearLong = Convert.ToDouble(tokens[6]);
                                sensewearForAcc = Convert.ToDouble(tokens[11]);
                            }
                        }
                        else if (sensewearVanderbiltFound)
                        {

                            string time = sensewearTime.Year + "-" + sensewearTime.Month + "-" + sensewearTime.Day + "-" + sensewearTime.Hour + "-" + sensewearTime.Minute + "-" + sensewearTime.Second;
                            sensewearSR = 1;
                            vanderbiltSensewearDataLine = sensewearSR + ",";
                            vanderbiltSensewearDataLine += tokens[1] + ",";
                            vanderbiltSensewearDataLine += tokens[2] + ",";
                            vanderbiltSensewearDataLine += tokens[3] + ",";
                            vanderbiltSensewearDataLine += tokens[4] + ",";
                            vanderbiltSensewearDataLine += tokens[5] + ",";
                            vanderbiltSensewearDataLine += tokens[6] + ",";
                            vanderbiltSensewearDataLine += tokens[7] + ",";
                            vanderbiltSensewearDataLine += tokens[8] + ",";
                            vanderbiltSensewearDataLine += tokens[9] + ",";
                            vanderbiltSensewearDataLine += tokens[10] + ",";
                            vanderbiltSensewearDataLine += tokens[11] + ",";
                            vanderbiltSensewearDataLine += tokens[15];
                            sensewearData.Add(time, vanderbiltSensewearDataLine);
                        }

                        prevSensewearTime = sensewearTime;

                    }


                }
            }
            catch (Exception e)
            {
                throw new Exception("Sensewear: Parsing failed " + e.Message);
            }

            hasSensewear = (SSR.Count > 0);
            sensewearRecords = SSR.Count;
            #endregion Read Sensewear data


            #region Read RT3 data
            file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-rt3*.csv");
            string rt3_line = "";
            Hashtable rt3 = new Hashtable();

            try
            {
                if (file.Length == 1)
                {
                    rt3Reader = new StreamReader(file[0]);
                    rt3Found = true;
                    for (int j = 0; (j < 20); j++)
                        rt3_line = rt3Reader.ReadLine(); //skip first line

                    rt3SR = 1;

                    while ((rt3_line = rt3Reader.ReadLine()) != null)
                    {
                        tokens = rt3_line.Split(',');

                        //11/20/2008,7:54:00

                        string[] dateTokens = tokens[1].Split('/');
                        string[] timeTokens = tokens[2].Split(':');
                        rt3Time = new DateTime(Convert.ToInt32(dateTokens[2]), Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));
                        rt3UnixTime = UnixTime.GetUnixTime(sensewearTime);

                        //Entry,Date,Time,Total Calories,Activity Calories,VM,Start Flag,Stop Flag,ActCntsX,ActCntsY,ActCntsZ
                        string time = rt3Time.Year + "-" + rt3Time.Month + "-" + rt3Time.Day + "-" + rt3Time.Hour + "-" + rt3Time.Minute + "-" + rt3Time.Second;



                        rt3SR = 1;
                        rt3_dataline = rt3SR + ",";
                        rt3_dataline += tokens[3] + ",";
                        rt3_dataline += tokens[4] + ",";
                        rt3_dataline += tokens[5] + ",";
                        rt3_dataline += tokens[8] + ",";
                        rt3_dataline += tokens[9] + ",";
                        rt3_dataline += tokens[10];
                        rt3Data.Add(time, rt3_dataline);


                    }


                }
            }
            catch (Exception e)
            {
                throw new Exception("RT3: Parsing failed " + e.Message);
            }
            #endregion Read RT3 data


            #region Setup master and other sensor files
            try
            {
                masterCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITesSummaryData.csv");
                hrCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\HeartRate_MITes.csv");

                for (int i = 0; (i < actigraphCSV.Length); i++)
                    actigraphCSV[i] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Actigraph" + (i + 1) + ".csv");


                if ((sensewearFound) || (sensewearVanderbiltFound))
                    sensewearCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Sensewear.csv");


                if (zephyrFound)
                    zephyrCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Zephyr.csv");
                if (oxyconFound)
                    oxyconCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Oxycon.csv");
                if (omronFound)
                    omronCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Omron.csv");
                if (columbiaFound)
                    columbiaCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Columbia.csv");
                if (gpsFound)
                    gpsCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\GPS.csv");
                if (rtiFound)
                    rtiCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\RTI.csv");
                if (rt3Found)
                    rt3CSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\RT3.csv");
            }
            catch (Exception e)
            {
                throw new Exception("Unable to open CSV: cannot open file " + e.Message);
            }

            #endregion Setup master and other sensor files


            #region Load Annotations

            AXML.Annotation aannotation = null;
            try
            {
                if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\" + ANNOTATION_INTERVALS_FILE))
                {
                    //AXML.Reader reader = new AXML.Reader(masterDirectory, aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY, "AnnotationIntervals.xml");
                    //aannotation = reader.parse();
                    //aannotation.RemoveData(filter);
                    //aannotation.DataDirectory = aDataDirectory;

                    //---------------------------------------------------------------------
                    // Read the Annotation XML file generated by the Annotation Software
                    // Use the session.cs for cleaner implementation
                    // If there is an offset add it 
                    //---------------------------------------------------------------------
                    Session xmlSession = new Session();
                    xmlSession.FromXML(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\" + ANNOTATION_INTERVALS_FILE);

                    AnnotationList ann_list = xmlSession.Annotations;


                    //------------------------------------
                    // Add annotations offset
                    //------------------------------------
                    double unix_start, unix_end;
                    DateTime t_start, t_end;


                    foreach (Annotation ann in ann_list)
                    {

                        //Add Offset
                        unix_start = ann._StartUnix + (annotationsOffset * 1000);
                        UnixTime.GetDateTime((long)unix_start, out t_start);
                        //t_start = t_start.AddSeconds(annotationsOffset);

                        unix_end = ann._EndUnix + (annotationsOffset * 1000);
                        UnixTime.GetDateTime((long)unix_end, out t_end);
                        //t_end = t_end.AddSeconds(annotationsOffset);

                        //Start Time
                        ann._StartDate = t_start.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK"); //String.Format("{0:MM-dd-yyyy}", t_start);
                        ann._StartHour = t_start.Hour;
                        ann._StartMinute = t_start.Minute;
                        ann._StartSecond = t_start.Second;
                        ann._StartMillisecond = t_start.Millisecond;

                        //ts = (t_start - new DateTime(1970, 1, 1, 0, 0, 0));
                        ann._StartUnix = unix_start; //ts.TotalSeconds;

                        //Stop Time
                        ann._EndDate = t_end.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");//String.Format("{0:MM-dd-yyyy}", t_end);
                        ann._EndHour = t_end.Hour;
                        ann._EndMinute = t_end.Minute;
                        ann._EndSecond = t_end.Second;
                        ann._EndMillisecond = t_end.Millisecond;

                        //ts = (t_end - new DateTime(1970, 1, 1, 0, 0, 0));
                        ann._EndUnix = unix_end;//ts.TotalSeconds;

                    }

                    //------------------------------------------
                    //Write new annotations to file
                    //------------------------------------------
                    TextWriter ann_intervals_xml = null;
                    TextWriter ann_intervals_csv = null;


                    // Annotation Intervals Files
                    if (File.Exists(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.xml"))
                    {
                        File.Delete(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.xml");
                    }

                    if (File.Exists(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.csv"))
                    { File.Delete(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.csv"); }

                    ann_intervals_xml = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.xml");
                    ann_intervals_csv = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.csv");



                    //write to files
                    ann_intervals_xml.WriteLine(xmlSession.ToXML());
                    ann_intervals_csv.WriteLine(xmlSession.ToCSV());

                    //close files
                    ann_intervals_xml.Flush();
                    ann_intervals_xml.Close();

                    ann_intervals_csv.Flush();
                    ann_intervals_csv.Close();
                }

                //--------------------------------------------------------------------------
                //Read the corrected annotation files
                // original code, but now the reader is pointing to the corrected xml file
                // it is done in this way for backwards compatibility
                //--------------------------------------------------------------------------
                if (File.Exists(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\AnnotationIntervals.xml"))
                {
                    AXML.Reader reader = new AXML.Reader(masterDirectory, aDataDirectory + "\\" + MERGED_SUBDIRECTORY, "AnnotationIntervals.xml");
                    aannotation = reader.parse();
                    aannotation.RemoveData(filter);
                    aannotation.DataDirectory = aDataDirectory;
                }


            }
            catch (Exception e)
            {
                throw new Exception("MITes Configuration Files: Parsing failed " + e.Message);
            }


            if (aannotation != null)
            {
                foreach (AXML.Category category in aannotation.Categories)
                    master_csv_header += "," + category.Name;
            }



            #endregion Load Annotations


            #region Setup MITes Data

            MITesDecoder aMITesDecoder = null;
            MITesHRAnalyzer aMITesHRAnalyzer = null;
            MITesLoggerReader aMITesLoggerReader = null;
            SXML.SensorAnnotation sannotation = null;


            //Set Mites Sampling Rate 
            int mites_SAMPLING_RATE = 45;

            //Size of the moving average 
            int mites_RM_DURATION = 1000;
            int mites_RM_SIZE = (mites_RM_DURATION / 1000) * mites_SAMPLING_RATE;


            if (Directory.Exists(aDataDirectory + "\\" + MITES_SUBDIRECTORY + "\\data\\"))
            {
                try
                {
                    SXML.Reader sreader = new SXML.Reader(masterDirectory, aDataDirectory + "\\" + MITES_SUBDIRECTORY);
                    sannotation = sreader.parse(maxControllers);
                }
                catch (Exception e)
                {
                    throw new Exception("MITes Configuration Files: Parsing failed " + e.Message);
                }
            }




            if (Directory.Exists(aDataDirectory + "\\" + MITES_SUBDIRECTORY + "\\data\\"))
            {

                try
                {
                    SXML.Reader sreader = new SXML.Reader(masterDirectory, aDataDirectory + "\\" + MITES_SUBDIRECTORY);
                    sannotation = sreader.parse(maxControllers);
                }
                catch (Exception e)
                {
                    throw new Exception("MITes Configuration Files: Parsing failed " + e.Message);
                }


                //create some counters for activity counts
                averageX = new int[sannotation.MaximumSensorID + 1];
                averageY = new int[sannotation.MaximumSensorID + 1];
                averageZ = new int[sannotation.MaximumSensorID + 1];

                averageRawX = new int[sannotation.MaximumSensorID + 1];
                averageRawY = new int[sannotation.MaximumSensorID + 1];
                averageRawZ = new int[sannotation.MaximumSensorID + 1];

                prevX = new int[sannotation.MaximumSensorID + 1];
                prevY = new int[sannotation.MaximumSensorID + 1];
                prevZ = new int[sannotation.MaximumSensorID + 1];
                acCounters = new int[sannotation.MaximumSensorID + 1];

                for (int k = 0; (k < prevX.Length); k++)
                {
                    prevX[k] = -1;
                    prevY[k] = -1;
                    prevZ[k] = -1;

                }

                //Create CSV Arrays
                activityCountCSVs = new StreamWriter[sannotation.MaximumSensorID + 1];
                samplingCSVs = new StreamWriter[sannotation.MaximumSensorID + 1];
                averagedRaw = new StreamWriter[sannotation.MaximumSensorID + 1];
                aucCSVs = new StreamWriter[sannotation.MaximumSensorID + 1];
                vmagCSVs = new StreamWriter[sannotation.MaximumSensorID + 1];
                rmCSVs = new StreamWriter[sannotation.MaximumSensorID + 1];




                foreach (SXML.Sensor sensor in sannotation.Sensors)
                {
                    int sensor_id = Convert.ToInt32(sensor.ID);
                    string location = sensor.Location.Replace(' ', '-');
                    if (sensor_id > 0) //exclude HR
                    {
                        activityCountCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITes_" + sensor_id.ToString("00") + "_SAD_" + location + ".csv");
                        activityCountCSVs[sensor_id].WriteLine(csv_line1);
                        rmCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITes_" + sensor_id.ToString("00") + "_RM_" + location + ".csv");
                        rmCSVs[sensor_id].WriteLine(csv_line1);
                        aucCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITes_" + sensor_id.ToString("00") + "_AUC_" + location + ".csv");
                        aucCSVs[sensor_id].WriteLine(csv_line1);
                        vmagCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITes_" + sensor_id.ToString("00") + "_VMAG_" + location + ".csv");
                        vmagCSVs[sensor_id].WriteLine(csv_line6);
                        averagedRaw[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITes_" + sensor_id.ToString("00") + "_1s-RawMean_" + location + ".csv");
                        averagedRaw[sensor_id].WriteLine(csv_line1);
                        samplingCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITes_" + sensor_id.ToString("00") + "_SampleRate_" + location + ".csv");
                        samplingCSVs[sensor_id].WriteLine(csv_line2);
                        master_csv_header += ",MITes" + sensor_id.ToString("00") + "_SR," + "MITes" + sensor_id.ToString("00") + "_AVRaw_X," +
                            "MITes" + sensor_id.ToString("00") + "_AVRaw_Y," + "MITes" + sensor_id.ToString("00") + "_AVRaw_Z," + "MITes" + sensor_id.ToString("00") + "_SAD_X," +
                            "MITes" + sensor_id.ToString("00") + "_SAD_Y," + "MITes" + sensor_id.ToString("00") + "_SAD_Z," + "MITes" + sensor_id.ToString("00") + "_AUC_X," +
                            "MITes" + sensor_id.ToString("00") + "_AUC_Y," + "MITes" + sensor_id.ToString("00") + "_AUC_Z," + "MITes" + sensor_id.ToString("00") + "_AUC_XYZ," +
                            "MITes" + sensor_id.ToString("00") + "_RM_X," + "MITes" + sensor_id.ToString("00") + "_RM_Y," + "MITes" + sensor_id.ToString("00") + "_RM_Z," +
                            "MITes" + sensor_id.ToString("00") + "_RM_SIZE," + "MITes" + sensor_id.ToString("00") + "_VMAG";

                    }
                    else
                        master_csv_header += ",HR";
                }





                //Initialize arrays based on number of sensors
                rawData = new int[sannotation.MaximumSensorID + 1, 3, mites_RM_SIZE];
                for (int i = 0; (i < sannotation.MaximumSensorID + 1); i++)
                    for (int j = 0; (j < 3); j++)
                        for (int k = 0; (k < mites_RM_SIZE); k++)
                            rawData[i, j, k] = -1;
                timeData = new long[sannotation.MaximumSensorID + 1, mites_RM_SIZE];
                AUC = new int[sannotation.MaximumSensorID + 1, 3];
                VMAG = new double[sannotation.MaximumSensorID + 1];
                head = new int[sannotation.MaximumSensorID + 1];

                RMX = new double[sannotation.MaximumSensorID + 1];
                RMY = new double[sannotation.MaximumSensorID + 1];
                RMZ = new double[sannotation.MaximumSensorID + 1];
                RMSize = new int[sannotation.MaximumSensorID + 1];


                for (int i = 0; (i < head.Length); i++)
                {
                    head[i] = 0;
                    RMX[i] = 0;
                    RMY[i] = 0;
                    RMZ[i] = 0;
                    RMSize[i] = 0;
                    VMAG[i] = 0;
                    for (int j = 0; (j < 3); j++)
                        AUC[i, j] = 0;
                }

                aMITesDecoder = new MITesDecoder();
                aMITesHRAnalyzer = new MITesHRAnalyzer(aMITesDecoder);
                aMITesLoggerReader = new MITesLoggerReader(aMITesDecoder, aDataDirectory + "\\" + MITES_SUBDIRECTORY);
            }

            #endregion Setup MITes Data


            #region Scan Annotation Records

            int channel = 0, x = 0, y = 0, z = 0;
            double unixtimestamp = 0.0;
            string current_activity = "";
            int activityIndex = 0;
            AXML.AnnotatedRecord annotatedRecord = null;
            if (aannotation != null)
            {

                annotatedRecord = ((AXML.AnnotatedRecord)aannotation.Data[activityIndex]);

                for (int j = 0; (j < annotatedRecord.Labels.Count); j++)
                {
                    if (j == annotatedRecord.Labels.Count - 1)
                        current_activity += "";
                    else
                        current_activity += ",";
                }
            }

            #endregion


            #region Setup Wockets Data

            int[] lastDecodedIndex = null;
            WocketsController wcontroller = null;
            double[] wunixtimestamp = null;

            //Initialize Wockets Sampling Rate 
            int SAMPLING_RATE = 0;

            //Size of the moving average 
            int RM_DURATION = 1000;
            int RM_SIZE = 0;

            if ((Directory.Exists(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY)) && (Directory.GetFiles(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY).Length > 0))
            {
                wcontroller = new WocketsController("", "", "");
                CurrentWockets._Controller = wcontroller;
                wcontroller.FromXML(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\SensorData.xml");


                //Set Wockets Sampling Rate & size of moving average 
                //---Check with Fahd how to handle the case when more than one sensor ---
                if (wcontroller._Sensors.Count > 0)
                {
                    SAMPLING_RATE = wcontroller._Sensors[0]._SamplingRate;
                    RM_SIZE = (RM_DURATION / 1000) * SAMPLING_RATE;
                }



                for (int r = 0; (r < wcontroller._Decoders.Count); r++)
                    wcontroller._Decoders[r].Initialize();
                wunixtimestamp = new double[wcontroller._Sensors.Count];


                for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                {
                    wcontroller._Sensors[i]._RootStorageDirectory = aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\data\\raw\\PLFormat\\";
                    wunixtimestamp[i] = 0.0;
                }

                lastDecodedIndex = new int[wcontroller._Sensors.Count];

                wactivityCountCSVs = new StreamWriter[wcontroller._Sensors.Count];
                wsamplingCSVs = new StreamWriter[wcontroller._Sensors.Count];
                waveragedRaw = new StreamWriter[wcontroller._Sensors.Count];
                waucCSVs = new StreamWriter[wcontroller._Sensors.Count];
                wvmagCSVs = new StreamWriter[wcontroller._Sensors.Count];
                wrmCSVs = new StreamWriter[wcontroller._Sensors.Count];


                /* Write Wockets raw data to csv files */
                WocketsController wc = new WocketsController("", "", "");
                CurrentWockets._Controller = wc;
                wc.FromXML(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\SensorData.xml");
                for (int r = 0; (r < wc._Decoders.Count); r++)
                    wc._Decoders[r].Initialize();


                int[] wocketsSR = new int[wcontroller._Sensors.Count];

                for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                {
                    int sensor_id = wcontroller._Sensors[i]._ID;
                    int wocketSR = 0;
                    long prevWocketTS = 0;
                    int totalseconds = 0;
                    wc._Sensors[i]._RootStorageDirectory = aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\data\\raw\\PLFormat\\";
                    if (CSVProgress == "")
                        CSVProgress = "Generating Raw Data File for Wocket " + sensor_id.ToString("00");

                    //try
                    //{
                    //TODO: check this line: Write out raw data
                    //TextWriter tw = null;

                    //try
                    //{
                    TextWriter tw = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "Wocket_" + sensor_id.ToString("00") + "_RawData_" + wcontroller._Sensors[i]._Location.Replace(' ', '-') + ".csv");
                    //}
                    //catch
                    //{
                    //if (tw != null)
                    // {
                    //     tw.Flush();
                    //     tw.Close();
                    //}
                    // tw = null;
                    //}


                    int lastDecodedPacket = 0;

                    while (wc._Sensors[i].Load())
                    {
                        if (wc._Sensors[i]._Decoder._Head == 0)
                            lastDecodedPacket = wc._Sensors[i]._Decoder._Data.Length - 1;
                        else
                            lastDecodedPacket = wc._Sensors[i]._Decoder._Head - 1;

                        Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[lastDecodedPacket];

                        //added by selene
                        //if( tw != null)
                        tw.WriteLine(data.UnixTimeStamp + "," + data._X + "," + data._Y + "," + data._Z);

                        long currentTS = (long)(data.UnixTimeStamp / 1000.0);
                        if ((currentTS - prevWocketTS) < 1)
                            wocketSR++;
                        if ((prevWocketTS > 0) & (currentTS - prevWocketTS) >= 1)
                            totalseconds += (int)(currentTS - prevWocketTS);
                        prevWocketTS = currentTS;
                    }
                    wocketsSR[i] = (int)Math.Round((double)wocketSR / (double)totalseconds);

                    //added by selene
                    //if (tw != null)
                    //{
                    tw.Flush();
                    tw.Close();
                    //}

                    //}
                    //catch(Exception e)
                    //{ }

                    //--------------------------------------------------------------

                    string location = wcontroller._Sensors[i]._Location.Replace(' ', '-');
                    lastDecodedIndex[i] = 0;
                    wactivityCountCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + sensor_id.ToString("00") + "_SAD_" + location + ".csv");
                    wactivityCountCSVs[sensor_id].WriteLine(csv_line1);
                    wrmCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + sensor_id.ToString("00") + "_RM_" + location + ".csv");
                    wrmCSVs[sensor_id].WriteLine(csv_line1);
                    waucCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + sensor_id.ToString("00") + "_AUC_" + location + ".csv");
                    waucCSVs[sensor_id].WriteLine(csv_line1);
                    wvmagCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + sensor_id.ToString("00") + "_VMAG_" + location + ".csv");
                    wvmagCSVs[sensor_id].WriteLine(csv_line6);
                    waveragedRaw[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + sensor_id.ToString("00") + "_1s-RawMean_" + location + ".csv");
                    waveragedRaw[sensor_id].WriteLine(csv_line1);
                    wsamplingCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + sensor_id.ToString("00") + "_SampleRate_" + location + ".csv");
                    wsamplingCSVs[sensor_id].WriteLine(csv_line2);


                    // Add the headers to the "Summary Data" master file
                    master_csv_header += ",Wocket" + sensor_id.ToString("00") + "_SR," + "Wocket" + sensor_id.ToString("00") + "_AVRaw_X," +
                        "Wocket" + sensor_id.ToString("00") + "_AVRaw_Y," + "Wocket" + sensor_id.ToString("00") + "_AVRaw_Z," + "Wocket" + sensor_id.ToString("00") + "_SAD_X," +
                        "Wocket" + sensor_id.ToString("00") + "_SAD_Y," + "Wocket" + sensor_id.ToString("00") + "_SAD_Z," + "Wocket" + sensor_id.ToString("00") + "_AUC_X," +
                        "Wocket" + sensor_id.ToString("00") + "_AUC_Y," + "Wocket" + sensor_id.ToString("00") + "_AUC_Z," + "Wocket" + sensor_id.ToString("00") + "_AUC_XYZ," +
                        "Wocket" + sensor_id.ToString("00") + "_RM_X," + "Wocket" + sensor_id.ToString("00") + "_RM_Y," + "Wocket" + sensor_id.ToString("00") + "_RM_Z," +
                        "Wocket" + sensor_id.ToString("00") + "_RM_SIZE," + "Wocket" + sensor_id.ToString("00") + "_VMAG";
                }

                // wc.Dispose();







                /* Correct the wockets timestamps */

                TextReader[] wocketsTR = new TextReader[wcontroller._Sensors.Count];
                TextWriter[] wocketsTW = new TextWriter[wcontroller._Sensors.Count];
                int LoadedSeconds = 10;
                int[] compensatedWindows = new int[10];
                int uncompensatedWindows = 0;
                int correctWindows = 0;


                for (int k = 0; (k < wcontroller._Sensors.Count); k++)
                {
                    wocketsTR[k] = new StreamReader(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "Wocket_" + wcontroller._Sensors[k]._ID.ToString("00") + "_RawData_" + wcontroller._Sensors[k]._Location.Replace(' ', '-') + ".csv");
                    wocketsTW[k] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "Wocket_" + wcontroller._Sensors[k]._ID.ToString("00") + "_RawCorrectedData_" + wcontroller._Sensors[k]._Location.Replace(' ', '-') + ".csv");

                    ArrayList[] loadedData = new ArrayList[LoadedSeconds];
                    long[] loadedDataTime = new long[LoadedSeconds];
                    for (int m = 0; (m < LoadedSeconds); m++)
                        loadedData[m] = new ArrayList();
                    int loadedIndex = 0;
                    string dataline = "";
                    long lastSecond = 0;
                    int nextCorrected = 0;
                    long nextCorrectedTime = 0;
                    double delta = 1000.0 / wocketsSR[k];
                    double recordTime = 0;

                    if (CSVProgress == "")
                        CSVProgress = "Correcting Timestamps for Raw Data File for Wocket " + wcontroller._Sensors[k]._ID.ToString("00");

                    while ((dataline = wocketsTR[k].ReadLine()) != null)
                    {
                        string[] wocketTokens = dataline.Split(',');
                        int wocketX = Convert.ToInt32(wocketTokens[1]);
                        int wocketY = Convert.ToInt32(wocketTokens[2]);
                        int wocketZ = Convert.ToInt32(wocketTokens[3]);
                        long unixtime = (long)(Convert.ToDouble(wocketTokens[0]) / 1000.0);

                        // if ((k == 2) && (unixtime >= 1255347111))
                        //   Console.Write(""); 

                        if (nextCorrectedTime == 0)
                            nextCorrectedTime = unixtime;
                        if (lastSecond == 0)
                            lastSecond = unixtime;

                        //if a new second is being loaded
                        if (lastSecond != unixtime)
                        {

                            //check if you have enough to correct
                            while ((unixtime - nextCorrectedTime) > 8)
                            {
                                bool compensated = false;
                                int compensatedCounter = 0;
                                //if the data needs compensation
                                if (loadedData[nextCorrected].Count < (wocketsSR[k] - 2)) //lower number of samples
                                {
                                    compensatedCounter = 1;
                                    //check if seconds that follow compensate for the current second
                                    int dataCounter = loadedData[nextCorrected].Count;
                                    int expectedCompensatedSR = 0;
                                    for (int r = 1; (r < 8); r++)
                                    {

                                        int adjacentDataIndex = (nextCorrected + r) % LoadedSeconds;
                                        if (loadedData[adjacentDataIndex].Count > 0)
                                        {
                                            string[] adjTokens = ((string)loadedData[adjacentDataIndex][0]).Split(',');
                                            long adjunixtime = (long)(Convert.ToDouble(adjTokens[0]) / 1000.0);
                                            if ((adjunixtime - unixtime) < 8)
                                                dataCounter += loadedData[adjacentDataIndex].Count;
                                            compensatedCounter++;
                                            if ((dataCounter / (r + 1)) >= (wocketsSR[k] - 10))
                                            {
                                                expectedCompensatedSR = dataCounter / (r + 1);
                                                compensated = true;

                                                break;
                                            }
                                        }
                                        else
                                            compensatedCounter++;

                                    }

                                    //use data points from adjacent seconds
                                    if (compensated)
                                    {
                                        compensatedWindows[compensatedCounter] = compensatedWindows[compensatedCounter] + 1;
                                        //int totalCompensatedPoints = loadedData[nextCorrected].Count;
                                        int correctingArray = nextCorrected;
                                        // if (compensatedCounter > 3)
                                        //     Console.Write("");
                                        //go through all arrays that were used in correction
                                        for (int r = 0; (r < compensatedCounter); r++)
                                        {
                                            correctingArray = (nextCorrected + r) % LoadedSeconds;

                                            for (int m = r + 1; (m < compensatedCounter); m++)
                                            {
                                                int compenstingArray = (nextCorrected + m) % LoadedSeconds;
                                                int totalCompensatedPoints = loadedData[correctingArray].Count;
                                                int compensatingArraySize = loadedData[compenstingArray].Count;
                                                for (int n = 0; (n < compensatingArraySize); n++)
                                                {
                                                    //always remove the top entry of the array to do the correction and preserve the order
                                                    loadedData[correctingArray].Add(loadedData[compenstingArray][0]);
                                                    loadedData[compenstingArray].RemoveAt(0);
                                                    //wocketsTW[k].WriteLine(recordTime + "," + recordTokens[1] + "," + recordTokens[2] + "," + recordTokens[3]);
                                                    //recordTime += delta;
                                                    totalCompensatedPoints++;
                                                    if (expectedCompensatedSR == totalCompensatedPoints)
                                                        break;
                                                }
                                                if (expectedCompensatedSR == totalCompensatedPoints)
                                                    break;
                                            }
                                        }
                                    }
                                    else
                                        uncompensatedWindows++;
                                }
                                else
                                    correctWindows++;

                                //Write out all data that got time corrected
                                //including where we have taken data points
                                if (!compensated) //no compensation
                                {

                                    recordTime = nextCorrectedTime * 1000.0;
                                    for (int n = 0; (n < loadedData[nextCorrected].Count); n++)
                                    {
                                        string[] recordTokens = ((string)loadedData[nextCorrected][n]).Split(',');
                                        wocketsTW[k].WriteLine(recordTime + "," + recordTokens[1] + "," + recordTokens[2] + "," + recordTokens[3]);
                                        recordTime += delta;
                                    }
                                    loadedData[nextCorrected] = new ArrayList();
                                    nextCorrected = (nextCorrected + 1) % LoadedSeconds;
                                    nextCorrectedTime++;
                                }
                                else
                                {
                                    int correctionIndex = 0;
                                    int correctionLength = compensatedCounter;

                                    while (correctionIndex != compensatedCounter)
                                    {
                                        recordTime = nextCorrectedTime * 1000.0;
                                        for (int n = 0; (n < loadedData[nextCorrected].Count); n++)
                                        {
                                            string[] recordTokens = ((string)loadedData[nextCorrected][n]).Split(',');
                                            wocketsTW[k].WriteLine(recordTime + "," + recordTokens[1] + "," + recordTokens[2] + "," + recordTokens[3]);
                                            recordTime += delta;
                                        }
                                        loadedData[nextCorrected] = new ArrayList();
                                        nextCorrected = (nextCorrected + 1) % LoadedSeconds;
                                        nextCorrectedTime++;
                                        correctionIndex++;
                                    }

                                    compensated = false;
                                }
                            }


                            while ((lastSecond < unixtime) && (unixtime != 0))
                            {

                                loadedIndex++;
                                if (loadedIndex == LoadedSeconds)
                                    loadedIndex = 0;
                                loadedData[loadedIndex] = new ArrayList();
                                lastSecond++;
                            }
                        }




                        loadedData[loadedIndex].Add(unixtime + "," + wocketX + "," + wocketY + "," + wocketZ);
                        lastSecond = unixtime;
                        //nextCorrectedTime = lastSecond-8;
                    }

                    wocketsTW[k].Close();
                }


                //create some counters for activity counts
                waverageX = new int[wcontroller._Sensors.Count];
                waverageY = new int[wcontroller._Sensors.Count];
                waverageZ = new int[wcontroller._Sensors.Count];

                waverageRawX = new int[wcontroller._Sensors.Count];
                waverageRawY = new int[wcontroller._Sensors.Count];
                waverageRawZ = new int[wcontroller._Sensors.Count];

                wprevX = new int[wcontroller._Sensors.Count];
                wprevY = new int[wcontroller._Sensors.Count];
                wprevZ = new int[wcontroller._Sensors.Count];
                wacCounters = new int[wcontroller._Sensors.Count];

                //JPN: Dimension array used to store number of samples per minute for WRAC
                wWRACCounterMinute = new int[wcontroller._Sensors.Count];

                for (int k = 0; (k < wprevX.Length); k++)
                {
                    wprevX[k] = -1;
                    wprevY[k] = -1;
                    wprevZ[k] = -1;

                }

                //Initialize arrays based on number of sensors
                wrawData = new int[wcontroller._Sensors.Count, 3, RM_SIZE];
                for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                    for (int j = 0; (j < 3); j++)
                        for (int k = 0; (k < RM_SIZE); k++)
                            wrawData[i, j, k] = -1;
                wtimeData = new long[wcontroller._Sensors.Count, RM_SIZE];
                wAUC = new int[wcontroller._Sensors.Count, 3];

                //JPN: Dimension array to store combined AUC counts for all axes
                wAUCXYZ = new int[wcontroller._Sensors.Count];

                wVMAG = new double[wcontroller._Sensors.Count];
                whead = new int[wcontroller._Sensors.Count];

                wRMX = new double[wcontroller._Sensors.Count];
                wRMY = new double[wcontroller._Sensors.Count];
                wRMZ = new double[wcontroller._Sensors.Count];
                wRMSize = new int[wcontroller._Sensors.Count];


                for (int i = 0; (i < whead.Length); i++)
                {
                    whead[i] = 0;
                    wRMX[i] = 0;
                    wRMY[i] = 0;
                    wRMZ[i] = 0;
                    wRMSize[i] = 0;
                    wVMAG[i] = 0;
                    for (int j = 0; (j < 3); j++)
                        wAUC[i, j] = 0;

                    //JPN: Initialize array to store combined AUC counts for all axes
                    wAUCXYZ[i] = 0;
                }
            }
            #endregion Setup Wockets Data



            #region Read Summary data

            //string[] file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY+"\\data\\summary", "Sensor*.csv");
            string[] subdirectories = null;
            if (Directory.Exists(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\data\\summary"))
            {
                subdirectories = Directory.GetDirectories(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\data\\summary");
                ArrayList[] files = new ArrayList[CurrentWockets._Controller._Sensors.Count];
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                    files[i] = new ArrayList();
                foreach (string subdirectory in subdirectories)
                {
                    for (int i = 0; i < 30; i++)
                    {
                        if (Directory.Exists(subdirectory + "\\" + i))
                        {
                            for (int k = 0; (k < CurrentWockets._Controller._Sensors.Count); k++)
                            {
                                string[] matchingFiles = Directory.GetFiles(subdirectory + "\\" + i, "SummaryAC-*" + k + ".csv");
                                for (int j = 0; (j < matchingFiles.Length); j++)
                                    files[k].Add(matchingFiles[j]);
                            }
                        }
                    }
                }

                //JPN: Dimension textwriter array for outputting WFAC values
                wWFACSummaryCSV = new TextWriter[CurrentWockets._Controller._Sensors.Count];

                //JPN: Dimension textwriter array for outputting WRAC values
                wWRACSummaryCSV = new TextWriter[CurrentWockets._Controller._Sensors.Count];

                //JPN: Dimension array for storing WFAC output data
                wWFACData = new Hashtable[CurrentWockets._Controller._Sensors.Count];

                //JPN: Dimension array for storing WRAC output data
                wWRACData = new Hashtable[CurrentWockets._Controller._Sensors.Count];

                //JPN: Dimension array for storing WRAC running summs
                wWRACSummation = new int[CurrentWockets._Controller._Sensors.Count];

                //JPN: Dimension array for storing WRAC sampling rates for each minute
                wWRACSamplingRate = new Hashtable[CurrentWockets._Controller._Sensors.Count];

                prevUnixTime = new double[CurrentWockets._Controller._Sensors.Count];
                summaryStartUnixTime = new double[CurrentWockets._Controller._Sensors.Count];

                //JPN: Initialize previous line array for PLOT WFAC data
                prevWFACPlotDataLine = new string[CurrentWockets._Controller._Sensors.Count];
                for (int i = 0; i < prevWFACPlotDataLine.Length; i++)
                {
                    prevWFACPlotDataLine[i] = "0";
                }

                //JPN: Initialize previous line array for PLOT WRAC data
                prevWRACPlotDataLine = new string[CurrentWockets._Controller._Sensors.Count];
                for (int i = 0; i < prevWRACPlotDataLine.Length; i++)
                {
                    prevWRACPlotDataLine[i] = "0";
                }

                //JPN: TEMP: Initialize previous line array for PLOT WRAC Sample Count
                prevWRACPlotSampleCount = new string[CurrentWockets._Controller._Sensors.Count];
                for (int i = 0; i < prevWRACPlotSampleCount.Length; i++)
                {
                    prevWRACPlotSampleCount[i] = "0";
                }

                try
                {

                    for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                    {
                        wWFACSummaryCSV[i] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + i.ToString("00") + "_WFAC.csv");

                        //JPN: Initialize textwriter array for outputting WRAC values for each sensor
                        wWRACSummaryCSV[i] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + i.ToString("00") + "_WRAC.csv");

                        wWFACData[i] = new Hashtable();

                        //JPN: Initialze array for storing WRAC values for each sensor
                        wWRACData[i] = new Hashtable();

                        //JPN: Initialize array for storing WRAC running sums for each sensor
                        wWRACSummation[i] = 0;

                        //JPN: Initialize array for storing WRAC sampling rates for each minute
                        wWRACSamplingRate[i] = new Hashtable();

                        prevUnixTime[i] = -1;
                        summaryStartUnixTime[i] = 0;
                    }
                    for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                    {
                        if (CSVProgress == "")
                            CSVProgress = "Processing Summary Data " + (i + 1);

                        foreach (string filename in files[i])
                        {
                            TextReader summaryReader = null;
                            string summary_line = "";
                            double summaryUnixTime = 0;
                            DateTime summaryTime = new DateTime();

                            summaryReader = new StreamReader(filename);
                            summary_line = summaryReader.ReadLine();//read first line

                            // JPN: These are the headers from the log file which will populate the tokens array
                            // [0] time when data is retrieved from the decoder and written to the file
                            // [1] index in the activity count array in the decoder: nextACindex (repeats until Decoders[].ActivityCountIndex)
                            // [2] AC sequence number according to the wocket
                            // [3] AC time stamp coming from the phone - human-readable version of the AC UnixTimeStamp
                            // [4] AC time stamp coming from the phone - UnixTimeStamp value
                            // [5] AC value

                            do
                            {
                                try
                                {
                                    if (summary_line == null)
                                        break;
                                    tokens = summary_line.Split(',');
                                    if (tokens.Length == 6)
                                    {
                                        summaryUnixTime = Convert.ToDouble(tokens[4]);//UnixTime.GetUnixTime(actigraphTime);
                                        UnixTime.GetDateTime((long)(summaryUnixTime), out summaryTime);
                                        string summaryKey = summaryTime.Year + "-" + summaryTime.Month + "-" + summaryTime.Day + "-" + summaryTime.Hour + "-" + summaryTime.Minute + "-" + summaryTime.Second;
                                        string summaryLine = tokens[5];
                                        if (summaryStart == null)
                                            summaryStart = summaryTime.Year + "/" + summaryTime.Month + "/" + summaryTime.Day + " " + summaryTime.Hour + ":" + summaryTime.Minute + ":" + summaryTime.Second;
                                        if (summaryStartUnixTime[i] <= 0)
                                            summaryStartUnixTime[i] = summaryUnixTime;
                                        wWFACData[i].Add(summaryKey, summaryLine);
                                    }
                                }
                                catch (Exception e)
                                {
                                }
                            } while ((summary_line = summaryReader.ReadLine()) != null);
                        }
                    }
                }
                catch (Exception e)
                {
                }
            }
            #endregion Read Summary data


            #region Actigraph Summary Header

            for (int i = 0; (i < actigraphData.Length); i++)
            {
                if (actigraphType[i] == "GT3X" || actigraphType[i] == "GT3X+")
                {
                    master_csv_header += ",Actigraph" + (i + 1) + "_X,Actigraph" + (i + 1) + "_Y,Actigraph" + (i + 1) + "_Z";
                    //PLOT values for actigraph activity counts
                    master_csv_header += ",PLOT_Actigraph" + (i + 1) + "_X,PLOT_Actigraph" + (i + 1) + "_Y,PLOT_Actigraph" + (i + 1) + "_Z" +
                        ",PLOT_Actigraph" + (i + 1) + "_XYZ";
                    actigraphCSV[i].WriteLine(actigraph_csv_header_gtx);
                }
                else if (actigraphType[i] == "GT1M")
                {
                    master_csv_header += ",Actigraph" + (i + 1) + "_X,Actigraph" + (i + 1) + "_Y";
                    actigraphCSV[i].WriteLine(actigraph_csv_header_gt1m);
                }
                else
                {
                    master_csv_header += ",Actigraph" + (i + 1);
                    actigraphCSV[i].WriteLine(actigraph_csv_header);
                }
            }

            #endregion Actigraph Summary Header

            #region Wockets Activity Counts Header

            //JPN: Add CSV headers for Wocket Firmware Activity Counts (WFAC)
            if (wWFACData != null)
            {
                for (int i = 0; (i < wWFACData.Length); i++)
                {
                    master_csv_header += ",Wocket" + i.ToString("00") + "_PerMinute_WFAC";
                    wWFACSummaryCSV[i].WriteLine(summary_csv_header);
                }
            }

            //JPN: Add CSV headers for Wocket Raw Activity Counts (WRAC)
            if (wWRACData != null)
            {
                for (int i = 0; (i < wWRACData.Length); i++)
                {
                    master_csv_header += ",Wocket" + i.ToString("00") + "_PerMinute_WRAC";
                    wWRACSummaryCSV[i].WriteLine(summary_csv_header);
                }
            }

            //JPN: Add CSV headers for Plottable Firmware Raw Activity Counts (WFAC)
            if (wWFACData != null)
                for (int i = 0; (i < wWFACData.Length); i++)
                    master_csv_header += ",Wocket" + i.ToString("00") + "_PLOT_PerMinute_WFAC";

            //JPN: Add CSV headers for Plottable Wocket Raw Activity Counts (WRAC)
            if (wWRACData != null)
                for (int i = 0; (i < wWRACData.Length); i++)
                    master_csv_header += ",Wocket" + i.ToString("00") + "_PLOT_PerMinute_WRAC";

            //JPN: TEMP: Add CSV headers for Plottable Wocket Raw Activity Counts (WRAC)
            if (wWRACData != null)
                for (int i = 0; (i < wWRACData.Length); i++)
                    master_csv_header += ",Wocket" + i.ToString("00") + "_PLOT_PerMinute_SampleCount";

            #endregion Wockets Activity Counts Header

            #region Other Sensors Headers

            if (sensewearFound)
                master_csv_header += ",SensewearSR,Sensewear_AVTranAcc,Senserwear_AVLongAcc,Sensewear_AVForAcc";
            else if (sensewearVanderbiltFound)
                master_csv_header += ",SensewearSR,Sensewear_numpeaks_accelerometer_transverse,Sensewear_numpeaks_accelerometer_longitudinal,Sensewear_heat_flux_average_original_rate,Sensewear_skin_temp_average_original_rate,Sensewear_transverse_accelerometer_average,Sensewear_longitudinal_accelerometer_average,Sensewear_cover_temp_average,Sensewear_transverse_accelerometer_MAD_graphable,Sensewear_longitudinal_accelerometer_MAD_graphable,Sensewear_STEPS,Sensewear_gsr_average,Sensewear_energy_expenditure_per_minute";
            if (zephyrFound)
                master_csv_header += ",ZephyrHeart Rate Data,ZephyrECG - Amplitude Data,ZephyrECG - Noise Data,ZephyrRES - Breathing Wave Amplitude (V) Data,ZephyrRES - Respiration Rate Data,ZephyrTEM - Skin Temperature Data,ZephyrBAT - Battery Voltage (V) Data,ZephyrPOS - Posture Data,ZephyrACC - Activity Data,ZephyrACC - Peak Acceleration (g) Data,ZephyrACC - Vertical Acc Minimum (g) Data,ZephyrACC - Vertical Acc Peak (g) Data,ZephyrACC - Lateral Acc Minimum (g) Data,ZephyrACC - Lateral Acc Peak (g) Data,ZephyrACC - Sagittal Acc Minimum (g) Data,ZephyrACC - Sagittal Acc Peak (g)";
            if (oxyconFound)
                master_csv_header += ",OxyconHR,OxyconBF,OxyconVE,OxyconVO2,OxyconVO2kg,OxyconMET,OxyconEE,OxyconRER";//OxyconRER,Oxyconttot,Oxycontex";
            if (omronFound)
                master_csv_header += ",OmronSteps";
            if (columbiaFound)
                master_csv_header += ",ColumbiaX,ColumbiaY,ColumbiaZ,ColumbiaFlow,ColumbiaValve";
            if (gpsFound)
                master_csv_header += ",GPSLatitude,GPSLongitude,GPSSpeed,GPSAltitude";
            if (rtiFound)
                master_csv_header += ",RTIX,RTIY,RTIZ,RTI_AUC_X,RTI_AUC_Y,RTI_AUC_Z,RTI_AUC_XYZ";
            if (rt3Found)
                master_csv_header += ",RT3_SR,RT3_Total_Calories,RT3_Activity_Calories,RT3_VM,RT3_ActCntsX,RT3_ActCntsY,RT3_ActCntsZ";

            masterCSV.WriteLine(master_csv_header);
            hrCSV.WriteLine(hr_csv_header);
            if (sensewearCSV != null)
                if (sensewearFound)
                    sensewearCSV.WriteLine(sensewear_csv_header);
                else if (sensewearVanderbiltFound)
                    sensewearCSV.WriteLine(sensewear_csv_header_vanderbilt);

            if ((zephyrCSV != null) && (zephyrFound))
                zephyrCSV.WriteLine(zephyr_csv_header);
            if ((oxyconCSV != null) && (oxyconFound))
                oxyconCSV.WriteLine(oxycon_csv_header);
            if ((omronCSV != null) && (omronFound))
                omronCSV.WriteLine(omron_csv_header);
            if ((columbiaCSV != null) && (columbiaFound))
                columbiaCSV.WriteLine(columbia_csv_header);
            if ((gpsCSV != null) && (gpsFound))
                gpsCSV.WriteLine(gps_csv_header);
            if ((rtiCSV != null) && (rtiFound))
                rtiCSV.WriteLine(rti_csv_header);
            if ((rt3CSV != null) && (rt3Found))
                rt3CSV.WriteLine(rt3_csv_header);


            #endregion Other Sensors Headers


            int year = 0;

            int month = 0;
            int day = 0;
            int startyear = 2050;
            int startmonth = 1;
            int startday = 1;
            int starthr = 1;
            int startmin = 1;
            int startsec = 1;

            int endyear = 1971;
            int endmonth = 1;
            int endday = 1;
            int endhr = 1;
            int endmin = 59;
            int endsec = 59;

            DateTime startDateTime = new DateTime(startyear, startmonth, startday, starthr, startmin, startsec);
            DateTime endDateTime = new DateTime(endyear, endmonth, endday, endhr, endmin, endsec);

            #region If there is MITES data

            //check mites start and end times
            if (aMITesDecoder != null)
            {
                string rawDirectory = aDataDirectory + "\\" + MITES_SUBDIRECTORY + "\\data\\raw\\PLFormat";


                if (Directory.Exists(rawDirectory) == false)
                    return;

                subdirectories = Directory.GetDirectories(rawDirectory);
                foreach (string subdirectory in subdirectories)
                {
                    string[] datetokens = subdirectory.Split('\\');
                    datetokens = datetokens[datetokens.Length - 1].Split('-');
                    year = Convert.ToInt32(datetokens[0]);
                    month = Convert.ToInt32(datetokens[1]);
                    day = Convert.ToInt32(datetokens[2]);

                    /*  if ((startyear == 0) || (year < startyear))
                          startyear = year;
                      if ((endyear == 0) || (year > endyear))
                          endyear = year;

                      if ((startmonth == 0) || (month < startmonth))
                          startmonth = month;
                      if ((endmonth == 0) || (month > endmonth))
                          endmonth = month;

                      if ((startday == 0) || (day < startday))
                          startday = day;
                      if ((endday == 0) || (day > endday))
                          endday = day;*/


                    for (int i = 0; i < 30; i++)
                    {
                        if (Directory.Exists(subdirectory + "\\" + i))
                        {
                            int hr = i;
                            /* if (hr < starthr)
                                 starthr = hr;
                             if (hr > endhr)
                                 endhr = hr;*/
                            DateTime d = new DateTime(year, month, day, hr, 0, 0);
                            if (d.Subtract(startDateTime).TotalSeconds < 0)
                                startDateTime = d;
                            if (d.Subtract(endDateTime).TotalSeconds > 0)
                                endDateTime = d;
                        }

                    }
                }
            }

            #endregion If there is MITES data

            #region If there is Wockets data

            //check wockets start and end times
            if (wcontroller != null)
            {
                string rawDirectory = aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\data\\raw\\PLFormat";


                if (Directory.Exists(rawDirectory) == false)
                    return;

                subdirectories = Directory.GetDirectories(rawDirectory);
                foreach (string subdirectory in subdirectories)
                {
                    string[] datetokens = subdirectory.Split('\\');
                    datetokens = datetokens[datetokens.Length - 1].Split('-');
                    year = Convert.ToInt32(datetokens[0]);
                    month = Convert.ToInt32(datetokens[1]);
                    day = Convert.ToInt32(datetokens[2]);

                    /* if ((startyear == 0) || (year < startyear))
                         startyear = year;
                     if ((endyear == 0) || (year > endyear))
                         endyear = year;

                     if ((startmonth == 0) || (month < startmonth))
                         startmonth = month;
                     if ((endmonth == 0) || (month > endmonth))
                         endmonth = month;

                     if ((startday == 0) || (day < startday))
                         startday = day;
                     if ((endday == 0) || (day > endday))
                         endday = day;
                     */

                    for (int i = 0; i < 30; i++)
                    {
                        if (Directory.Exists(subdirectory + "\\" + i))
                        {
                            int hr = i;
                            /* if (hr < starthr)
                                 starthr = hr;
                             if (hr > endhr)
                                 endhr = hr;*/

                            DateTime d = new DateTime(year, month, day, hr, 0, 0);
                            if (d.Subtract(startDateTime).TotalSeconds < 0)
                                startDateTime = d;
                            d = new DateTime(year, month, day, hr, 59, 59);
                            if (d.Subtract(endDateTime).TotalSeconds > 0)
                                endDateTime = d;
                        }

                    }
                }
            }//if wockets data is not present and merging only actigraph data
            else
            {
                if ((actigraphEndTimes[0] != null) && (actigraphStartTimes[0] != null))
                {
                    startDateTime = actigraphStartTimes[0];
                    endDateTime = actigraphEndTimes[0];
                }
            }


            #endregion If there is Wockets data


            //sele check
            #region check annotation start and end times


            if (aannotation != null)
            {
                AXML.AnnotatedRecord record = ((AXML.AnnotatedRecord)aannotation.Data[0]);
                year = Convert.ToInt32(record.StartDate.Split('-')[2]);
                month = Convert.ToInt32(record.StartDate.Split('-')[0]);
                day = Convert.ToInt32(record.StartDate.Split('-')[1]);

                DateTime d = new DateTime(year, month, day, record.StartHour, 0, 0);
                if (d.Subtract(startDateTime).TotalSeconds < 0)
                    startDateTime = d;

                /* if ((startyear == 0) || (year < startyear))
                     startyear = year;

                 if ((startmonth == 0) || (month < startmonth))
                     startmonth = month;
                 if ((startday == 0) || (day < startday))
                     startday = day;

                 if (record.StartHour < starthr)
                     starthr = record.StartHour;
                 */
                record = ((AXML.AnnotatedRecord)aannotation.Data[aannotation.Data.Count - 1]);
                year = Convert.ToInt32(record.StartDate.Split('-')[2]);
                month = Convert.ToInt32(record.StartDate.Split('-')[0]);
                day = Convert.ToInt32(record.StartDate.Split('-')[1]);
                d = new DateTime(year, month, day, record.EndHour, 59, 59);
                if (d.Subtract(endDateTime).TotalSeconds > 0)
                    endDateTime = d;
                /*
                if ((endyear == 0) || (year > endyear))
                    endyear = year;
                if ((endmonth == 0) || (month > endmonth))
                    endmonth = month;
                if ((endday == 0) || (day > endday))
                    endday = day;
                if (record.EndHour > endhr)
                    endhr = record.EndHour;
                if ((record.EndMinute < 54) && (record.EndMinute < endmin))
                    endmin = record.EndMinute + 5;
                 */
            }


            #endregion



            if (wWFACData != null)
            {
                for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                {
                    DateTime d = new DateTime();
                    UnixTime.GetDateTime((long)summaryStartUnixTime[i], out d);

                    if (d.Subtract(startDateTime).TotalSeconds < 0)
                        startDateTime = d;

                    /*if ((startyear == 0) || (d.Year < startyear))
                        startyear = d.Year;

                    if ((startmonth == 0) || (d.Month < startmonth))
                        startmonth = d.Month;

                    if ((startday == 0) || (d.Day < startday))
                        startday = d.Day;

                    if ((starthr == 0) || (d.Hour < starthr))
                        starthr = d.Hour;*/

                }
            }


            DateTime currentDateTime = startDateTime;
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0); ;
            TimeSpan diff;
            string timestamp = "";
            double currentUnixTime = 0;







            #region Cleanup CSV lines


            string master_csv_line = "";
            string hr_csv_line = "";

            string[] actigraph_csv_line = new string[actigraphData.Length];
            for (int i = 0; (i < actigraphData.Length); i++)
                actigraph_csv_line[i] = "";

            string[] summary_csv_line = null;
            if (wWFACData != null)
            {
                summary_csv_line = new string[wWFACData.Length];
                for (int i = 0; (i < wWFACData.Length); i++)
                    summary_csv_line[i] = "";
            }

            string sensewear_csv_line = "";
            string zephyr_csv_line = "";
            string oxycon_csv_line = "";
            string omron_csv_line = "";
            string columbia_csv_line = "";
            string gps_csv_line = "";
            string rti_csv_line = "";
            string rt3_csv_line = "";


            #endregion Initialize CSV lines



            TextReader[] wocketsTR1 = null;
            if (wcontroller != null)
            {
                wocketsTR1 = new TextReader[wcontroller._Sensors.Count];
                for (int k = 0; (k < wcontroller._Sensors.Count); k++)
                    wocketsTR1[k] = new StreamReader(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "Wocket_" + wcontroller._Sensors[k]._ID.ToString("00") + "_RawCorrectedData_" + wcontroller._Sensors[k]._Location.Replace(' ', '-') + ".csv");
            }



            while (((TimeSpan)endDateTime.Subtract(currentDateTime)).TotalSeconds >= 0)
            {
                string key = currentDateTime.Year + "-" + currentDateTime.Month + "-" + currentDateTime.Day + "-" + currentDateTime.Hour + "-" + currentDateTime.Minute + "-" + currentDateTime.Second;
                diff = currentDateTime.Subtract(origin);
                timestamp = diff.TotalMilliseconds + "," + currentDateTime.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                currentUnixTime = diff.TotalMilliseconds;


                #region Setup prefix of CSV lines

                master_csv_line = timestamp;
                hr_csv_line = timestamp;
                for (int i = 0; (i < actigraphData.Length); i++)
                    actigraph_csv_line[i] = timestamp;

                if (wWFACData != null)
                {
                    for (int i = 0; (i < wWFACData.Length); i++)
                        summary_csv_line[i] = timestamp;
                }
                sensewear_csv_line = timestamp;
                zephyr_csv_line = timestamp;
                oxycon_csv_line = timestamp;
                omron_csv_line = timestamp;
                columbia_csv_line = timestamp;
                gps_csv_line = timestamp;
                rti_csv_line = timestamp;
                rt3_csv_line = timestamp;

                if (aannotation != null)
                    master_csv_line += "," + current_activity;



                #endregion Setup prefix of CSV lines



                if (CSVProgress == "")
                    CSVProgress = "Synchronizing " + currentDateTime.ToLongDateString() + " " + currentDateTime.ToLongTimeString();



                if (aannotation != null)
                {

                    #region Load Activity Labels

                    if (currentUnixTime > annotatedRecord.EndUnix)
                    {
                        current_activity = "";
                        for (int j = 0; (j < annotatedRecord.Labels.Count); j++)
                        {
                            if (j == annotatedRecord.Labels.Count - 1)
                                current_activity += "";
                            else
                                current_activity += ",";
                        }
                        if (activityIndex < aannotation.Data.Count - 1)
                        {
                            activityIndex++;
                            annotatedRecord = ((AXML.AnnotatedRecord)aannotation.Data[activityIndex]);
                        }
                    }


                    if ((currentUnixTime >= annotatedRecord.StartUnix) &&
                         (currentUnixTime <= annotatedRecord.EndUnix))
                    {

                        current_activity = "";
                        for (int j = 0; (j < annotatedRecord.Labels.Count); j++)
                        {
                            if (j == annotatedRecord.Labels.Count - 1)
                                current_activity += ((AXML.Label)annotatedRecord.Labels[j]).Name;
                            else
                                current_activity += ((AXML.Label)annotatedRecord.Labels[j]).Name + ",";
                        }



                        current_activity = current_activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                        current_activity = Regex.Replace(current_activity, "[_]+", "_");
                        current_activity = Regex.Replace(current_activity, "^[_]+", "");
                        current_activity = Regex.Replace(current_activity, "[_]+$", "");
                    }


                    #endregion Load Activity Label
                }

                #region If MITes Decoder exist

                double mitesTime = 0;

                if (aMITesDecoder != null)
                {

                    #region Load MITes data if needed

                    //always have at least 5 seconds worth of data for the MITes
                    while (((unixtimestamp - currentUnixTime) <= mites_RM_DURATION) && (aMITesLoggerReader.GetSensorData(10)))
                    {
                        channel = aMITesDecoder.GetSomeMITesData()[0].channel;

                        if (channel == 0)
                        {
                            //Store raw heart rate
                            int hr = aMITesHRAnalyzer.UpdateOffline();
                            if (hr > 0)
                            {
                                rawData[channel, 0, head[channel]] = hr;

                                //Here the offset was added

                                mitesTime = unixtimestamp;
                                timeData[channel, head[channel]] = (long)mitesTime;
                                head[channel] = (head[channel] + 1) % mites_RM_SIZE;

                            }
                        }
                        else
                        {
                            x = aMITesDecoder.GetSomeMITesData()[0].x;
                            y = aMITesDecoder.GetSomeMITesData()[0].y;
                            z = aMITesDecoder.GetSomeMITesData()[0].z;

                            //Here add the offset
                            unixtimestamp = aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp;

                            rawData[channel, 0, head[channel]] = x;
                            rawData[channel, 1, head[channel]] = y;
                            rawData[channel, 2, head[channel]] = z;

                            //DateTime d1,d2;
                            //UnixTime.GetDateTime((long)unixtimestamp, out d1);
                            mitesTime = unixtimestamp;
                            //UnixTime.GetDateTime((long)mitesTime,out d2);

                            timeData[channel, head[channel]] = (long)mitesTime;
                            head[channel] = (head[channel] + 1) % mites_RM_SIZE;


                        }

                    }

                    #endregion Load MITes data if needed



                    #region Calculate Statistics

                    foreach (SXML.Sensor sensor in sannotation.Sensors)
                    {
                        channel = Convert.ToInt32(sensor.ID);



                        int headPtr = head[channel] - 1;
                        if (headPtr < 0)
                            headPtr = 39;


                        if (channel > 0)
                        {
                            double runningMeanX = 0;
                            double runningMeanY = 0;
                            double runningMeanZ = 0;
                            int numMeanPts = 0;

                            //compute running means
                            // && ((timeData[channel, headPtr] - currentUnixTime) <=MEAN_SIZE)

                            while ((timeData[channel, headPtr] > 0) && (headPtr != head[channel]) && (numMeanPts <= 39))
                            {
                                runningMeanX += rawData[channel, 0, headPtr];
                                runningMeanY += rawData[channel, 1, headPtr];
                                runningMeanZ += rawData[channel, 2, headPtr];
                                numMeanPts++;
                                headPtr--;
                                if (headPtr < 0)
                                    headPtr = 39;
                            }

                            runningMeanX = runningMeanX / numMeanPts;
                            runningMeanY = runningMeanY / numMeanPts;
                            runningMeanZ = runningMeanZ / numMeanPts;
                            RMX[channel] = runningMeanX;
                            RMY[channel] = runningMeanY;
                            RMZ[channel] = runningMeanZ;
                            RMSize[channel] = numMeanPts;

                            //RMCount[channel] = RMCount[channel] + 1;

                            headPtr = head[channel] - 1;
                            if (headPtr < 0)
                                headPtr = 39;
                            //compute values per second

                            while ((timeData[channel, headPtr] > 0) && (headPtr != head[channel]))
                            {
                                if (((timeData[channel, headPtr] - currentUnixTime) >= 0) && ((timeData[channel, headPtr] - currentUnixTime) <= 1000))
                                {

                                    //Calculate MITes Raw Values
                                    if ((channel != 0) && (channel <= sannotation.MaximumSensorID)) //if junk comes ignore it
                                    {
                                        if ((prevX[channel] > -1) && (prevY[channel] > -1) && (prevZ[channel] > -1) && (rawData[channel, 0, headPtr] > -1) && (rawData[channel, 1, headPtr] > -1) && (rawData[channel, 2, headPtr] > -1))
                                        {
                                            averageX[channel] = averageX[channel] + Math.Abs(prevX[channel] - rawData[channel, 0, headPtr]);
                                            averageRawX[channel] = averageRawX[channel] + rawData[channel, 0, headPtr];
                                            averageY[channel] = averageY[channel] + Math.Abs(prevY[channel] - rawData[channel, 1, headPtr]);
                                            averageRawY[channel] = averageRawY[channel] + rawData[channel, 1, headPtr];
                                            averageZ[channel] = averageZ[channel] + Math.Abs(prevZ[channel] - rawData[channel, 2, headPtr]);
                                            averageRawZ[channel] = averageRawZ[channel] + rawData[channel, 2, headPtr];
                                            acCounters[channel] = acCounters[channel] + 1;
                                        }

                                        prevX[channel] = rawData[channel, 0, headPtr];
                                        prevY[channel] = rawData[channel, 1, headPtr];
                                        prevZ[channel] = rawData[channel, 2, headPtr];


                                        //current data item
                                        //headPtr = head[channel];
                                        int prevHead = headPtr - 1;
                                        if (prevHead < 0)
                                            prevHead = 39;


                                        //trapezoid
                                        //double a2=rawData[channel, 0, headPtr];
                                        //double a1=rawData[channel, 0, prevHead];
                                        //a2 = a2 - runningMeanX;
                                        //a1 = a1 - runningMeanX;

                                        double t2 = timeData[channel, headPtr];
                                        double t1 = timeData[channel, prevHead];
                                        if ((t2 > 0) & (t1 > 0))
                                        {
                                            /*
                                             *                          double fa=Math.Abs((rawData[channel, 0, headPtr] - runningMeanX));
                                            double fb=Math.Abs((rawData[channel, 0, prevHead] - runningMeanX));



                                            AUC[channel, 0] = AUC[channel, 0] + (int)( ((t2 - t1) *  ((fa-fb)/ 2))*1000);
                                            fa = Math.Abs((rawData[channel, 1, headPtr] - runningMeanY));
                                            fb = Math.Abs((rawData[channel, 1, prevHead] - runningMeanY));

                                            AUC[channel, 1] = AUC[channel, 1] + (int)( ((t2 - t1) * ((fa - fb) / 2))*1000);
                                            fa = Math.Abs((rawData[channel, 2, headPtr] - runningMeanZ));
                                            fb = Math.Abs((rawData[channel, 2, prevHead] - runningMeanZ));
                                            AUC[channel, 2] = AUC[channel, 2] + (int)(((t2 - t1) * ((fa - fb) / 2))*1000);
                                             */

                                            AUC[channel, 0] = AUC[channel, 0] + (int)Math.Abs((rawData[channel, 0, headPtr] - runningMeanX));
                                            AUC[channel, 1] = AUC[channel, 1] + (int)Math.Abs((rawData[channel, 1, headPtr] - runningMeanY));
                                            AUC[channel, 2] = AUC[channel, 2] + (int)Math.Abs((rawData[channel, 2, headPtr] - runningMeanZ));
                                            VMAG[channel] = VMAG[channel] + Math.Sqrt(Math.Pow((double)(rawData[channel, 0, headPtr] - runningMeanX), 2.0) + Math.Pow((double)(rawData[channel, 1, headPtr] - runningMeanY), 2.0) + Math.Pow((double)(rawData[channel, 2, headPtr] - runningMeanZ), 2.0));
                                        }


                                    }
                                }

                                headPtr--;
                                if (headPtr < 0)
                                    headPtr = 39;
                            }
                        }

                        csv_line1 = timestamp;
                        csv_line2 = timestamp;
                        csv_line3 = timestamp;
                        csv_line4 = timestamp;
                        csv_line5 = timestamp;
                        csv_line6 = timestamp;

                        int sensor_id = Convert.ToInt32(sensor.ID);


                        if (sensor_id > 0) //No HR
                        {
                            if (acCounters[sensor_id] > 0)
                            {
                                csv_line2 += "," + acCounters[sensor_id];

                                csv_line1 += "," + ((double)(averageX[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00") + ",";
                                csv_line1 += ((double)(averageY[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00") + ",";
                                csv_line1 += ((double)(averageZ[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00");

                                csv_line3 += "," + ((int)(averageRawX[sensor_id] / acCounters[sensor_id])) + ",";
                                csv_line3 += ((int)(averageRawY[sensor_id] / acCounters[sensor_id])) + ",";
                                csv_line3 += ((int)(averageRawZ[sensor_id] / acCounters[sensor_id]));

                                csv_line4 += "," + ((double)RMX[sensor_id]).ToString("00.00") + ",";
                                csv_line4 += ((double)RMY[sensor_id]).ToString("00.00") + ",";
                                csv_line4 += ((double)RMZ[sensor_id]).ToString("00.00");

                                csv_line5 += "," + ((double)AUC[sensor_id, 0]).ToString("00.00") + ",";
                                csv_line5 += ((double)AUC[sensor_id, 1]).ToString("00.00") + ",";
                                csv_line5 += ((double)AUC[sensor_id, 2]).ToString("00.00") + ",";
                                csv_line5 += ((double)(AUC[sensor_id, 0] + AUC[sensor_id, 1] + AUC[sensor_id, 2])).ToString("00.00");

                                csv_line6 += "," + ((double)(VMAG[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00");

                                master_csv_line += "," + acCounters[sensor_id];
                                master_csv_line += "," + ((int)(averageRawX[sensor_id] / acCounters[sensor_id])) + ",";
                                master_csv_line += ((int)(averageRawY[sensor_id] / acCounters[sensor_id])) + ",";
                                master_csv_line += ((int)(averageRawZ[sensor_id] / acCounters[sensor_id]));
                                master_csv_line += "," + ((double)(averageX[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00") + ",";
                                master_csv_line += ((double)(averageY[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00") + ",";
                                master_csv_line += ((double)(averageZ[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00") + ",";

                                master_csv_line += ((double)AUC[sensor_id, 0]).ToString("00.00") + ",";
                                master_csv_line += ((double)AUC[sensor_id, 1]).ToString("00.00") + ",";
                                master_csv_line += ((double)AUC[sensor_id, 2]).ToString("00.00") + ",";
                                master_csv_line += ((double)(AUC[sensor_id, 0] + AUC[sensor_id, 1] + AUC[sensor_id, 2])).ToString("00.00") + ",";

                                master_csv_line += ((double)RMX[sensor_id]).ToString("00.00") + ",";
                                master_csv_line += ((double)RMY[sensor_id]).ToString("00.00") + ",";
                                master_csv_line += ((double)RMZ[sensor_id]).ToString("00.00") + ",";
                                master_csv_line += ((double)RMSize[sensor_id]).ToString("00.00") + ",";
                                master_csv_line += ((double)(VMAG[sensor_id] / (double)acCounters[sensor_id])).ToString("00.00");


                            }
                            else
                            {
                                csv_line1 += ",,,,";
                                csv_line3 += ",,,,";
                                csv_line2 += ",0";
                                csv_line4 += ",,,,";
                                csv_line5 += ",,,,,";
                                csv_line6 += ",";
                                master_csv_line += ",0,,,,,,,,,,,,,,,";
                            }

                            //Store data in CSV files
                            activityCountCSVs[sensor_id].WriteLine(csv_line1);
                            samplingCSVs[sensor_id].WriteLine(csv_line2);
                            averagedRaw[sensor_id].WriteLine(csv_line3);
                            rmCSVs[sensor_id].WriteLine(csv_line4);
                            aucCSVs[sensor_id].WriteLine(csv_line5);
                            vmagCSVs[sensor_id].WriteLine(csv_line6);

                        }
                        else
                        {

                            hrCount = 0;
                            sumHR = 0;
                            while ((timeData[0, headPtr] > 0) && (headPtr != head[0]))
                            {
                                if (((timeData[0, headPtr] - currentUnixTime) >= 0) && ((timeData[0, headPtr] - currentUnixTime) <= 1000))
                                {

                                    sumHR += rawData[0, 0, headPtr];
                                    hrCount++;
                                }
                                headPtr--;
                                if (headPtr < 0)
                                    headPtr = mites_RM_SIZE - 1;
                            }
                            if (hrCount > 0)
                            {
                                hrCSV.WriteLine(hr_csv_line + "," + (int)(sumHR / hrCount));
                                master_csv_line = master_csv_line + "," + (int)(sumHR / hrCount);
                            }
                            else
                            {
                                hrCSV.WriteLine(hr_csv_line + ",");
                                master_csv_line = master_csv_line + ",";
                            }
                        }

                        averageX[sensor_id] = 0;
                        averageY[sensor_id] = 0;
                        averageZ[sensor_id] = 0;
                        averageRawX[sensor_id] = 0;
                        averageRawY[sensor_id] = 0;
                        averageRawZ[sensor_id] = 0;
                        //prevX[sensor_id] = 0;
                        //prevY[sensor_id] = 0;
                        //prevY[sensor_id] = 0;
                        acCounters[sensor_id] = 0;
                        RMX[sensor_id] = 0;
                        RMY[sensor_id] = 0;
                        RMZ[sensor_id] = 0;
                        RMSize[sensor_id] = 0;
                        VMAG[sensor_id] = 0;
                        for (int j = 0; (j < 3); j++)
                            AUC[sensor_id, j] = 0;
                    }

                    #endregion Calculate Statistics


                    #region Append MITes Statistics (Deleted)

                    #region Write CSV line for MITes HR

                    #endregion Write CSV line for MITes HR


                    #endregion Append MITes Statistics

                }

                #endregion if there is MITes data

                #region If Wockets Decoder exist

                if (wcontroller != null)
                {

                    #region Load Wockets data if needed
                    for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                    {

                        string s = "";
                        while (((wunixtimestamp[i] - currentUnixTime) <= RM_DURATION) && ((s = wocketsTR1[i].ReadLine()) != null))
                        {
                            string[] wocketsTokens = s.Split(',');
                            wrawData[wcontroller._Sensors[i]._ID, 0, whead[wcontroller._Sensors[i]._ID]] = Convert.ToInt32(wocketsTokens[1]);
                            wrawData[wcontroller._Sensors[i]._ID, 1, whead[wcontroller._Sensors[i]._ID]] = Convert.ToInt32(wocketsTokens[2]);
                            wrawData[wcontroller._Sensors[i]._ID, 2, whead[wcontroller._Sensors[i]._ID]] = Convert.ToInt32(wocketsTokens[3]);
                            wtimeData[wcontroller._Sensors[i]._ID, whead[wcontroller._Sensors[i]._ID]] = (long)Convert.ToDouble(wocketsTokens[0]);
                            wunixtimestamp[i] = Convert.ToDouble(wocketsTokens[0]);
                            whead[wcontroller._Sensors[i]._ID] = (whead[wcontroller._Sensors[i]._ID] + 1) % RM_SIZE;
                        }
                    }

                    #endregion Load Wockets data if needed

                    #region Calculate Statistics

                    for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                    {
                        double wrunningMeanX = 0;
                        double wrunningMeanY = 0;
                        double wrunningMeanZ = 0;
                        int wnumMeanPts = 0;

                        int wheadPtr = whead[wcontroller._Sensors[i]._ID] - 1;
                        if (wheadPtr < 0)
                            wheadPtr = RM_SIZE - 1;


                        #region compute running means

                        while ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] > 0) && (wheadPtr != whead[wcontroller._Sensors[i]._ID]) && (wnumMeanPts <= (RM_SIZE - 1)))
                        {
                            wrunningMeanX += wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr];
                            wrunningMeanY += wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr];
                            wrunningMeanZ += wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr];
                            wnumMeanPts++;
                            wheadPtr--;

                            if (wheadPtr < 0)
                                wheadPtr = (RM_SIZE - 1);
                        }

                        wrunningMeanX = wrunningMeanX / wnumMeanPts;
                        wrunningMeanY = wrunningMeanY / wnumMeanPts;
                        wrunningMeanZ = wrunningMeanZ / wnumMeanPts;
                        wRMX[wcontroller._Sensors[i]._ID] = wrunningMeanX;
                        wRMY[wcontroller._Sensors[i]._ID] = wrunningMeanY;
                        wRMZ[wcontroller._Sensors[i]._ID] = wrunningMeanZ;
                        wRMSize[wcontroller._Sensors[i]._ID] = wnumMeanPts;
                        //RMCount[wcontroller._Sensors[i]._ID] = RMCount[wcontroller._Sensors[i]._ID] + 1;

                        wheadPtr = whead[wcontroller._Sensors[i]._ID] - 1;
                        if (wheadPtr < 0)
                            wheadPtr = (RM_SIZE - 1);


                        #endregion compute running means





                        //compute values per second
                        while ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] > 0) && (wheadPtr != whead[wcontroller._Sensors[i]._ID]))
                        {
                            double ttt = wtimeData[wcontroller._Sensors[i]._ID, wheadPtr];

                            if (((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] - currentUnixTime) >= 0) && ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] - currentUnixTime) <= 1000))
                            {

                                if ((wprevX[wcontroller._Sensors[i]._ID] > -1) && (wprevY[wcontroller._Sensors[i]._ID] > -1) && (wprevZ[wcontroller._Sensors[i]._ID] > -1) && (wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] > -1) && (wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] > -1) && (wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] > -1))
                                {
                                    waverageX[wcontroller._Sensors[i]._ID] = waverageX[wcontroller._Sensors[i]._ID] + Math.Abs(wprevX[wcontroller._Sensors[i]._ID] - wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr]);
                                    waverageRawX[wcontroller._Sensors[i]._ID] = waverageRawX[wcontroller._Sensors[i]._ID] + wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr];
                                    waverageY[wcontroller._Sensors[i]._ID] = waverageY[wcontroller._Sensors[i]._ID] + Math.Abs(wprevY[wcontroller._Sensors[i]._ID] - wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr]);
                                    waverageRawY[wcontroller._Sensors[i]._ID] = waverageRawY[wcontroller._Sensors[i]._ID] + wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr];
                                    waverageZ[wcontroller._Sensors[i]._ID] = waverageZ[wcontroller._Sensors[i]._ID] + Math.Abs(wprevZ[wcontroller._Sensors[i]._ID] - wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr]);
                                    waverageRawZ[wcontroller._Sensors[i]._ID] = waverageRawZ[wcontroller._Sensors[i]._ID] + wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr];
                                    wacCounters[wcontroller._Sensors[i]._ID] = wacCounters[wcontroller._Sensors[i]._ID] + 1;

                                    //JPN: Increment counter used to determine samples per minute for WRAC calculations
                                    wWRACCounterMinute[wcontroller._Sensors[i]._ID]++;
                                }

                                wprevX[wcontroller._Sensors[i]._ID] = wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr];
                                wprevY[wcontroller._Sensors[i]._ID] = wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr];
                                wprevZ[wcontroller._Sensors[i]._ID] = wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr];


                                int wprevHead = wheadPtr - 1;
                                if (wprevHead < 0)
                                    wprevHead = (RM_SIZE - 1);


                                double wt2 = wtimeData[wcontroller._Sensors[i]._ID, wheadPtr];
                                double wt1 = wtimeData[wcontroller._Sensors[i]._ID, wprevHead];
                                if ((wt2 > 0) & (wt1 > 0))
                                {

                                    wAUC[wcontroller._Sensors[i]._ID, 0] = wAUC[wcontroller._Sensors[i]._ID, 0] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] - wrunningMeanX));
                                    wAUC[wcontroller._Sensors[i]._ID, 1] = wAUC[wcontroller._Sensors[i]._ID, 1] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] - wrunningMeanY));
                                    wAUC[wcontroller._Sensors[i]._ID, 2] = wAUC[wcontroller._Sensors[i]._ID, 2] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] - wrunningMeanZ));

                                    wVMAG[wcontroller._Sensors[i]._ID] = wVMAG[wcontroller._Sensors[i]._ID] + Math.Sqrt(Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] - wrunningMeanX), 2.0) + Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] - wrunningMeanY), 2.0) + Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] - wrunningMeanZ), 2.0));
                                }
                            }

                            wheadPtr--;
                            if (wheadPtr < 0)
                                wheadPtr = (RM_SIZE - 1);
                        }

                        wrunningMeanX = 0;
                        wrunningMeanY = 0;
                        wrunningMeanZ = 0;

                        for (int k = 0; (k < RM_SIZE); k++)
                        {
                            wrunningMeanX += wrawData[wcontroller._Sensors[i]._ID, 0, k];
                            wrunningMeanY += wrawData[wcontroller._Sensors[i]._ID, 1, k];
                            wrunningMeanZ += wrawData[wcontroller._Sensors[i]._ID, 2, k];
                        }
                        
                        wrunningMeanX = wrunningMeanX / RM_SIZE;
                        wrunningMeanY = wrunningMeanY / RM_SIZE;
                        wrunningMeanZ = wrunningMeanZ / RM_SIZE;

                        wAUC[wcontroller._Sensors[i]._ID, 0] = 0;
                        wAUC[wcontroller._Sensors[i]._ID, 1] = 0;
                        wAUC[wcontroller._Sensors[i]._ID, 2] = 0;

                        //JPN: Reset combined AUC array for next second
                        wAUCXYZ[wcontroller._Sensors[i]._ID] = 0;

                        wVMAG[wcontroller._Sensors[i]._ID] = 0;



                        for (int k = 0; k < RM_SIZE; k++)
                        {
                            wAUC[wcontroller._Sensors[i]._ID, 0] = wAUC[wcontroller._Sensors[i]._ID, 0] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 0, k] - wrunningMeanX));
                            wAUC[wcontroller._Sensors[i]._ID, 1] = wAUC[wcontroller._Sensors[i]._ID, 1] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 1, k] - wrunningMeanY));
                            wAUC[wcontroller._Sensors[i]._ID, 2] = wAUC[wcontroller._Sensors[i]._ID, 2] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 2, k] - wrunningMeanZ));

                            //JPN!!!!!
                            //wAUC[wcontroller._Sensors[i]._ID, 0] = Filter(wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr], 0);
                            //wAUC[wcontroller._Sensors[i]._ID, 1] = Filter(wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr], 1);
                            //wAUC[wcontroller._Sensors[i]._ID, 2] = Filter(wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr], 2);

                            //JPN: Sum AUC values for each axis for the current sample and add to a running total for the current second
                            double myRawAC = wAUCXYZ[wcontroller._Sensors[i]._ID] + wAUC[wcontroller._Sensors[i]._ID, 0] + wAUC[wcontroller._Sensors[i]._ID, 1] + wAUC[wcontroller._Sensors[i]._ID, 2];
                            //JPN: Divide running total by the scaling factor used in Wockets Firmware Activity Counts (WFAC)
                            myRawAC /= 24;
                            //JPN: Trim oversized values to match integer size of WFAC calculations and add to combined AUC array for WRAC
                            wAUCXYZ[wcontroller._Sensors[i]._ID] = (myRawAC > 65535 ? 65535 : (int)myRawAC);

                            wVMAG[wcontroller._Sensors[i]._ID] = wVMAG[wcontroller._Sensors[i]._ID] + Math.Sqrt(Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] - wrunningMeanX), 2.0) + Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] - wrunningMeanY), 2.0) + Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] - wrunningMeanZ), 2.0));
                        }

                        //Inititalize lines to be written to cvs files
                        int sensor_id = wcontroller._Sensors[i]._ID;
                        csv_line1 = timestamp;
                        csv_line2 = timestamp;
                        csv_line3 = timestamp;
                        csv_line4 = timestamp;
                        csv_line5 = timestamp;
                        csv_line6 = timestamp;

                        if (wacCounters[sensor_id] > 0)
                        {

                            #region Append Wockets Statistics


                            csv_line2 += "," + wacCounters[sensor_id];

                            csv_line1 += "," + ((double)(waverageX[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00") + ",";
                            csv_line1 += ((double)(waverageY[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00") + ",";
                            csv_line1 += ((double)(waverageZ[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00");

                            csv_line3 += "," + ((int)(waverageRawX[sensor_id] / wacCounters[sensor_id])) + ",";
                            csv_line3 += ((int)(waverageRawY[sensor_id] / wacCounters[sensor_id])) + ",";
                            csv_line3 += ((int)(waverageRawZ[sensor_id] / wacCounters[sensor_id]));

                            csv_line4 += "," + ((double)wRMX[sensor_id]).ToString("00.00") + ",";
                            csv_line4 += ((double)wRMY[sensor_id]).ToString("00.00") + ",";
                            csv_line4 += ((double)wRMZ[sensor_id]).ToString("00.00");

                            csv_line5 += "," + ((double)wAUC[sensor_id, 0]).ToString("00.00") + ",";
                            csv_line5 += ((double)wAUC[sensor_id, 1]).ToString("00.00") + ",";
                            csv_line5 += ((double)wAUC[sensor_id, 2]).ToString("00.00") + ",";
                            csv_line5 += ((double)(wAUC[sensor_id, 0] + wAUC[sensor_id, 1] + wAUC[sensor_id, 2])).ToString("00.00");

                            csv_line6 += "," + ((double)(wVMAG[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00");

                            master_csv_line += "," + wacCounters[sensor_id];
                            master_csv_line += "," + ((int)(waverageRawX[sensor_id] / wacCounters[sensor_id])) + ",";
                            master_csv_line += ((int)(waverageRawY[sensor_id] / wacCounters[sensor_id])) + ",";
                            master_csv_line += ((int)(waverageRawZ[sensor_id] / wacCounters[sensor_id]));
                            master_csv_line += "," + ((double)(waverageX[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00") + ",";
                            master_csv_line += ((double)(waverageY[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00") + ",";
                            master_csv_line += ((double)(waverageZ[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00") + ",";

                            master_csv_line += ((double)wAUC[sensor_id, 0]).ToString("00.00") + ",";
                            master_csv_line += ((double)wAUC[sensor_id, 1]).ToString("00.00") + ",";
                            master_csv_line += ((double)wAUC[sensor_id, 2]).ToString("00.00") + ",";
                            master_csv_line += ((double)(wAUC[sensor_id, 0] + wAUC[sensor_id, 1] + wAUC[sensor_id, 2])).ToString("00.00") + ",";

                            master_csv_line += ((double)wRMX[sensor_id]).ToString("00.00") + ",";
                            master_csv_line += ((double)wRMY[sensor_id]).ToString("00.00") + ",";
                            master_csv_line += ((double)wRMZ[sensor_id]).ToString("00.00") + ",";

                            master_csv_line += ((double)wRMSize[sensor_id]).ToString("00.00") + ",";
                            master_csv_line += ((double)(wVMAG[sensor_id] / (double)wacCounters[sensor_id])).ToString("00.00");

                            #endregion Append Wockets Statistics

                            //JPN: If WRAC sums are available
                            if (wWRACSummation != null)
                            {
                                //JPN: Sum the raw ACs for each accelerometer axis (X,Y,Z) per second for each sensor
                                wWRACSummation[wcontroller._Sensors[i]._ID] += wAUCXYZ[wcontroller._Sensors[i]._ID];

                                //JPN: Update the unix counter for the AC per minute calculation 
                                if (prevUnixTime[wcontroller._Sensors[i]._ID] == -1)
                                    prevUnixTime[wcontroller._Sensors[i]._ID] = currentUnixTime;

                                //JPN: If one minute has elapsed, computer WRAC for this sensor
                                if ((currentUnixTime - prevUnixTime[wcontroller._Sensors[i]._ID]) >= 60000)
                                {
                                    //JPN: Add the last minute's worth of WRAC data to the final array
                                    wWRACData[wcontroller._Sensors[i]._ID][key] = Convert.ToInt32(wWRACData[wcontroller._Sensors[i]._ID][key]) + wWRACSummation[wcontroller._Sensors[i]._ID];

                                    //JPN: Compute sampling rate for this WRAC by dividing number of samples by 60 seconds
                                    wWRACSamplingRate[wcontroller._Sensors[i]._ID][key] = (double)wWRACCounterMinute[wcontroller._Sensors[i]._ID] / 60;

                                    //JPN: Reset arrays used to compute WRAC
                                    wWRACSummation[wcontroller._Sensors[i]._ID] = 0;
                                    wWRACCounterMinute[wcontroller._Sensors[i]._ID] = 0;

                                    //JPN: Mark the start of the next epoch for WRAC calcluation
                                    prevUnixTime[wcontroller._Sensors[i]._ID] = currentUnixTime;
                                }
                            }
                        }
                        else
                        {
                            csv_line1 += ",,,,";
                            csv_line3 += ",,,,";
                            csv_line2 += ",0";
                            csv_line4 += ",,,,";
                            csv_line5 += ",,,,,";
                            csv_line6 += ",";
                            master_csv_line += ",0,,,,,,,,,,,,,,,";
                        }

                        //Store data in CSV files
                        wactivityCountCSVs[sensor_id].WriteLine(csv_line1);
                        wsamplingCSVs[sensor_id].WriteLine(csv_line2);
                        waveragedRaw[sensor_id].WriteLine(csv_line3);
                        wrmCSVs[sensor_id].WriteLine(csv_line4);
                        waucCSVs[sensor_id].WriteLine(csv_line5);
                        wvmagCSVs[sensor_id].WriteLine(csv_line6);


                        //Reset Variables
                        waverageX[sensor_id] = 0;
                        waverageY[sensor_id] = 0;
                        waverageZ[sensor_id] = 0;
                        waverageRawX[sensor_id] = 0;
                        waverageRawY[sensor_id] = 0;
                        waverageRawZ[sensor_id] = 0;
                        //prevX[sensor_id] = 0;
                        //prevY[sensor_id] = 0;
                        //prevY[sensor_id] = 0;
                        wacCounters[sensor_id] = 0;
                        wRMX[sensor_id] = 0;
                        wRMY[sensor_id] = 0;
                        wRMZ[sensor_id] = 0;
                        wRMSize[sensor_id] = 0;
                        wVMAG[sensor_id] = 0;
                        for (int j = 0; (j < 3); j++)
                            wAUC[sensor_id, j] = 0;

                        //JPN: reset AUC summation for next second's WRAC calculation
                        wAUCXYZ[sensor_id] = 0;

                    }

                    #endregion Calculate Statistics

                }

                #endregion If Wockets Decoder Exist

                #region Write the CSV lines for each sensor

                #region Write CSV lines for Actigraphs

                for (int i = 0; (i < actigraphData.Length); i++)
                {
                    if (actigraphData[i].ContainsKey(key) == false)
                    {
                        if (actigraphType[i] == "GT3X" || actigraphType[i] == "GT3X+")
                        {
                            actigraphCSV[i].WriteLine(actigraph_csv_line[i] + ",,,");
                            master_csv_line = master_csv_line + ",,,";
                            master_csv_line = master_csv_line + "," + prevActLine[i] + "," + prevActAC_XYZ;
                        }
                        else if (actigraphType[i] == "GT1M")
                        {
                            actigraphCSV[i].WriteLine(actigraph_csv_line[i] + ",,");
                            master_csv_line = master_csv_line + ",,";
                        }
                        else
                        {
                            actigraphCSV[i].WriteLine(actigraph_csv_line[i] + ",");
                            master_csv_line = master_csv_line + ",";
                        }

                    }
                    else
                    {

                        actigraphCSV[i].WriteLine(actigraph_csv_line[i] + "," + actigraphData[i][key]);
                        master_csv_line = master_csv_line + "," + actigraphData[i][key];
                        //PLOT value                        
                        prevActLine[i] = actigraphData[i][key].ToString();
                        try
                        {
                            prevActXYZ = prevActLine[i].Split(',');
                            prevActAC_XYZ = Convert.ToInt32(prevActXYZ[0]) + Convert.ToInt32(prevActXYZ[1]) + Convert.ToInt32(prevActXYZ[2]);
                        }
                        catch (Exception ex)
                        {
                        }
                        master_csv_line = master_csv_line + "," + actigraphData[i][key] + "," + prevActAC_XYZ;

                    }
                }

                #endregion Write CSV lines for Actigraphs

                #region Write CSV lines for Wockets Firmware Activity Counts (WFAC)

                if (wWFACData != null)
                {
                    for (int i = 0; (i < wWFACData.Length); i++)
                    {
                        if (wWFACData[i].ContainsKey(key) == false)
                        {
                            wWFACSummaryCSV[i].WriteLine(summary_csv_line[i] + ",");
                            master_csv_line = master_csv_line + ",";
                        }
                        else
                        {
                            wWFACSummaryCSV[i].WriteLine(summary_csv_line[i] + "," + wWFACData[i][key]);
                            master_csv_line = master_csv_line + "," + wWFACData[i][key];
                        }
                    }
                }

                #endregion Write CSV lines for Wockets Firmware Activity Counts (WFAC)

                #region Write CSV lines for Wockets Raw Activity Counts (WRAC)

                //JPN: If WRAC data is available, add that to the summary spreadsheets
                if (wWRACData != null)
                {
                    //JPN: Iterate through each sensor
                    for (int i = 0; (i < wWRACData.Length); i++)
                    {
                        //JPN: Write blank data column if the current sample is not the start of a new WRAC minute epoch
                        if (wWRACData[i].ContainsKey(key) == false)
                        {
                            wWRACSummaryCSV[i].WriteLine(summary_csv_line[i] + ",");
                            master_csv_line = master_csv_line + ",";
                        }
                        else
                        {
                            //JPN: Retrieve WRAC data point and divide by computed sampling rate for the minute observed
                            //int value = Convert.ToInt32(Convert.ToDouble(wWRACData[i][key]) * Convert.ToDouble(wWRACSamplingRate[i][key]));
                            //JPN!!!!
                            int value = Convert.ToInt32(Convert.ToDouble(wWRACData[i][key]));
                            //JPN: Add scaled WRAC data to the WRAC text stream
                            wWRACSummaryCSV[i].WriteLine(summary_csv_line[i] + "," + value);
                            //JPN: Add scaled WRAC data to the master summary CSV file
                            master_csv_line = master_csv_line + "," + value;
                        }
                    }
                }

                #endregion Write CSV lines for Wockets Raw Activity Counts (WRAC)

                #region Write CSV lines for PLOT Wockets Firmware Activity Counts (WFAC)
                if (wWFACData != null)
                {
                    for (int i = 0; (i < wWFACData.Length); i++)
                    {
                        if (wWFACData[i].ContainsKey(key) == false)
                        {
                            master_csv_line = master_csv_line + "," + prevWFACPlotDataLine[i];
                        }
                        else
                        {
                            master_csv_line = master_csv_line + "," + wWFACData[i][key];
                            prevWFACPlotDataLine[i] = wWFACData[i][key].ToString();
                        }
                    }
                }
                #endregion Write CSV lines for PLOT Wockets Firmware Activity Counts (WFAC)

                #region Write CSV lines for PLOT Wockets Raw Activity Counts (WRAC)

                //JPN: If WRAC data is available, add that to the summary spreadsheets
                if (wWRACData != null)
                {
                    //JPN: Iterate through each sensor
                    for (int i = 0; (i < wWRACData.Length); i++)
                    {
                        //JPN: Carry over previous WRAC value if the current sample is not the start of a new WRAC minute epoch
                        if (wWRACData[i].ContainsKey(key) == false)
                        {
                            master_csv_line = master_csv_line + "," + prevWRACPlotDataLine[i];
                        }
                        //JPN: Log new WRAC value when the next minute epoch starts
                        else
                        {
                            //JPN: Retrieve WRAC data point and divide by computed sampling rate for the minute observed
                            //JPN!!!
                            //int value = Convert.ToInt32(Convert.ToDouble(wWRACData[i][key]) / Convert.ToDouble(wWRACSamplingRate[i][key]));
                            int value = Convert.ToInt32(Convert.ToDouble(wWRACData[i][key]));
                            //JPN: Add scaled WRAC data to the text stream
                            master_csv_line = master_csv_line + "," + value;
                            //JPN: Store this line so it can be repeated in the summary CSV until the WRAC value changes
                            prevWRACPlotDataLine[i] = value.ToString();
                        }
                    }

                    //JPN: TEMP: Output computed sampling rate with values...
                    for (int i = 0; (i < wWRACData.Length); i++)
                    {
                        //JPN: Carry over previous WRAC Sample Count the current sample is not the start of a new WRAC minute epoch
                        if (wWRACData[i].ContainsKey(key) == false)
                        {
                            master_csv_line = master_csv_line + "," + prevWRACPlotSampleCount[i];
                        }
                        //JPN: Log new WRAC value when the next minute epoch starts
                        else
                        {
                            //JPN: Retrieve WRAC sampling rate and multiply by 60 to represent numbers of samples in the minute
                            int value = Convert.ToInt32(wWRACSamplingRate[i][key]) * 60;
                            //JPN: Add WRAC Sample Rate to the text stream
                            master_csv_line = master_csv_line + "," + value;
                            //JPN: Store this line so it can be repeated in the summary CSV until the WRAC value changes
                            prevWRACPlotSampleCount[i] = value.ToString();
                        }
                    }
                }

                #endregion Write CSV lines for PLOT Wockets Raw Activity Counts (WRAC)

                #region Write CSV line for Sensewear

                if ((sensewearFound) && (sensewearCSV != null))
                {
                    if (SSR.ContainsKey(key))
                    {
                        sensewearCSV.WriteLine(sensewear_csv_line + "," + (int)SSR[key] + "," + (double)STrans[key] +
                            "," + (double)SLong[key] + "," + (double)SAcc[key]);
                        master_csv_line = master_csv_line + "," + (int)SSR[key] + "," + (double)STrans[key] +
                            "," + (double)SLong[key] + "," + (double)SAcc[key];
                    }
                    else
                    {
                        sensewearCSV.WriteLine(sensewear_csv_line + ",,,,");
                        master_csv_line = master_csv_line + ",,,,";
                    }
                }

                #endregion Write CSV line for Sensewear

                #region Write CSV line for Sensewear Vanderbilt

                if ((sensewearVanderbiltFound) && (sensewearCSV != null))
                {
                    if (sensewearData.ContainsKey(key))
                    {
                        sensewearCSV.WriteLine(sensewear_csv_line + "," + ((string)sensewearData[key]));
                        master_csv_line = master_csv_line + "," + ((string)sensewearData[key]);
                    }
                    else
                    {
                        sensewearCSV.WriteLine(sensewear_csv_line + ",,,,,,,,,,,,,");
                        master_csv_line = master_csv_line + ",,,,,,,,,,,,,";
                    }
                }

                #endregion Write CSV line for Sensewear Vanderbilt

                #region Write CSV line for Zephyr

                if ((zephyrFound) && (zephyrCSV != null))
                {
                    if (zephyrData.ContainsKey(key))
                    {
                        zephyrCSV.WriteLine(zephyr_csv_line + "," + ((string)zephyrData[key]));
                        master_csv_line = master_csv_line + "," + ((string)zephyrData[key]);
                    }
                    else
                    {
                        zephyrCSV.WriteLine(zephyr_csv_line + ",,,,,,,,,,,,,,,,");
                        master_csv_line = master_csv_line + ",,,,,,,,,,,,,,,,";
                    }
                }

                #endregion Write CSV line for Zephyr

                #region Write CSV line for Oxycon

                if ((oxyconFound) && (oxyconCSV != null))
                {
                    if (oxyconData.ContainsKey(key))
                    {
                        oxyconCSV.WriteLine(oxycon_csv_line + "," + ((string)oxyconData[key]));
                        master_csv_line = master_csv_line + "," + ((string)oxyconData[key]);
                    }
                    else
                    {
                        oxyconCSV.WriteLine(zephyr_csv_line + ",,,,,,,,");
                        master_csv_line = master_csv_line + ",,,,,,,,";
                    }
                }

                #endregion Write CSV line for Oxycon

                #region Write CSV line for Omron

                if ((omronFound) && (omronCSV != null))
                {
                    if (omronData.Contains(key))
                    {
                        omronCSV.WriteLine(omron_csv_line + "," + ((int)omronData[key]));
                        master_csv_line = master_csv_line + "," + ((int)omronData[key]);
                    }
                    else
                    {
                        omronCSV.WriteLine(omron_csv_line + ",");
                        master_csv_line = master_csv_line + ",";
                    }
                }

                #endregion Write CSV line for Omron

                #region Write CSV line for Columbia

                if ((columbiaFound) && (columbiaCSV != null))
                {
                    if (columbiaData.ContainsKey(key))
                    {
                        columbiaCSV.WriteLine(columbia_csv_line + "," + ((string)columbiaData[key]));
                        master_csv_line = master_csv_line + "," + ((string)columbiaData[key]);
                    }
                    else
                    {
                        columbiaCSV.WriteLine(columbia_csv_line + ",,,,,");
                        master_csv_line = master_csv_line + ",,,,,";
                    }
                }

                #endregion Write CSV line for Columbia

                #region Write CSV line for GPS

                if ((gpsFound) && (gpsCSV != null))
                {
                    if (gpsData.ContainsKey(key))
                    {
                        gpsCSV.WriteLine(gps_csv_line + "," + ((string)gpsData[key]));
                        master_csv_line = master_csv_line + "," + ((string)gpsData[key]);
                    }
                    else
                    {
                        gpsCSV.WriteLine(gps_csv_line + ",,,,");
                        master_csv_line = master_csv_line + ",,,,";
                    }
                }

                #endregion Write CSV line for GPS

                #region Write CSV line for RTI

                if ((rtiFound) && (rtiCSV != null))
                {
                    if (rtiData.ContainsKey(key))
                    {
                        rtiCSV.WriteLine(rti_csv_line + "," + ((string)rtiData[key]));
                        master_csv_line = master_csv_line + "," + ((string)rtiData[key]);
                    }
                    else
                    {
                        rtiCSV.WriteLine(rti_csv_line + ",,,,");
                        master_csv_line = master_csv_line + ",,,,";
                    }
                }

                #endregion Write CSV line for RTI

                #region Write CSV line for RT3

                if ((rt3Found) && (rt3CSV != null))
                {
                    if (rt3Data.ContainsKey(key))
                    {
                        rt3CSV.WriteLine(rt3_csv_line + "," + ((string)rt3Data[key]));
                        master_csv_line = master_csv_line + "," + ((string)rt3Data[key]);
                    }
                    else
                    {
                        rt3CSV.WriteLine(rt3_csv_line + ",,,,");
                        master_csv_line = master_csv_line + ",,,,";
                    }
                }

                #endregion Write CSV line for RT3

                masterCSV.WriteLine(master_csv_line);


                #endregion Write the CSV lines for each sensor

                //reinitialize variables
                hrCount = 0;
                sumHR = 0;

                currentDateTime = currentDateTime.AddSeconds(1.0);

            }

            #region Convert Actigraph Raw Data to Wockets Raw Format and CSV

            CSVProgress = "Converting Actigraph Raw Data to Wockets Raw Format and csv";
            string actRawDirectory = aDataDirectory + "\\othersensors";
            //file = Directory.GetFileSystemEntries(actRawDirectory, "*ActRawCSV*.csv");
            file = Directory.GetFileSystemEntries(actRawDirectory, "*RAW*.csv");
            if (file.Length > 0)
            {
                string line;
                string[] row = { "" };
                string startDate = "";
                string startTime = "";
                string startDT = "";
                string endDate = "";
                string endDT = "";
                string endTime = "";

                DateTime start = DateTime.MinValue;
                DateTime end = DateTime.MinValue;

                double totalActSeconds = 1;
                double totalActSamples;
                double actSR;
                double nextActTime = 25;

                int headcount = 0;
                DateTime dateTime = DateTime.MinValue;
                for (int i = 0; i < file.Length; i++)
                {
                    string pth = Path.Combine(actRawDirectory, file[i]);
                    StreamReader sr = new StreamReader(pth);
                    headcount = 0;

                    int len = File.ReadAllLines(pth).Length;
                    len = len - 10;
                    //TextWriter tw = new StreamWriter(actRawDirectory + "/ActRawData" + (i+1) + ".csv");   
                    TextWriter tw = new StreamWriter(aDataDirectory + "\\merged" + "\\Actigraph_Raw_Data" + (i + 1) + ".csv");
                    while ((line = sr.ReadLine()) != null)
                    {
                        headcount++;
                        if (headcount == 3)
                        {
                            row = line.Split(',');
                            startTime = row[0];
                            startTime = startTime.Substring(10);
                        }
                        if (headcount == 4)
                        {
                            row = line.Split(',');
                            startDate = row[0];
                            startDate = startDate.Substring(10);
                            startDT = startDate + startTime;
                            dateTime = DateTime.Parse(startDT);
                            start = DateTime.Parse(startDT);
                            dateTime = dateTime.AddSeconds(actigraphOffset[i]);

                            TimeSpan t = (dateTime - new DateTime(1970, 1, 1, 0, 0, 0, 0).ToLocalTime());
                            TimeSpan uts = dateTime.Subtract(new DateTime(1970, 1, 1, 0, 0, 0, 0));
                            double unixts = uts.TotalMilliseconds;
                            double ts = t.TotalMilliseconds;
                        }
                        if (headcount == 6)
                        {
                            row = line.Split(',');
                            endTime = row[0];
                            endTime = endTime.Substring(13);
                        }
                        if (headcount == 7)
                        {
                            row = line.Split(',');
                            endDate = row[0];
                            endDate = endDate.Substring(13);
                            endDT = endDate + endTime;
                            end = DateTime.Parse(endDT);
                            TimeSpan tsAct = end - start;
                            totalActSeconds = tsAct.TotalSeconds;
                            totalActSamples = len;
                            actSR = totalActSamples / totalActSeconds;
                            nextActTime = (1000 / actSR);
                        }

                        if (headcount > 10)
                        {
                            if (line.Contains("\""))
                            {
                                line = line.Replace("\"", "");
                            }

                            row = line.Split(',');
                            double xval, yval, zval;
                            diff = dateTime.Subtract(new DateTime(1970, 1, 1, 0, 0, 0, 0));
                            tw.Write(diff.TotalMilliseconds + ",");
                            dateTime = dateTime.AddMilliseconds(nextActTime);
                            //xval = Math.Round((Convert.ToDouble(row[1]) + 6) / 0.01171875);
                            // Wocket +X -> Actigraph +Axis 2
                            xval = Math.Round(((ACTRANGE / 2) - Convert.ToDouble(row[1])) / ACTWKTNORM);
                            xval = Math.Round(((ACTRANGE / 2) + Convert.ToDouble(row[1])) / ACTWKTNORM);
                            // Wocket +Y -> Actigraph +Axis 1
                            //yval = Math.Round(((ACTRANGE / 2) - (Convert.ToDouble(row[0]))) / ACTWKTNORM);
                            yval = Math.Round(((ACTRANGE / 2) + (Convert.ToDouble(row[0]))) / ACTWKTNORM);
                            //Wocket +Z -> Actigraph -Axis3
                            //zval = Math.Round((6 - (Convert.ToDouble(row[2]))) / 0.0171875);
                            zval = Math.Round((Convert.ToDouble(row[2]) + (ACTRANGE / 2)) / ACTWKTNORM);
                            //zval = Math.Round(((ACTRANGE / 2) - Convert.ToDouble(row[2])) / ACTWKTNORM);
                            tw.Write(xval + "," + yval + "," + zval + ",");
                            tw.WriteLine();

                        }
                    }
                    //totalActSamples = headcount - 10;
                    //actSR = totalActSamples / totalActSeconds;
                    tw.Close();
                    sr.Close();
                    //sr = new StreamReader(actRawDirectory + "\\actRawData" + (i+1) + ".csv");
                    sr = new StreamReader(aDataDirectory + "\\merged" + "\\Actigraph_Raw_Data" + (i + 1) + ".csv");
                    //i + 1
                    DateTime dt = DateTime.Parse(startDate + " " + startTime);
                    string date = dt.Year.ToString() + "-" + dt.Month.ToString() + "-" + dt.Day.ToString();
                    string dir = actRawDirectory + "\\Actigraph\\data\\raw\\PLFormat";
                    int hr = dt.Hour;
                    string dir1 = dir + "\\" + date + "\\" + dt.Hour.ToString();
                    Directory.CreateDirectory(dir1);
                    FileStream fs = new FileStream(dir1 + "\\Actigraph" + (i + 1) + ".PLFormat", FileMode.Create);
                    BinaryWriter bw = new BinaryWriter(fs);
                    DateTime currentDate = DateTime.MinValue;
                    int count = 0;
                    int currentDay;
                    int currentMonth;
                    int currentYear;
                    int currentHour;
                    int startDay = DateTime.Parse(startDT).Day;
                    int startMonth = DateTime.Parse(startDT).Month;
                    int startYear = DateTime.Parse(startDT).Year;
                    int startHour = DateTime.Parse(startDT).Hour;
                    while ((line = sr.ReadLine()) != null)
                    {
                        count++;
                        row = line.Split(',');

                        if (count == 1)
                        {
                            DateTime startDt;
                            UnixTime.GetDateTime(Convert.ToInt64(row[0]), out startDt);
                            startDay = startDt.Day;
                            startMonth = startDt.Month;
                            startYear = startDt.Year;
                            startHour = startDt.Hour;
                        }

                        UnixTime.GetDateTime(Convert.ToInt64(row[0]), out currentDate);
                        currentDay = currentDate.Day;
                        currentMonth = currentDate.Month;
                        currentYear = currentDate.Year;
                        currentHour = currentDate.Hour;

                        if (currentDay != startDay)
                        {
                            bw.Flush();
                            bw.Close();
                            fs.Close();
                            startDay = currentDay;
                            dir1 = dir + "/" + currentYear + "-" + currentMonth + "-" + currentDay + "/" + currentHour;
                            Directory.CreateDirectory(dir1);
                            fs = new FileStream(dir1 + "/Actigraph" + (i + 1) + ".PLFormat", FileMode.Create);
                            bw = new BinaryWriter(fs);
                            bw.Write(Convert.ToInt64(row[0]));
                            bw.Write(Convert.ToInt16(row[1]));
                            bw.Write(Convert.ToInt16(row[2]));
                            bw.Write(Convert.ToInt16(row[3]));
                        }
                        else if (currentHour != startHour)
                        {
                            bw.Flush();
                            bw.Close();
                            fs.Close();
                            startHour = currentHour;
                            dir1 = dir + "/" + currentYear + "-" + currentMonth + "-" + currentDay + "/" + currentHour;
                            Directory.CreateDirectory(dir1);
                            fs = new FileStream(dir1 + "/Actigraph" + (i + 1) + ".PLFormat", FileMode.Create);
                            bw = new BinaryWriter(fs);
                            bw.Write(Convert.ToInt64(row[0]));
                            bw.Write(Convert.ToInt16(row[1]));
                            bw.Write(Convert.ToInt16(row[2]));
                            bw.Write(Convert.ToInt16(row[3]));
                        }
                        else
                        {
                            bw.Write(Convert.ToInt64(row[0]));
                            bw.Write(Convert.ToInt16(row[1]));
                            bw.Write(Convert.ToInt16(row[2]));
                            bw.Write(Convert.ToInt16(row[3]));
                        }

                    }
                    tw.Close();
                    sr.Close();
                    bw.Close();
                    fs.Close();
                }
            }
            else
            {
                if (Directory.Exists(actRawDirectory + "\\Actigraph\\data\\raw\\PLFormat"))
                {
                    string[] actDir = Directory.GetDirectories(actRawDirectory + "\\Actigraph\\data\\raw\\PLFormat");
                    for (int i = 0; i < actDir.Length; i++)
                    {
                        string[] actSubDir = Directory.GetDirectories(actDir[i]);

                        for (int j = 0; j < actSubDir.Length; j++)
                        {
                            string[] actfile = Directory.GetFileSystemEntries(actSubDir[j]);

                            for (int k = 0; k < actfile.Length; k++)
                            {
                                FileStream fs = new FileStream(actfile[k], FileMode.Open);
                                BinaryReader br = new BinaryReader(fs);
                                //FileStream fs1 = new FileStream(actRawDirectory + "\\ActRawData" + (k+1) + ".csv", FileMode.Append);
                                FileStream fs1 = new FileStream(aDataDirectory + "\\merged" + "\\Actigraph_Raw_Data" + (k + 1) + ".csv", FileMode.Append);
                                TextWriter tw = new StreamWriter(fs1);
                                int length = (int)br.BaseStream.Length;
                                int pos = 0;

                                while (pos < length)
                                {
                                    tw.Write(br.ReadInt64());
                                    tw.Write("," + br.ReadInt16() + "," + br.ReadInt16() + "," + br.ReadInt16() + ",");
                                    tw.WriteLine();
                                    pos += 4 * sizeof(Int64);

                                }
                                tw.Close();
                                fs1.Close();
                                br.Close();
                                fs.Close();

                            }

                        }
                    }
                }
            }


            #endregion


            #region Close all files

            if (aMITesDecoder != null)
            {
                foreach (SXML.Sensor sensor in sannotation.Sensors)
                {
                    int sensor_id = Convert.ToInt32(sensor.ID);
                    if (sensor_id > 0)
                    {
                        activityCountCSVs[sensor_id].Flush();
                        samplingCSVs[sensor_id].Flush();
                        averagedRaw[sensor_id].Flush();
                        rmCSVs[sensor_id].Flush();
                        aucCSVs[sensor_id].Flush();
                        vmagCSVs[sensor_id].Flush();
                        activityCountCSVs[sensor_id].Close();
                        samplingCSVs[sensor_id].Close();
                        averagedRaw[sensor_id].Close();
                        rmCSVs[sensor_id].Close();
                        aucCSVs[sensor_id].Close();
                        vmagCSVs[sensor_id].Close();
                    }
                }
            }

            if (hrCSV != null)
            {
                hrCSV.Flush();
                hrCSV.Close();
            }

            if (wcontroller != null)
            {
                for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                {
                    int sensor_id = wcontroller._Sensors[i]._ID;
                    wactivityCountCSVs[sensor_id].Flush();
                    wsamplingCSVs[sensor_id].Flush();
                    waveragedRaw[sensor_id].Flush();
                    wrmCSVs[sensor_id].Flush();
                    waucCSVs[sensor_id].Flush();
                    wvmagCSVs[sensor_id].Flush();
                    wactivityCountCSVs[sensor_id].Close();
                    wsamplingCSVs[sensor_id].Close();
                    waveragedRaw[sensor_id].Close();
                    wrmCSVs[sensor_id].Close();
                    waucCSVs[sensor_id].Close();
                    wvmagCSVs[sensor_id].Close();
                    wocketsTR1[sensor_id].Close();
                }
            }

            masterCSV.Flush();
            masterCSV.Close();
            for (int i = 0; (i < actigraphCSV.Length); i++)
                actigraphCSV[i].Close();

            //JPN: Close WFAC summary datafiles
            if (wWFACSummaryCSV != null)
                for (int i = 0; (i < wWFACSummaryCSV.Length); i++)
                    wWFACSummaryCSV[i].Close();

            //JPN: Close WRAC summary datafiles
            if (wWRACSummaryCSV != null)
                for (int i = 0; (i < wWRACSummaryCSV.Length); i++)
                    wWRACSummaryCSV[i].Close();

            if (sensewearCSV != null)
                sensewearCSV.Close();
            if (zephyrCSV != null)
                zephyrCSV.Close();
            if (oxyconCSV != null)
                oxyconCSV.Close();
            if (omronCSV != null)
                omronCSV.Close();

            if (columbiaCSV != null)
                columbiaCSV.Close();
            if (gpsCSV != null)
                gpsCSV.Close();
            if (rtiCSV != null)
                rtiCSV.Close();
            #endregion Close all files

        }
        
        #endregion

        static int[,] xv = new int[3, 41];

        static int Filter(int data, int axis)
        {
            int mean=0;
            int j=0;
            for (; (j < 40); j++)
            {
                mean += xv[axis, j];
                xv[axis, j] = xv[axis, j + 1];
            }
            mean = mean / 40;
            xv[axis, j] = data;

            if (data > mean)
                return (data - mean);
            else
                return (mean - data);
        }


    }
}