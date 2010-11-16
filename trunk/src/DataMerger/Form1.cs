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
        private static Form2 f;

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

                    #region File Status Window

                    //Older Stuff
                    this.progressForm.AppendLog("Older Merged MITes CSVs .....................Deleting\r\n");
                    string[] file = Directory.GetFileSystemEntries(this.textBox1.Text +"\\"+MERGED_SUBDIRECTORY, "*MITes*.csv");
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


                    //annotation files  (Audio) 
                    if (File.Exists(this.textBox1.Text + "\\" + ANNOTATION_SUBDIRECTORY + "\\audioannotation" + "\\AnnotationIntervals.xml"))
                    {
                        this.progressForm.AppendLog("Annotation File in Audio Folder................Found\r\n");
                        ANNOTATION_SUBDIRECTORY = ANNOTATION_SUBDIRECTORY + "\\audioannotation";
                    }
                    else if (File.Exists(this.textBox1.Text + "\\" + ANNOTATION_SUBDIRECTORY + "\\PhoneAnnotation" + "\\AnnotationIntervals.xml"))
                    {
                        this.progressForm.AppendLog("Annotation File in Phone Folder.....................Found\r\n");
                        ANNOTATION_SUBDIRECTORY = ANNOTATION_SUBDIRECTORY + "\\PhoneAnnotation";
                    }
                    else
                        this.progressForm.AppendLog("Annotation File ..................... Not Found\r\n");


                    #region commented
                    //if (File.Exists(this.textBox1.Text+"\\"+ ANNOTATION_SUBDIRECTORY + "\\AnnotationIntervals.xml"))
                    //    this.progressForm.AppendLog("Annotation File .....................Found\r\n");
                    //else
                    //    this.progressForm.AppendLog("Annotation File ..................... Not Found\r\n");
                    #endregion 


                    //activity labels for annotations (Wockets)
                    if (File.Exists(this.textBox1.Text + "\\" + WOCKETS_SUBDIRECTORY + "\\ActivityLabelsRealtime.xml"))
                        this.progressForm.AppendLog("Activity Labels File .....................Found\r\n");
                    else
                        this.progressForm.AppendLog("Activity Labels File .....................Not Found\r\n");
           


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


                    try
                    {
                        if (File.Exists("Configuration.xml"))
                            File.Copy("Configuration.xml", this.textBox1.Text + "\\" + WOCKETS_SUBDIRECTORY + "\\Configuration.xml", true);
                    }
                    catch
                    {
                    }



                    f= new Form2(this.textBox1.Text);
                    f.Show();


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
                toCSV(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter);
                try
                {
                    toQualityHTML(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter);
                }catch (Exception ee)
                {
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
            int WOCKETS_SR = 92;
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
            session.FromXML(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationIntervals.xml");

            int numPostures = 0;
            Hashtable postures = new Hashtable();
            int k = 0;


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
                    postures.Add(session.OverlappingActivityLists[0][i]._Name , k);
                    k++;
                }

            }

            //Check if postures contain the "unknown" label, otherwise add it
            postures.Add("unknown", k);


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


            #region Initialize Annotations

            int numCategories = session.OverlappingActivityLists.Count;
            int currentAnnotation = 0;

            //Get the number of annotations
            int annotationsLength = session.Annotations.Count;

            //Get the overall session time
            double startTime = session.Annotations[0]._StartUnix;
            double endTime = session.Annotations[annotationsLength-1]._EndUnix;

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


            string summary = "<h2>MITes and Wockets Data Loss, Disconnections and Maxing out Statistics </h2><TABLE border=\"1\">\n";
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
            TextWriter tw = new StreamWriter(aDataDirectory + "\\result.html");
            tw.WriteLine(summary);
            tw.WriteLine("\n<p>&nbsp;</p>\n");



            #endregion



            #region Statistics per Activity Table


            summary = "<h2>Wockets Data Loss by Posture and Activity Statistics</h2><TABLE border=\"1\">\n";
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

            summary = "<h2>Other Sensors Statistics</h2><TABLE border=\"1\">\n";
                header = "<TR>\n<td><div align=\"center\"><strong>Sensor Type</strong></div></td><td><div align=\"center\"><strong>Start Time</strong></div></td><td><strong>Data Present</strong></td><td><strong>Num Samples</strong></td><td><strong>Percent Loss</strong></td></TR>\n";
                header += "</TR>\n";
                summary += header;

                int expectedOxyconRecords=totalSeconds/5;
                double oxyconLoss=0;            
                if (oxyconRecords<expectedOxyconRecords)
                    oxyconLoss = 100 - (((double)oxyconRecords / expectedOxyconRecords) * 100.0);

                summary += "<TR>\n<td><div align=\"center\"><strong>Oxycon</strong></div></td><td>"+(oxyconStart==null?"&nbsp;":oxyconStart)+"</td><td>" + (hasOxycon ? "Yes" : "No") + "</td><td>" + oxyconRecords + "</td><td>" + oxyconLoss.ToString("0") + "%</td></TR>\n";

                
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
                    summary += actigraphLoss.ToString("0")+" %";
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
                if (columbiaRecords <  totalSeconds)
                    columbiaLoss = 100 - (((double)columbiaRecords / totalSeconds) * 100.0);
                summary += "<TR>\n<td><div align=\"center\"><strong>Columbia</strong></div></td><td>" + (columbiaStart == null ? "&nbsp;" : columbiaStart) + "</td><td>" + (hasColumbia ? "Yes" : "No") + "</td><td>" + columbiaRecords + "</td><td>" + columbiaLoss.ToString("0") + "%</td></TR>\n";

                double gpsLoss = 0;
                if (gpsRecords < totalSeconds)
                    gpsLoss = 100 - (((double)gpsRecords / totalSeconds) * 100.0);
                summary += "<TR>\n<td><div align=\"center\"><strong>GPS</strong></div></td><td>" + (gpsStart == null ? "&nbsp;" : gpsStart) + "</td><td>" + (hasGPS ? "Yes" : "No") + "</td><td>" + gpsRecords + "</td><td>" + gpsLoss.ToString("0") + "%</td></TR>\n";


            #endregion


            #endregion



            #region Add the Annotations Summary

            summary += "</TABLE>\n";
            summary += "<h2>Annotation Summary</h2>\n";


            //If the annotation summary file exists, add it to current summary
            //If it doesn't exist, add the HTML to summary 
            if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationSummary.html"))
            {
                TextReader ttr = new StreamReader(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationSummary.html");
                summary += ttr.ReadToEnd();
                ttr.Close();
            }
            else
            {

                #region Create HTML content with stats

                //Create Table & Headers
                summary += "<table border=\"1\">\n";

                //Session total time
                summary += "<tr> <td>Session Total Time</td> <td>" + totalSeconds.ToString() + "</td>" +
                            "<td>&nbsp;</td> <td>&nbsp;</td> </tr>";
                
                //Add a blank column
                summary += "<tr>\n <td>&nbsp;</td> <td>&nbsp;</td> <td>&nbsp;</td> <td>&nbsp;</td> </tr>";

                //Headers for annotation metrics
                summary += "<tr><td>Label</td><td>Duration</td><td>%Occurrence</td><td>Frequency</td></tr>";


                //Scan through labels
                string cur_activity = "";
                int total_secs_activity = 0;
                double percent_duration = 0.0;
                int frequency = 0;

                for (int n = 0; n < session.OverlappingActivityLists.Count; n++)
                {
                    for (int j = 0; j < session.OverlappingActivityLists[n].Count; j++)
                    {
                        cur_activity = session.OverlappingActivityLists[n][j]._Name;
                        total_secs_activity = (int)annotatedPostures[cur_activity];
                        percent_duration = ((double)total_secs_activity / totalSeconds) * 100.0;


                        summary += "<tr>\n<td>" + cur_activity + "</td><td>" + total_secs_activity.ToString() + 
                                   "</td><td>"  + String.Format("{0:0.0}%",percent_duration) + "</td></tr>";                       
                    }
                }


                //Close table
                summary +="</table>";

                #endregion


            }

                
            summary +="</HTML>";

            #endregion 




        tw.WriteLine(summary);
        tw.Close();


        SaveLabelsColorsToFile(aDataDirectory, session.OverlappingActivityLists.Count, session.OverlappingActivityLists);


    #endregion

    #endregion



 }

           


     //--- This colors assigned to the annotation bar in the viewer are protocol specific  ----
     //Check how I can make it more general
     private static void SaveLabelsColorsToFile(string aDataDirectory, int number_of_categories, ConcurrentActivityLists list_of_activities)
     {

           
            //Category
            if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_1.csv"))
            { File.Delete(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_1.csv"); }
            TextWriter labels_colors_csv_1 = new StreamWriter(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\ActivityLabelsColors_1.csv");


            //Write headers
            labels_colors_csv_1.WriteLine("Category,Label,Color,ARGB");

            string label = "";
            string csv = "";
            string color = "";
            string argb = "";
            string category_name = "";


            //Load the list according the number of activity categories 
            for (int i = 0; i < number_of_categories; i++)
            {

               
                    if (list_of_activities[i].Count > 0)
                        category_name = list_of_activities[i][0]._Category;


                    //load labels for each category
                    for (int j = 0; j < list_of_activities[i].Count; j++)
                    {

                        label = list_of_activities[i][j]._Name;

                        csv = "";
                        color = "";
                        argb = "";


                        if (label.Trim().CompareTo("") != 0)
                        {
                            csv = category_name + "," + label + ",";

                            if (i == 0)
                            {
                                if (label.CompareTo("unknown") == 0)
                                {
                                    color = Color.Gainsboro.Name;
                                    argb = Color.Gainsboro.ToArgb().ToString();

                                }
                                else if (label.CompareTo("sync") == 0)
                                {
                                    color = Color.Plum.Name;
                                    argb = Color.Plum.ToArgb().ToString();

                                }
                                else if (label.CompareTo("flap") == 0)
                                {
                                    color = Color.Green.Name;
                                    argb = Color.FromArgb(150, Color.Green).ToArgb().ToString();

                                }
                                else if (label.CompareTo("rock") == 0)
                                {
                                    color = Color.Orange.Name;
                                    argb = Color.FromArgb(200, Color.Orange).ToArgb().ToString();

                                }
                                else if (label.CompareTo("flap-rock") == 0)
                                {
                                    color = Color.DeepSkyBlue.Name;
                                    argb = Color.FromArgb(200, Color.DeepSkyBlue).ToArgb().ToString();

                                }


                                labels_colors_csv_1.WriteLine(csv + color + "," + argb);
                            }




                        }//ends if
                    }//ends for
               


            } //ends if for overlapping activity lists


            //Close files
            labels_colors_csv_1.Flush();
            labels_colors_csv_1.Close();

        }




#endregion




         #region Declare Variables

 public static string MITES_SUBDIRECTORY = "mites";
        public static string WOCKETS_SUBDIRECTORY = "wockets";
        public static string OTHER_SUBDIRECTORY = "othersensors";
        public static string MERGED_SUBDIRECTORY = "merged";
        public static string ANNOTATION_SUBDIRECTORY = "annotation";

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



        #endregion



        #region Generate the Summary Files

        static TextWriter[] summaryCSV;
        static Hashtable[] summaryData;
        static int[] rawSummaryData;
        static TextWriter[] rawSummaryCSV;

        public static void toCSV(string aDataDirectory, string masterDirectory, int maxControllers, string[] filter)
        {

            double previousUnixTime = -1;

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



            //Size of the moving average
            int RM_DURATION = 1000;
            int SAMPLING_RATE = 40;
            int RM_SIZE = (RM_DURATION / 1000) * SAMPLING_RATE;
            

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

            //Variables to store raw data,running mean and areas under curve
            int[, ,] wrawData = null; //channel,axis ->data            
            long[,] wtimeData = null; //channel ->timestamp
            int[,] wAUC = null;
            double[] wVMAG = null;
            int[] whead = null; //channel ->pointer to the head (circular)
            double[] wRMX = null;
            double[] wRMY = null;
            double[] wRMZ = null;
            int[] wRMSize = null;







            TextWriter masterCSV;      //Master CSV
            TextWriter hrCSV;       //HR CSV

            



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
            string rt3_dataline="";





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
            bool rt3Found=false;


            double actigraphOffset = 0;
            double sensewearOffset = 0;
            double zephyrOffset = 0;
            double columbiaOffset = 0;
            double rtiOffset = 0;
            double oxyconOffset = 0;

            double annotationsOffset = 0;
            double mitesOffset = 0;
            double gpsOffset = 0;


            actigraphOffset = f._ActigraphSeconds;
            sensewearOffset = f._SensewearSeconds;
            zephyrOffset = f._ZephyrSeconds;
            columbiaOffset = f._ColumbiaSeconds;
            rtiOffset = f._RTISeconds;
            oxyconOffset = f._OxyconSeconds;

            annotationsOffset = f._AnnotationsSeconds;
            mitesOffset = f._MitesSeconds;
            gpsOffset = f._GpsSeconds;




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
                    int rti_sample_counter=0;
                    rtiTime=rtiOriginTime;
                    while ((rti_line = rtiReader.ReadLine()) != null)
                    {
                        tokens = rti_line.Split(',');
                        if (tokens.Length >= 4)
                        {

                            if (!rtiOriginFound)
                            {
                                string[] dateTokens = tokens[0].Split(new char[] { ' ', '\t' });                            
                                string[] timeTokens=null;
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
                                rtiTime = new DateTime(Convert.ToInt32(dateTokens[2]), Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]),mseconds);
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
                                rtiRMZ =0; 
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


                                if (runningMeanSize<5)
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
            rtiRecords = rtiData.Count ;
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
                    for (int k=0;(k<25);k++)
                        columbia_line = columbiaReader.ReadLine();


                    while ((columbia_line = columbiaReader.ReadLine()) != null)
                    {
                        tokens = columbia_line.Split(',');
                        if (tokens.Length == 14)
                        {
                            
                            string[] dateTokens = tokens[1].Split('/');
                            string[] timeTokens = tokens[2].Split(':');
                            columbiaTime = new DateTime(Convert.ToInt32("20"+dateTokens[2]), Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));

                           // if (columbiaOffset > 0)
                             columbiaTime=columbiaTime.AddSeconds(columbiaOffset);

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

                    actigraphReader = new StreamReader(file[i]);
                    actigraph_line = actigraphReader.ReadLine();//read first line

                    if (actigraph_line.Contains("ActiSoft"))
                    {
                        actigraphType[i] = "ActiSoft";
                        Match m;
                        do
                        {
                            actigraph_line = actigraphReader.ReadLine();
                            tokens = actigraph_line.Split(',');
                            m = Regex.Match(tokens[0].Trim(), "^[0-9]+/[0-9]+/[0-9]+$");
                        } while (m.Success == false);


                        tokens = actigraph_line.Split(',');
                        Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                        
                        
                        //if (actigraphOffset > 0)
                        actigraphTime = actigraphTime.AddSeconds(actigraphOffset);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            tokens = actigraph_line.Split(',');
                            if (tokens[0].Length > 1)
                            {
                                m1 = Regex.Match(tokens[0], "([0-9]+)/([0-9]+)/([0-9]+)");
                                m2 = Regex.Match(tokens[1], "([0-9]+):([0-9]+):([0-9]+)");
                                actigraphTime = new DateTime(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                                //if (actigraphOffset > 0)
                                    actigraphTime = actigraphTime.AddSeconds(actigraphOffset);
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
                        } while (tokens.Length!=3);


                        tokens = actigraph_line.Split(',');
                        //Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        //Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(actiyear, actimonth, actiday, actihour, actiminute, actisecond);//(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                       // if (actigraphOffset > 0)
                            actigraphTime = actigraphTime.AddSeconds(actigraphOffset);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
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
                    else if (actigraph_line.Contains("GT3X"))
                    {
                        actigraphType[i] = "GT3X";
                        Match m;
                        int actihour = 0, actiminute = 0, actisecond = 0, actiyear = 0, actiday = 0, actimonth = 0;
                        do
                        {
                            actigraph_line = actigraphReader.ReadLine();
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
                        } while (tokens.Length!=5);


                        tokens = actigraph_line.Split(',');
                        //Match m1 = Regex.Match(tokens[0].Trim(), "([0-9]+)/([0-9]+)/([0-9]+)");
                        //Match m2 = Regex.Match(tokens[1].Trim(), "([0-9]+):([0-9]+):([0-9]+)");
                        actigraphTime = new DateTime(actiyear, actimonth, actiday, actihour, actiminute, actisecond);//(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                       //if (actigraphOffset > 0)
                            actigraphTime = actigraphTime.AddSeconds(actigraphOffset);
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
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
                            zephyrTime=zephyrTime.AddSeconds(zephyrOffset);
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
                    sensewear_line=sensewearReader.ReadLine(); //skip first line
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
                           sensewearTime=sensewearTime.AddSeconds(sensewearOffset);
                            sensewearUnixTime = UnixTime.GetUnixTime(sensewearTime);
                        }
                        else
                        { //unix time
                            TimeZone localZone = TimeZone.CurrentTimeZone;
                            DaylightTime daylight = localZone.GetDaylightChanges(DateTime.Now.Year);
                            sensewearUnixTime = Convert.ToInt64(tokens[0].Trim()) - (8 * 60 * 60 * 1000);                            
                            UnixTime.GetDateTime((long)sensewearUnixTime, out sensewearTime);

                            if (!TimeZone.IsDaylightSavingTime(new DateTime(sensewearTime.Year,sensewearTime.Month,sensewearTime.Day), daylight))          
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
                            vanderbiltSensewearDataLine += tokens[1]+",";
                            vanderbiltSensewearDataLine += tokens[2]+",";
                            vanderbiltSensewearDataLine += tokens[3]+",";
                            vanderbiltSensewearDataLine += tokens[4]+",";
                            vanderbiltSensewearDataLine += tokens[5]+",";
                            vanderbiltSensewearDataLine += tokens[6]+",";
                            vanderbiltSensewearDataLine += tokens[7]+",";
                            vanderbiltSensewearDataLine += tokens[8]+",";
                            vanderbiltSensewearDataLine += tokens[9]+",";
                            vanderbiltSensewearDataLine +=tokens[10]+",";
                            vanderbiltSensewearDataLine +=tokens[11]+",";
                            vanderbiltSensewearDataLine +=tokens[15];
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


                if ( (sensewearFound) || (sensewearVanderbiltFound))
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
                    gpsCSV= new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\GPS.csv");
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

            #region Load Annotation

            AXML.Annotation aannotation = null;
            try
            {
                if (File.Exists(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationIntervals.xml"))
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
                    xmlSession.FromXML(aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY + "\\AnnotationIntervals.xml");

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
                    { File.Delete(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "AnnotationIntervals.xml"); }

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
            #endregion Load Annotation

            #region Setup MITes Data

            MITesDecoder aMITesDecoder = null;
            MITesHRAnalyzer aMITesHRAnalyzer = null;
            MITesLoggerReader aMITesLoggerReader = null;
            SXML.SensorAnnotation sannotation = null;

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

                    }else
                        master_csv_header += ",HR";
                }

                



                //Initialize arrays based on number of sensors
                rawData = new int[sannotation.MaximumSensorID + 1, 3, RM_SIZE];
                for (int i = 0; (i < sannotation.MaximumSensorID + 1); i++)
                    for (int j=0;(j<3);j++)
                        for (int k=0;(k<RM_SIZE);k++)
                            rawData[i,j,k]=-1;
                timeData = new long[sannotation.MaximumSensorID + 1, RM_SIZE];
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

            #region Setup Wockets Data
            int[] lastDecodedIndex = null;
            WocketsController wcontroller = null;
            double[] wunixtimestamp = null;

            if ((Directory.Exists(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY)) && (Directory.GetFiles(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY).Length>0))
            {
                wcontroller = new WocketsController("", "", "");
                CurrentWockets._Controller = wcontroller;
                wcontroller.FromXML(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\SensorData.xml");
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
                    //Write out raw data
                    TextWriter tw = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "Wocket_" + sensor_id.ToString("00") + "_RawData_" + wcontroller._Sensors[i]._Location.Replace(' ', '-') + ".csv");
                    int lastDecodedPacket = 0;
                    
                        while (wc._Sensors[i].Load())
                        {
                            if (wc._Sensors[i]._Decoder._Head == 0)
                                lastDecodedPacket = wc._Sensors[i]._Decoder._Data.Length - 1;
                            else
                                lastDecodedPacket = wc._Sensors[i]._Decoder._Head - 1;

                            Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[lastDecodedPacket];
                            tw.WriteLine(data.UnixTimeStamp + "," + data._X + "," + data._Y + "," + data._Z);

                            long currentTS=(long)(data.UnixTimeStamp/1000.0);
                            if ((currentTS - prevWocketTS) < 1)
                                wocketSR++;                            
                            if ((prevWocketTS>0) & (currentTS - prevWocketTS)>=1)
                                totalseconds += (int)(currentTS - prevWocketTS);
                            prevWocketTS = currentTS;
                        }
                        wocketsSR[i] = (int) Math.Round((double)wocketSR/(double)totalseconds);
                    tw.Flush();
                    tw.Close();

           


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
                    master_csv_header += ",Wocket" + sensor_id.ToString("00") + "_SR," + "Wocket" + sensor_id.ToString("00") + "_AVRaw_X," +
                        "Wocket" + sensor_id.ToString("00") + "_AVRaw_Y," + "Wocket" + sensor_id.ToString("00") + "_AVRaw_Z," + "Wocket" + sensor_id.ToString("00") + "_SAD_X," +
                        "Wocket" + sensor_id.ToString("00") + "_SAD_Y," + "Wocket" + sensor_id.ToString("00") + "_SAD_Z," + "Wocket" + sensor_id.ToString("00") + "_AUC_X," +
                        "Wocket" + sensor_id.ToString("00") + "_AUC_Y," + "Wocket" + sensor_id.ToString("00") + "_AUC_Z," + "Wocket" + sensor_id.ToString("00") + "_AUC_XYZ," +
                        "Wocket" + sensor_id.ToString("00") + "_RM_X," + "Wocket" + sensor_id.ToString("00") + "_RM_Y," + "Wocket" + sensor_id.ToString("00") + "_RM_Z," +
                        "Wocket" + sensor_id.ToString("00") + "_RM_SIZE," + "Wocket" + sensor_id.ToString("00") + "_VMAG";
                }

                wc.Dispose();

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
                    wocketsTW[k] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\" + "Wocket_" + wcontroller._Sensors[k]._ID.ToString("00") + "_RawCorrectedData_"  + wcontroller._Sensors[k]._Location.Replace(' ', '-') + ".csv");

                    ArrayList[] loadedData = new ArrayList[LoadedSeconds];
                    long[] loadedDataTime = new long[LoadedSeconds];
                    for (int m = 0; (m < LoadedSeconds); m++)
                        loadedData[m] = new ArrayList();
                    int loadedIndex = 0;
                    string dataline = "";
                    long lastSecond = 0;
                    int nextCorrected = 0;
                    long nextCorrectedTime = 0;
                    double delta = 1000.0/wocketsSR[k];
                    double recordTime = 0;

                    if (CSVProgress == "")
                        CSVProgress = "Correcting Timestamps for Raw Data File for Wocket " +  wcontroller._Sensors[k]._ID.ToString("00");

                    while ((dataline = wocketsTR[k].ReadLine()) != null)
                    {
                        string[] wocketTokens = dataline.Split(',');
                        int wocketX = Convert.ToInt32(wocketTokens[1]);
                        int wocketY = Convert.ToInt32(wocketTokens[2]);
                        int wocketZ = Convert.ToInt32(wocketTokens[3]);
                        long unixtime = (long)(Convert.ToDouble(wocketTokens[0])/1000.0);

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


                            while ((lastSecond != unixtime) && (unixtime!=0))
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
                            wrawData[i,j,k]=-1;
                wtimeData = new long[wcontroller._Sensors.Count, RM_SIZE];
                wAUC = new int[wcontroller._Sensors.Count, 3];
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
                                string[] matchingFiles = Directory.GetFiles(subdirectory + "\\" + i, "Sensor-*" + k + ".csv");
                                for (int j = 0; (j < matchingFiles.Length); j++)
                                    files[k].Add(matchingFiles[j]);
                            }
                        }
                    }
                }

                summaryCSV = new TextWriter[CurrentWockets._Controller._Sensors.Count];
                rawSummaryCSV = new TextWriter[CurrentWockets._Controller._Sensors.Count];
                summaryData = new Hashtable[CurrentWockets._Controller._Sensors.Count];
                rawSummaryData = new int[CurrentWockets._Controller._Sensors.Count];

                try
                {

                    for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                    {
                        summaryCSV[i] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + i.ToString("00") + "_Summary.csv");
                        rawSummaryCSV[i] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Wocket_" + i.ToString("00") + "_RawSummary.csv");
                        summaryData[i] = new Hashtable();
                        rawSummaryData[i] = 0;
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


                                        //
                                        summaryData[i].Add(summaryKey, summaryLine);

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



            for (int i = 0; (i < actigraphData.Length); i++)
            {
                if (actigraphType[i] == "GT3X")
                {
                    master_csv_header += ",Actigraph" + (i + 1) + "_X,Actigraph" + (i + 1) + "_Y,Actigraph" + (i + 1) + "_Z";
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


            if (summaryData != null)
            {
                for (int i = 0; (i < summaryData.Length); i++)
                {
                    master_csv_header += ",WocketSummary" + i.ToString("00") + ",RawWocketSummary" + i.ToString("00");
                    summaryCSV[i].WriteLine(summary_csv_header);
                }
            }
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








            int year = 0;

            int month = 0;
            int day = 0;
            int startyear = 0;
            int startmonth = 0;
            int startday = 0;
            int starthr = 25;
            int startmin = 0;
            int startsec = 0;

            int endyear = 0;
            int endmonth = 0;
            int endday = 0;
            int endhr = -1;
            int endmin = 59;
            int endsec = 59;



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

                    if ((startyear == 0) || (year < startyear))
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


                    for (int i = 0; i < 30; i++)
                    {
                        if (Directory.Exists(subdirectory + "\\" + i))
                        {
                            int hr = i;
                            if (hr < starthr)
                                starthr = hr;
                            if (hr > endhr)
                                endhr = hr;
                        }

                    }
                }
            }

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

                    if ((startyear == 0) || (year < startyear))
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


                    for (int i = 0; i < 30; i++)
                    {
                        if (Directory.Exists(subdirectory + "\\" + i))
                        {
                            int hr = i;
                            if (hr < starthr)
                                starthr = hr;
                            if (hr > endhr)
                                endhr = hr;
                        }

                    }
                }
            }


            //sele check
            #region check annotation start and end times
            
            
            if (aannotation != null)
            {
                AXML.AnnotatedRecord record = ((AXML.AnnotatedRecord)aannotation.Data[0]);
                year = Convert.ToInt32(record.StartDate.Split('-')[2]);
                month = Convert.ToInt32(record.StartDate.Split('-')[0]);
                day = Convert.ToInt32(record.StartDate.Split('-')[1]);
                if ((startyear == 0) || (year < startyear))
                    startyear = year;

                if ((startmonth == 0) || (month < startmonth))
                    startmonth = month;
                if ((startday == 0) || (day < startday))
                    startday = day;

                if (record.StartHour < starthr)
                    starthr = record.StartHour;

                record = ((AXML.AnnotatedRecord)aannotation.Data[aannotation.Data.Count - 1]);
                year = Convert.ToInt32(record.StartDate.Split('-')[2]);
                month = Convert.ToInt32(record.StartDate.Split('-')[0]);
                day = Convert.ToInt32(record.StartDate.Split('-')[1]);

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
            }


            #endregion



            DateTime startDateTime = new DateTime(startyear, startmonth, startday, starthr, startmin, startsec);
            DateTime endDateTime = new DateTime(endyear, endmonth, endday, endhr, endmin, endsec);
            DateTime currentDateTime = startDateTime;


            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0); ;
            TimeSpan diff;
            string timestamp = "";
            double currentUnixTime = 0;






            #region Initialize CSV lines
                string master_csv_line = "";
                string hr_csv_line = "";
                
                string[] actigraph_csv_line = new string[actigraphData.Length];                
                for (int i = 0; (i < actigraphData.Length); i++)
                    actigraph_csv_line[i] = "";

                string[] summary_csv_line = null; 
                if (summaryData != null)
                {
                    summary_csv_line = new string[summaryData.Length];
                    for (int i = 0; (i < summaryData.Length); i++)
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

            TextReader[] wocketsTR1=null;
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

                if (summaryData != null)
                {
                    for (int i = 0; (i < summaryData.Length); i++)
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

                    #region Load Activity Label
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


                double mitesTime = 0;

                //if there is MITes data
                if (aMITesDecoder != null)
                {

                    #region Load MITes data if needed

                    //always have at least 5 seconds worth of data for the MITes
                    while (((unixtimestamp - currentUnixTime) <= RM_DURATION) && (aMITesLoggerReader.GetSensorData(10)))
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
                                head[channel] = (head[channel] + 1) % RM_SIZE;

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
                            head[channel] = (head[channel] + 1) % RM_SIZE;

                            
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
                                    headPtr = RM_SIZE-1;
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

                    #region Append MITes Statistics

                    #region Write CSV line for MITes HR

                    #endregion Write CSV line for MITes HR


                    #endregion Append MITes Statistics

                }


                //if there is Wockets data
                if (wcontroller != null)
                {
                    
                    #region Load Wockets data if needed
                    for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                    {

                        string s = "";
                        while (((wunixtimestamp[i] - currentUnixTime) <= RM_DURATION) && ((s=wocketsTR1[i].ReadLine())!=null))
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
                            wheadPtr = RM_SIZE-1;

                        //compute running means


                        while ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] > 0) && (wheadPtr != whead[wcontroller._Sensors[i]._ID]) && (wnumMeanPts <= (RM_SIZE-1)))
                        {
                            wrunningMeanX += wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr];
                            wrunningMeanY += wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr];
                            wrunningMeanZ += wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr];
                            wnumMeanPts++;                           
                            wheadPtr--;

                            if (wheadPtr < 0)
                                wheadPtr = (RM_SIZE-1);
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
                            wheadPtr = (RM_SIZE-1);
                        //compute values per second




                        while ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] > 0) && (wheadPtr != whead[wcontroller._Sensors[i]._ID]))
                        {
                            double ttt=wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] ;

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
                                }

                                wprevX[wcontroller._Sensors[i]._ID] = wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr];
                                wprevY[wcontroller._Sensors[i]._ID] = wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr];
                                wprevZ[wcontroller._Sensors[i]._ID] = wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr];


                                int wprevHead = wheadPtr - 1;
                                if (wprevHead < 0)
                                    wprevHead = (RM_SIZE-1);


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
                                wheadPtr = (RM_SIZE-1);
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
                        wVMAG[wcontroller._Sensors[i]._ID] = 0;
                        for (int k = 0; (k < RM_SIZE); k++)
                        {
                            wAUC[wcontroller._Sensors[i]._ID, 0] = wAUC[wcontroller._Sensors[i]._ID, 0] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] - wrunningMeanX));
                            wAUC[wcontroller._Sensors[i]._ID, 1] = wAUC[wcontroller._Sensors[i]._ID, 1] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] - wrunningMeanY));
                            wAUC[wcontroller._Sensors[i]._ID, 2] = wAUC[wcontroller._Sensors[i]._ID, 2] + (int)Math.Abs((wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] - wrunningMeanZ));
                            wVMAG[wcontroller._Sensors[i]._ID] = wVMAG[wcontroller._Sensors[i]._ID] + Math.Sqrt(Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] - wrunningMeanX), 2.0) + Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] - wrunningMeanY), 2.0) + Math.Pow((double)(wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] - wrunningMeanZ), 2.0));
                        }



                        #region Append Wockets Statistics

                        int sensor_id = wcontroller._Sensors[i]._ID;
                        csv_line1 = timestamp;
                        csv_line2 = timestamp;
                        csv_line3 = timestamp;
                        csv_line4 = timestamp;
                        csv_line5 = timestamp;
                        csv_line6 = timestamp;

                        if (wacCounters[sensor_id] > 0)
                        {
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
                         
                            
                            if (rawSummaryData!=null)
                                rawSummaryData[i] += (int)((double)(wAUC[sensor_id, 0] + wAUC[sensor_id, 1] + wAUC[sensor_id, 2]));

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

                        #endregion Append Wockets Statistics
                    }

                    #endregion Calculate Statistics

                }


                #region Write CSV lines for Actigraphs
                for (int i = 0; (i < actigraphData.Length); i++)
                {
                    if (actigraphData[i].ContainsKey(key) == false)
                    {
                        if (actigraphType[i] == "GT3X")
                        {
                            actigraphCSV[i].WriteLine(actigraph_csv_line[i] + ",,,");
                            master_csv_line = master_csv_line + ",,,";
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
                    }
                }
                #endregion Write CSV lines for Actigraphs


                #region Write CSV lines for Wockets Summary
                if (summaryData != null)
                {
                    for (int i = 0; (i < summaryData.Length); i++)
                    {
                        if (summaryData[i].ContainsKey(key) == false)
                        {
                            summaryCSV[i].WriteLine(summary_csv_line[i] + ",");
                            rawSummaryCSV[i].WriteLine(summary_csv_line[i] + ",");
                            master_csv_line = master_csv_line + ",,";
                        }
                        else
                        {
                            string myline = summary_csv_line[i] + "," + summaryData[i][key];
                            summaryCSV[i].WriteLine(summary_csv_line[i] + "," + summaryData[i][key]);
                            rawSummaryCSV[i].WriteLine(summary_csv_line[i] + "," + rawSummaryData[i]);
                            master_csv_line = master_csv_line + "," + summaryData[i][key] + "," + rawSummaryData[i];
                            rawSummaryData[i] = 0;
                        }
                    }
                }
                #endregion Write CSV lines for Wockets Summary

                #region Write CSV line for Sensewear
                if ((sensewearFound) && (sensewearCSV != null))
                {
                    if (SSR.ContainsKey(key))
                    {
                        sensewearCSV.WriteLine(sensewear_csv_line + "," + (int)SSR[key] + "," + (double)STrans[key] +
                            "," + (double)SLong[key] + "," + (double)SAcc[key]);
                        master_csv_line = master_csv_line +","+ (int)SSR[key] + "," + (double)STrans[key] +
                            "," + (double)SLong[key] + "," + (double)SAcc[key];
                    }
                    else
                    {
                        sensewearCSV.WriteLine(sensewear_csv_line + ",,,,");
                        master_csv_line = master_csv_line + ",,,,";
                    }
                }
                //else
                 //   master_csv_line = master_csv_line + ",,,,";
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
                //else
                  //  master_csv_line = master_csv_line + ",,,,,,,,,,,,,";


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
               // else
               //     master_csv_line = master_csv_line + ",,,,,,,,,,,,,,,,";
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
             //   else
               //     master_csv_line = master_csv_line + ",,,,,,,,";
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
               // else
                 //   master_csv_line = master_csv_line + ",";
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
             //   else
               //     master_csv_line = master_csv_line + ",,,,,";
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
              //  else
                //    master_csv_line = master_csv_line + ",,,,";
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
               // else
                 //   master_csv_line = master_csv_line + ",,,,";
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
                else
                    master_csv_line = master_csv_line + ",,,,";
                #endregion Write CSV line for RT3

                #region Write master CSV line
                masterCSV.WriteLine(master_csv_line);
                #endregion Write master CSV line


                //reinitialize variables
                hrCount = 0;
                sumHR = 0;

                currentDateTime = currentDateTime.AddSeconds(1.0);
            }


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

            if (summaryCSV != null)
            {
                for (int i = 0; (i < summaryCSV.Length); i++)
                {
                    summaryCSV[i].Close();
                    rawSummaryCSV[i].Close();
                }
            }
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




    }
}