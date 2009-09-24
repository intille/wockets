using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Threading;
using HousenCS.MITes;
using System.Collections;
using System.Text.RegularExpressions;
using Wockets.Data.Annotation;
using Wockets;

namespace DataMerger
{
    public partial class Form1 : Form
    {
        ProgressForm progressForm;

        public Form1()
        {
            InitializeComponent();
            progressForm = new ProgressForm();
            progressForm.Show();

        }


        private void button2_Click(object sender, EventArgs e)
        {
            DialogResult result = this.folderBrowserDialog1.ShowDialog();
            if (result == DialogResult.OK)
            {
                this.textBox1.Text = this.folderBrowserDialog1.SelectedPath;


                //Check if all the files that we are looking for exist
                try
                {
                    /*string[] file = Directory.GetDirectories(this.textBox1.Text);
                    foreach (string directory in file)
                        if (directory.Contains("phone"))
                        {
                            this.progressForm.AppendLog("Phone Annotation .....................Found\r\n");
                            if ((File.Exists(directory + "\\AnnotationIntervals.xml")) && (File.Exists(directory + "\\AnnotationIntervals.csv")) &&
                                (File.Exists(this.textBox1.Text + "\\AnnotationIntervals.xml")) && (File.Exists(this.textBox1.Text + "\\AnnotationIntervals.csv")))
                            {
                                File.Copy(this.textBox1.Text + "\\AnnotationIntervals.xml", this.textBox1.Text + "\\AnnotationIntervalsPC.xml", true);
                                File.Copy(this.textBox1.Text + "\\AnnotationIntervals.csv", this.textBox1.Text + "\\AnnotationIntervals-PC.csv", true);

                                File.Copy(directory + "\\AnnotationIntervals.xml", this.textBox1.Text + "\\AnnotationIntervals.xml", true);
                                File.Copy(directory + "\\AnnotationIntervals.csv", this.textBox1.Text + "\\AnnotationIntervals.csv", true);
                                this.progressForm.AppendLog("Phone Annotation .....................Copied\r\n");
                            }
                        }
                     */

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

                
                    //annotation files   
                    if (File.Exists(this.textBox1.Text+"\\"+ ANNOTATION_SUBDIRECTORY + "\\AnnotationIntervals.xml"))
                        this.progressForm.AppendLog("Annotation File .....................Found\r\n");
                    else
                        this.progressForm.AppendLog("Annotation File ..................... Not Found\r\n");


                    if (File.Exists(this.textBox1.Text + "\\" + WOCKETS_SUBDIRECTORY + "\\ActivityLabelsRealtime.xml"))
                        this.progressForm.AppendLog("Activity Labels File .....................Found\r\n");
                    else
                        this.progressForm.AppendLog("Activity Labels File .....................Not Found\r\n");
           
                    //Sensewear
                    file = Directory.GetFileSystemEntries(this.textBox1.Text+"\\"+ OTHER_SUBDIRECTORY, "*-sensewear*.csv");
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

                }
                catch (Exception ex)
                {
                    MessageBox.Show("Error: " + ex.Message);
                    Application.Exit();
                }

                this.button1.Enabled = true;
            }

        }

        private void ConversionThread()
        {
            string[] filter = new string[2];
            filter[0] = "annotation";
            filter[1] = "setup";
            try
            {
                toCSV(this.textBox1.Text, "..\\NeededFiles\\Master\\", 3, filter);
            }
            catch (Exception e)
            {
                MessageBox.Show("Error: Format error in the CSV files " + e.StackTrace);
                Environment.Exit(0);
            }
            converted = true;

        }

        private Thread aConversionThread;
        private bool converted = false;
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



        //directories

        public static string MITES_SUBDIRECTORY = "mites";
        public static string WOCKETS_SUBDIRECTORY = "wockets";
        public static string OTHER_SUBDIRECTORY = "othersensors";
        public static string MERGED_SUBDIRECTORY = "merged";
        public static string ANNOTATION_SUBDIRECTORY = "annotation\\audioannotation";

        public static string CSVProgress = "";
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
            int MEAN_SIZE = 5000;


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

            //Actigraph
            TextWriter[] actigraphCSV;
            Hashtable[] actigraphData;
            string[] actigraphType;



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
            string actigraph_csv_header_gt1m = "UnixTimeStamp,TimeStamp,ActigraphX,ActigraphY";
            string actigraph_csv_header_gtx = "UnixTimeStamp,TimeStamp,ActigraphX,ActigraphY,ActigraphZ";
            string sensewear_csv_header = "UnixTimeStamp,TimeStamp,SensewearSR,Sensewear_AVTranAcc,Senserwear_AVLongAcc,Sensewear_AVForAcc";
            string zephyr_csv_header = "UnixTimeStamp,TimeStamp,ZephyrHeart Rate Data,ZephyrECG - Amplitude Data,ZephyrECG - Noise Data,ZephyrRES - Breathing Wave Amplitude (V) Data,ZephyrRES - Respiration Rate Data,ZephyrTEM - Skin Temperature Data,ZephyrBAT - Battery Voltage (V) Data,ZephyrPOS - Posture Data,ZephyrACC - Activity Data,ZephyrACC - Peak Acceleration (g) Data,ZephyrACC - Vertical Acc Minimum (g) Data,ZephyrACC - Vertical Acc Peak (g) Data,ZephyrACC - Lateral Acc Minimum (g) Data,ZephyrACC - Lateral Acc Peak (g) Data,ZephyrACC - Sagittal Acc Minimum (g) Data,ZephyrACC - Sagittal Acc Peak (g)";
            string oxycon_csv_header = "UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2,OxyconVO2kg,OxyconMET,OxyconEE,OxyconRER";
            string omron_csv_header = "UnixTimeStamp,TimeStamp,Steps";
            string columbia_csv_header = "UnixTimeStamp,TimeStamp,ColumbiaX,ColumbiaY,ColumbiaZ,ColumbiaFlow,ColumbiaValve";
            string gps_csv_header = "UnixTimeStamp,TimeStamp,GPSLatitude,GPSLongitude,GPSSpeed,GPSAltitude";
            string master_csv_header = "UnixTimeStamp,TimeStamp";

            //files found

            bool sensewearFound = false;
            bool zephyrFound = false;
            bool oxyconFound = false;
            bool omronFound = false;
            bool columbiaFound = false;
            bool gpsFound = false;
            bool rtiFound = false;





            #region Read Columbia data
            string[] file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-columbia*.csv");

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
                            columbiaUnixTime = UnixTime.GetUnixTime(columbiaTime);
                            string columbiaKey = columbiaTime.Year + "-" + columbiaTime.Month + "-" + columbiaTime.Day + "-" + columbiaTime.Hour + "-" + columbiaTime.Minute + "-" + columbiaTime.Second;
                            string columbiaLine = "";

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
                            gpsUnixTime = UnixTime.GetUnixTime(gpsTime);
                            string gpsKey = gpsTime.Year + "-" + gpsTime.Month + "-" + gpsTime.Day + "-" + gpsTime.Hour + "-" + gpsTime.Minute + "-" + gpsTime.Second;
                            string gpsLine = "";

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
                            gpsLine += ",";

                            if (gpsData.Contains(gpsKey) == false)
                                gpsData.Add(gpsKey, gpsLine);
                        }
                    }

                    gpsFound = true;
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
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            tokens = actigraph_line.Split(',');
                            if (tokens[0].Length > 1)
                            {
                                m1 = Regex.Match(tokens[0], "([0-9]+)/([0-9]+)/([0-9]+)");
                                m2 = Regex.Match(tokens[1], "([0-9]+):([0-9]+):([0-9]+)");
                                actigraphTime = new DateTime(Convert.ToInt32("20" + m1.Groups[3].Value), Convert.ToInt32(m1.Groups[1].Value), Convert.ToInt32(m1.Groups[2].Value), Convert.ToInt32(m2.Groups[1].Value), Convert.ToInt32(m2.Groups[2].Value), Convert.ToInt32(m2.Groups[3].Value));
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
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
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            tokens = actigraph_line.Split(',');
                            if (tokens.Length == 3)
                            {
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
                                string actigraphLine = Convert.ToInt32(tokens[0]) + "," + Convert.ToInt32(tokens[1]);
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
                        actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);

                        do
                        {
                            tokens = actigraph_line.Split(',');
                            if (tokens.Length == 5)
                            {
                                actigraphUnixTime = UnixTime.GetUnixTime(actigraphTime);
                                string actigraphKey = actigraphTime.Year + "-" + actigraphTime.Month + "-" + actigraphTime.Day + "-" + actigraphTime.Hour + "-" + actigraphTime.Minute + "-" + actigraphTime.Second;
                                string actigraphLine = Convert.ToInt32(tokens[0]) + "," + Convert.ToInt32(tokens[1]) + "," + Convert.ToInt32(tokens[2]);
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
                            zephyrUnixTime = UnixTime.GetUnixTime(zephyrTime);
                            string zephyrKey = zephyrTime.Year + "-" + zephyrTime.Month + "-" + zephyrTime.Day + "-" + zephyrTime.Hour + "-" + zephyrTime.Minute + "-" + zephyrTime.Second;
                            string zephyrLine = "";

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

                file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-flashcard*");
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
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-flashcard.dat");
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
                    file = Directory.GetFileSystemEntries(aDataDirectory + "\\" + OTHER_SUBDIRECTORY, "*-flashcard.dat");
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

                                    oxyconUnixTime = UnixTime.GetUnixTime(oxyconTime);
                                    string oxyconKey = oxyconTime.Year + "-" + oxyconTime.Month + "-" + oxyconTime.Day + "-" + oxyconTime.Hour + "-" + oxyconTime.Minute + "-" + oxyconTime.Second;
                                    string oxyconLine = "";
                                    if (oxyconTime.Day >= 10)
                                        Console.Write("");
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
                                    oxyconLine += ",";
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
                                    string oxyconKey = oxyconTime.Year + "-" + oxyconTime.Month + "-" + oxyconTime.Day + "-" + oxyconTime.Hour + "-" + oxyconTime.Minute + "-" + oxyconTime.Second;
                                    string oxyconLine = "";

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
                                    oxyconLine += ",";
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
                                    string oxyconKey = oxyconTime.Year + "-" + oxyconTime.Month + "-" + oxyconTime.Day + "-" + oxyconTime.Hour + "-" + oxyconTime.Minute + "-" + oxyconTime.Second;
                                    string oxyconLine = "";

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
                                    oxyconLine += ",";
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
                    sensewearReader.ReadLine(); //skip first line


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
                            DateTime sensewearDateTime=new DateTime(Convert.ToInt32(dateTokens[0]), Convert.ToInt32(dateTokens[1]), Convert.ToInt32(dateTokens[2]), Convert.ToInt32(timeTokens[0]), Convert.ToInt32(timeTokens[1]), Convert.ToInt32(timeTokens[2]));
                            sensewearUnixTime = UnixTime.GetUnixTime(sensewearDateTime);
                        }
                        else //unix time
                            sensewearUnixTime = Convert.ToInt64(tokens[0].Trim()) - (8 * 60 * 60 * 1000);
                        
                        UnixTime.GetDateTime((long)sensewearUnixTime, out sensewearTime);

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

                        prevSensewearTime = sensewearTime;

                    }

                    sensewearFound = true;
                }
            }
            catch (Exception e)
            {
                throw new Exception("Sensewear: Parsing failed " + e.Message);
            }
            #endregion Read Sensewear data





            #region Setup master and other sensor files
            try
            {
                masterCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\MITesSummaryData.csv");
                hrCSV = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\HeartRate_MITes.csv");
                for (int i = 0; (i < actigraphCSV.Length); i++)
                    actigraphCSV[i] = new StreamWriter(aDataDirectory + "\\" + MERGED_SUBDIRECTORY + "\\Actigraph" + (i + 1) + ".csv");
                if (sensewearFound)
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
                    AXML.Reader reader = new AXML.Reader(masterDirectory, aDataDirectory + "\\" + ANNOTATION_SUBDIRECTORY, "AnnotationIntervals.xml");
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
                rawData = new int[sannotation.MaximumSensorID + 1, 3, 500];
                timeData = new long[sannotation.MaximumSensorID + 1, 500];
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

            if (Directory.Exists(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY))
            {
                wcontroller = new WocketsController("", "", "");
                wcontroller.FromXML(aDataDirectory + "\\" + WOCKETS_SUBDIRECTORY + "\\SensorData.xml");
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
                for (int i = 0; (i < wcontroller._Sensors.Count); i++)
                {
                    int sensor_id = wcontroller._Sensors[i]._ID;
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






                //Initialize arrays based on number of sensors
                wrawData = new int[wcontroller._Sensors.Count, 3, 500];
                wtimeData = new long[wcontroller._Sensors.Count, 500];
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
            master_csv_header += ",SensewearSR,Sensewear_AVTranAcc,Senserwear_AVLongAcc,Sensewear_AVForAcc";
            master_csv_header += ",ZephyrHeart Rate Data,ZephyrECG - Amplitude Data,ZephyrECG - Noise Data,ZephyrRES - Breathing Wave Amplitude (V) Data,ZephyrRES - Respiration Rate Data,ZephyrTEM - Skin Temperature Data,ZephyrBAT - Battery Voltage (V) Data,ZephyrPOS - Posture Data,ZephyrACC - Activity Data,ZephyrACC - Peak Acceleration (g) Data,ZephyrACC - Vertical Acc Minimum (g) Data,ZephyrACC - Vertical Acc Peak (g) Data,ZephyrACC - Lateral Acc Minimum (g) Data,ZephyrACC - Lateral Acc Peak (g) Data,ZephyrACC - Sagittal Acc Minimum (g) Data,ZephyrACC - Sagittal Acc Peak (g)";
            master_csv_header += ",OxyconHR,OxyconBF,OxyconVE,OxyconVO2,OxyconVO2kg,OxyconMET,OxyconEE,OxyconRER";//OxyconRER,Oxyconttot,Oxycontex";
            master_csv_header += ",OmronSteps";
            master_csv_header += ",ColumbiaX,ColumbiaY,ColumbiaZ,ColumbiaFlow,ColumbiaValve";
            master_csv_header += ",GPSLatitude,GPSLongitude,GPSSpeed,GPSAltitude";
            masterCSV.WriteLine(master_csv_header);
            hrCSV.WriteLine(hr_csv_header);
            if ((sensewearCSV != null) && (sensewearFound))
                sensewearCSV.WriteLine(sensewear_csv_header);
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

                string[] subdirectories = Directory.GetDirectories(rawDirectory);
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

                string[] subdirectories = Directory.GetDirectories(rawDirectory);
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

            //check annotation start and end times
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

            DateTime startDateTime = new DateTime(startyear, startmonth, startday, starthr, startmin, startsec);
            //startDateTime = startDateTime.AddMinutes(-15.0);
            DateTime endDateTime = new DateTime(endyear, endmonth, endday, endhr, endmin, endsec);
            //endDateTime = endDateTime.AddMinutes(15.0);
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
            string sensewear_csv_line = "";
            string zephyr_csv_line = "";
            string oxycon_csv_line = "";
            string omron_csv_line = "";
            string columbia_csv_line = "";
            string gps_csv_line = "";
            string rti_csv_line = "";
            #endregion Initialize CSV lines

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
                sensewear_csv_line = timestamp;
                zephyr_csv_line = timestamp;
                oxycon_csv_line = timestamp;
                omron_csv_line = timestamp;
                columbia_csv_line = timestamp;
                gps_csv_line = timestamp;
                rti_csv_line = timestamp;
                
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
                //if there is MITes data
                if (aMITesDecoder != null)
                {

                    #region Load MITes data if needed

                    //always have at least 5 seconds worth of data for the MITes
                    while (((unixtimestamp - currentUnixTime) <= MEAN_SIZE) && (aMITesLoggerReader.GetSensorData(10)))
                    {
                        channel = aMITesDecoder.GetSomeMITesData()[0].channel;

                        if (channel == 0)
                        {
                            //Store raw heart rate
                            int hr = aMITesHRAnalyzer.UpdateOffline();
                            if (hr > 0)
                            {
                                rawData[channel, 0, head[channel]] = hr;
                                timeData[channel, head[channel]] = (long)unixtimestamp;
                                head[channel] = (head[channel] + 1) % 500;
                            }
                        }
                        else
                        {
                            x = aMITesDecoder.GetSomeMITesData()[0].x;
                            y = aMITesDecoder.GetSomeMITesData()[0].y;
                            z = aMITesDecoder.GetSomeMITesData()[0].z;
                            unixtimestamp = aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp;
                            rawData[channel, 0, head[channel]] = x;
                            rawData[channel, 1, head[channel]] = y;
                            rawData[channel, 2, head[channel]] = z;
                            timeData[channel, head[channel]] = (long)unixtimestamp;
                            head[channel] = (head[channel] + 1) % 500;
                        }

                    }

                    #endregion Load MITes data if needed

                    #region Calculate Statistics

                    foreach (SXML.Sensor sensor in sannotation.Sensors)
                    {
                        channel = Convert.ToInt32(sensor.ID);



                        int headPtr = head[channel] - 1;
                        if (headPtr < 0)
                            headPtr = 499;


                        if (channel > 0)
                        {
                            double runningMeanX = 0;
                            double runningMeanY = 0;
                            double runningMeanZ = 0;
                            int numMeanPts = 0;

                            //compute running means
                            // && ((timeData[channel, headPtr] - currentUnixTime) <=MEAN_SIZE)

                            while ((timeData[channel, headPtr] > 0) && (headPtr != head[channel]) && (numMeanPts <= 499))
                            {
                                runningMeanX += rawData[channel, 0, headPtr];
                                runningMeanY += rawData[channel, 1, headPtr];
                                runningMeanZ += rawData[channel, 2, headPtr];
                                numMeanPts++;
                                headPtr--;
                                if (headPtr < 0)
                                    headPtr = 499;
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
                                headPtr = 499;
                            //compute values per second

                            while ((timeData[channel, headPtr] > 0) && (headPtr != head[channel]))
                            {
                                if (((timeData[channel, headPtr] - currentUnixTime) >= 0) && ((timeData[channel, headPtr] - currentUnixTime) <= 1000))
                                {

                                    //Calculate MITes Raw Values
                                    if ((channel != 0) && (channel <= sannotation.MaximumSensorID)) //if junk comes ignore it
                                    {
                                        if ((prevX[channel] > 0) && (prevY[channel] > 0) && (prevZ[channel] > 0) && (rawData[channel, 0, headPtr] > 0) && (rawData[channel, 1, headPtr] > 0) && (rawData[channel, 2, headPtr] > 0))
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
                                            prevHead = 499;


                                        //trapezoid
                                        //double a2=rawData[channel, 0, headPtr];
                                        //double a1=rawData[channel, 0, prevHead];
                                        //a2 = a2 - runningMeanX;
                                        //a1 = a1 - runningMeanX;

                                        double t2 = timeData[channel, headPtr];
                                        double t1 = timeData[channel, prevHead];
                                        if ((t2 > 0) & (t1 > 0))
                                        {

                                            AUC[channel, 0] = AUC[channel, 0] + (int)Math.Abs((rawData[channel, 0, headPtr] - runningMeanX));
                                            AUC[channel, 1] = AUC[channel, 1] + (int)Math.Abs((rawData[channel, 1, headPtr] - runningMeanY));
                                            AUC[channel, 2] = AUC[channel, 2] + (int)Math.Abs((rawData[channel, 2, headPtr] - runningMeanZ));
                                            VMAG[channel] = VMAG[channel] + Math.Sqrt(Math.Pow((double)(rawData[channel, 0, headPtr] - runningMeanX), 2.0) + Math.Pow((double)(rawData[channel, 1, headPtr] - runningMeanY), 2.0) + Math.Pow((double)(rawData[channel, 2, headPtr] - runningMeanZ), 2.0));
                                        }


                                    }
                                }

                                headPtr--;
                                if (headPtr < 0)
                                    headPtr = 499;
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
                                    headPtr = 499;
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

                        //always have at least 5 seconds worth of data for the MITes
                        while (((wunixtimestamp[i] - currentUnixTime) <= MEAN_SIZE) && (wcontroller._Sensors[i].Load()))
                        {

                            if (wcontroller._Sensors[i]._Decoder._Head == 0)
                                lastDecodedIndex[i] = wcontroller._Sensors[i]._Decoder._Data.Length - 1;
                            else
                                lastDecodedIndex[i] = wcontroller._Sensors[i]._Decoder._Head - 1;

                            Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wcontroller._Sensors[i]._Decoder._Data[lastDecodedIndex[i]];
                            wrawData[wcontroller._Sensors[i]._ID, 0, whead[wcontroller._Sensors[i]._ID]] = data.X;
                            wrawData[wcontroller._Sensors[i]._ID, 1, whead[wcontroller._Sensors[i]._ID]] = data.Y;
                            wrawData[wcontroller._Sensors[i]._ID, 2, whead[wcontroller._Sensors[i]._ID]] = data.Z;
                            wtimeData[wcontroller._Sensors[i]._ID, whead[wcontroller._Sensors[i]._ID]] = (long)data.UnixTimeStamp;
                            wunixtimestamp[i] = data.UnixTimeStamp;
                            whead[wcontroller._Sensors[i]._ID] = (whead[wcontroller._Sensors[i]._ID] + 1) % 500;

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
                            wheadPtr = 499;

                        //compute running means


                        while ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] > 0) && (wheadPtr != whead[wcontroller._Sensors[i]._ID]) && (wnumMeanPts <= 499))
                        {
                            wrunningMeanX += wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr];
                            wrunningMeanY += wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr];
                            wrunningMeanZ += wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr];
                            wnumMeanPts++;
                            wheadPtr--;
                            if (wheadPtr < 0)
                                wheadPtr = 499;
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
                            wheadPtr = 499;
                        //compute values per second




                        while ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] > 0) && (wheadPtr != whead[wcontroller._Sensors[i]._ID]))
                        {

                            if (((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] - currentUnixTime) >= 0) && ((wtimeData[wcontroller._Sensors[i]._ID, wheadPtr] - currentUnixTime) <= 1000))
                            {

                                if ((wprevX[wcontroller._Sensors[i]._ID] > 0) && (wprevY[wcontroller._Sensors[i]._ID] > 0) && (wprevZ[wcontroller._Sensors[i]._ID] > 0) && (wrawData[wcontroller._Sensors[i]._ID, 0, wheadPtr] > 0) && (wrawData[wcontroller._Sensors[i]._ID, 1, wheadPtr] > 0) && (wrawData[wcontroller._Sensors[i]._ID, 2, wheadPtr] > 0))
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


                                //current data item
                                //headPtr = head[wcontroller._Sensors[i]._ID];
                                int wprevHead = wheadPtr - 1;
                                if (wprevHead < 0)
                                    wprevHead = 499;


                                //trapezoid
                                //double a2=rawData[wcontroller._Sensors[i]._ID, 0, headPtr];
                                //double a1=rawData[wcontroller._Sensors[i]._ID, 0, prevHead];
                                //a2 = a2 - runningMeanX;
                                //a1 = a1 - runningMeanX;

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
                                wheadPtr = 499;
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
                else
                    master_csv_line = master_csv_line + ",,,,";
                #endregion Write CSV line for Sensewear

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
                else
                    master_csv_line = master_csv_line + ",,,,,,,,,,,,,,,,";
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
                else
                    master_csv_line = master_csv_line + ",,,,,,,,";
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
                else
                    master_csv_line = master_csv_line + ",";
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
                else
                    master_csv_line = master_csv_line + ",,,,,";
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
                else
                    master_csv_line = master_csv_line + ",,,,";
                #endregion Write CSV line for GPS


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
                }
            }

            masterCSV.Flush();
            masterCSV.Close();
            for (int i = 0; (i < actigraphCSV.Length); i++)
                actigraphCSV[i].Close();
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
    }
}