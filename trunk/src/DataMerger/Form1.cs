using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Threading;
using System.IO;
using HousenCS.MITes;
using System.Collections;
using System.Text.RegularExpressions;

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
                    string[] file = Directory.GetDirectories(this.textBox1.Text);
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

                    this.progressForm.AppendLog("Older MITes CSVs .....................Deleting\r\n");
                    file = Directory.GetFileSystemEntries(this.textBox1.Text, "*MITes*.csv");
                    foreach (string filename in file)
                        File.Delete(filename);

                    //File.Copy("SensorData.xml", this.textBox1.Text + "\\SensorData.xml",true);
                    //this.progressForm.AppendLog("SensorData Locations .....................Fixing\r\n");

                    //annotation files   
                    if (File.Exists(this.textBox1.Text + "\\AnnotationIntervals.xml"))
                        this.progressForm.AppendLog("Annotation File .....................Found\r\n");
                    else
                        throw new Exception("Annotation File ....................Not Found\r\n");

                    if (File.Exists(this.textBox1.Text + "\\ActivityLabelsRealtime.xml"))
                        this.progressForm.AppendLog("Activity Labels File .....................Found\r\n");
                    else
                        throw new Exception("Activity Labels File ....................Not Found");

                    //sensewear
                    file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-sensewear*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Sensewear File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Sensewear File ..................... Not Found\r\n");
                    else
                        throw new Exception("Sensewear naming problem. Too many sensewear files.");


                    //actigraph
                    file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-actigraph*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("1 Actigraph File .....................Found\r\n");
                    else if (file.Length == 2)
                        this.progressForm.AppendLog("2 Actigraph Files .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Actigraph File ..................... Not Found\r\n");
                    //else
                    //    throw new Exception("Actigraph naming problem. Too many actigraph files.");

                    //oxycon
                    if (File.Exists(this.textBox1.Text + "\\OxyconSyncronizationTime.txt"))
                    {
                        this.progressForm.AppendLog("Oxycon Synchronization File .....................Found\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-oxycon.dat");
                        if (file.Length == 1)
                            this.progressForm.AppendLog("Oxycon PC File .....................Found\r\n");
                        else if (file.Length == 0)
                            this.progressForm.AppendLog("Oxycon PC File .....................Not Found\r\n");
                        else
                            throw new Exception("Oxycon PC naming problem. Too many Oxycon PC files.");

                        file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-flashcard.dat");
                        if (file.Length == 1)
                            this.progressForm.AppendLog("Oxycon Flash File .....................Found\r\n");
                        else if (file.Length == 0)
                        {
                            file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-flash.dat");
                            if (file.Length == 1)
                            {
                                this.progressForm.AppendLog("Oxycon Flash.dat wrong name .....................Renaming\r\n");
                                File.Copy(file[0], file[0].Replace("-flash.dat", "-flashcard.dat"));
                            }
                            else
                                this.progressForm.AppendLog("Oxycon Flash file not found.... manual inspection needed");
                        }
                        else
                            throw new Exception("Oxycon Flash naming problem. Too many Oxycon Flash files.");

                    }
                    else
                        this.progressForm.AppendLog("Oxycon Synchronization File ....................Not Found");


                    //omron

                    file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-omron.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Omron File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Omron File ..................... Not Found\r\n");
                    else
                        throw new Exception("Omron naming problem. Too many Omron files.");

                    //zephyr

                    file = Directory.GetFileSystemEntries(this.textBox1.Text, "*-zephyr*.csv");
                    if (file.Length == 1)
                        this.progressForm.AppendLog("Zephyr File .....................Found\r\n");
                    else if (file.Length == 0)
                        this.progressForm.AppendLog("Zephyr File ..................... Not Found\r\n");
                    else
                        throw new Exception("Zephyr naming problem. Too many Omron files.");

                    //MITes

                    //configuration files
                    if (File.Exists(this.textBox1.Text + "\\Configuration.xml"))
                        this.progressForm.AppendLog("Configuration.xml File .....................Found\r\n");
                    else
                        throw new Exception("Configuration.xml File ....................Not Found");

                    if (File.Exists(this.textBox1.Text + "\\SensorData.xml"))
                        this.progressForm.AppendLog("SensorData.xml File .....................Found\r\n");
                    else
                        throw new Exception("SensorData.xml File ....................Not Found");

                    if (File.Exists(this.textBox1.Text + "\\SensorData.xml"))
                        this.progressForm.AppendLog("SensorData.xml File .....................Found\r\n");
                    else
                        throw new Exception("SensorData.xml File ....................Not Found");

                    if (Directory.Exists(this.textBox1.Text + "\\data\\raw\\PLFormat"))
                        this.progressForm.AppendLog("PLFormat Data Directory .....................Found\r\n");
                    else //Attempt to Fix
                    {
                        this.progressForm.AppendLog("Non PLFormat Data Directory .....................Fixing\r\n");
                        file = Directory.GetFileSystemEntries(this.textBox1.Text + "\\data\\raw", "*.PLFormat");
                        //MITesAccelBytes.2008-6-12-13-42-12-671
                        if (file.Length == 1)
                        {

                            string timestamp = file[0].Substring(file[0].IndexOf("MITesAccelBytes.") + 16);
                            timestamp = timestamp.Substring(0, timestamp.IndexOf(".PLFormat"));
                            string[] times = timestamp.Split('-');
                            string date = times[0] + "-" + Convert.ToInt32(times[1]).ToString("00") + "-" + Convert.ToInt32(times[2]).ToString("00");
                            string hour = Convert.ToInt32(times[3]).ToString();

                            Directory.CreateDirectory(this.textBox1.Text + "\\data\\raw\\PLFormat\\" + date);
                            Directory.CreateDirectory(this.textBox1.Text + "\\data\\raw\\PLFormat\\" + date + "\\" + hour);
                            File.Copy(file[0], this.textBox1.Text + "\\data\\raw\\PLFormat\\" + date + "\\" + hour + "\\" + file[0].Substring(file[0].IndexOf("MITesAccelBytes.")));
                        }
                        else
                            throw new Exception("Old Format: More than 1 file ....................manual fix needed");
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
                MessageBox.Show("Error: Format error in the CSV files " + e.Message);
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


        public static string CSVProgress = "";
        public static void toCSV(string aDataDirectory, string masterDirectory, int maxControllers, string[] filter)
        {

            double previousUnixTime = -1;

            /**** MITes,wockets Variables ****/

            //Variables that average raw values
            int[] averageX;
            int[] averageY;
            int[] averageZ;
            int[] averageRawX;
            int[] averageRawY;
            int[] averageRawZ;

            //variables for older activity count calculation
            int[] prevX;
            int[] prevY;
            int[] prevZ;
            int[] acCounters;

            //Variables to store raw data,running mean and areas under curve
            int[, ,] rawData; //channel,axis ->data            
            long[,] timeData; //channel ->timestamp
            int[,] AUC;
            double[] VMAG;
            int[] head; //channel ->pointer to the head (circular)
            double[] RMX;
            double[] RMY;
            double[] RMZ;
            int[] RMSize;
            int[] RMCount;


            //Size of the moving average
            int MEAN_SIZE = 5000;


            //CSV files that store data                    
            TextWriter[] activityCountCSVs; //old activity count files
            TextWriter[] aucCSVs; //AUC files
            TextWriter[] vmagCSVs; //AUC files
            TextWriter[] rmCSVs; //Running mean files
            TextWriter[] samplingCSVs; //Sample Rate CSV       
            TextWriter[] averagedRaw;  //Raw signal CSV
            TextWriter masterCSV;      //Master CSV
            TextWriter hrCSV;       //HR CSV

            //Actigraph
            TextWriter[] actigraphCSV;
            Hashtable[] actigraphData;


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
            string sensewear_csv_header = "UnixTimeStamp,TimeStamp,SensewearSR,Sensewear_AVTranAcc,Senserwear_AVLongAcc,Sensewear_AVForAcc";
            string zephyr_csv_header = "UnixTimeStamp,TimeStamp,ZephyrHeart Rate Data,ZephyrECG - Amplitude Data,ZephyrECG - Noise Data,ZephyrRES - Breathing Wave Amplitude (V) Data,ZephyrRES - Respiration Rate Data,ZephyrTEM - Skin Temperature Data,ZephyrBAT - Battery Voltage (V) Data,ZephyrPOS - Posture Data,ZephyrACC - Activity Data,ZephyrACC - Peak Acceleration (g) Data,ZephyrACC - Vertical Acc Minimum (g) Data,ZephyrACC - Vertical Acc Peak (g) Data,ZephyrACC - Lateral Acc Minimum (g) Data,ZephyrACC - Lateral Acc Peak (g) Data,ZephyrACC - Sagittal Acc Minimum (g) Data,ZephyrACC - Sagittal Acc Peak (g)";
            string oxycon_csv_header = "UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2,OxyconVO2kg,OxyconMET,OxyconEE,OxyconRER";
            string omron_csv_header = "UnixTimeStamp,TimeStamp,Steps";
            string master_csv_header = "UnixTimeStamp,TimeStamp";

            //files found

            bool sensewearFound = false;
            bool zephyrFound = false;
            bool oxyconFound = false;
            bool omronFound = false;








            #region Read Omron data
            string[] file = Directory.GetFileSystemEntries(aDataDirectory, "*-omron.csv");
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
            file = Directory.GetFileSystemEntries(aDataDirectory, "*-actigraph*.csv");
            actigraphCSV = new TextWriter[file.Length];
            actigraphData = new Hashtable[file.Length];

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

                    actigraphReader.Close();
                }
            }
            catch (Exception e)
            {
                throw new Exception("Actigraphs: Parsing failed " + e.Message);
            }
            #endregion Read Actigraph data

            #region Read Zephyr data
            file = Directory.GetFileSystemEntries(aDataDirectory, "*-zephyr*.csv");

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

            if (File.Exists(aDataDirectory + "\\OxyconSyncronizationTime.txt"))
            {

                file = Directory.GetFileSystemEntries(aDataDirectory, "*-flashcard*");
                if (file.Length == 1)
                {

                    TextReader oxyconOriginTR = new StreamReader(aDataDirectory + "\\OxyconSyncronizationTime.txt");
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
                    file = Directory.GetFileSystemEntries(aDataDirectory, "*-oxycon.dat");
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
                    file = Directory.GetFileSystemEntries(aDataDirectory, "*-flashcard.dat");
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
                    file = Directory.GetFileSystemEntries(aDataDirectory, "*-flashcard.dat");
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


                                        oxyconTime = oxyconOriginTime.AddHours(Convert.ToDouble(timeTokens[0]));
                                        oxyconTime = oxyconTime.AddMinutes(Convert.ToDouble(timeTokens[1]));
                                        oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[2]));


                                    }


                                    oxyconTime = oxyconTime.AddSeconds(-1.0 * oxyconAdjustment);

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
                else if (file.Length == 2)
                {

                    TextReader oxyconOriginTR = new StreamReader(aDataDirectory + "\\OxyconSyncronizationTime.txt");
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
                    file = Directory.GetFileSystemEntries(aDataDirectory, "*-flashcard.1.dat");
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


                                        oxyconTime = oxyconOriginTime.AddHours(Convert.ToDouble(timeTokens[0]));
                                        oxyconTime = oxyconTime.AddMinutes(Convert.ToDouble(timeTokens[1]));
                                        oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[2]));


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
                    file = Directory.GetFileSystemEntries(aDataDirectory, "*-flashcard.2.dat");
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


                                        oxyconTime = oxyconOriginTime.AddHours(Convert.ToDouble(timeTokens[0]));
                                        oxyconTime = oxyconTime.AddMinutes(Convert.ToDouble(timeTokens[1]));
                                        oxyconTime = oxyconTime.AddSeconds(Convert.ToDouble(timeTokens[2]));


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
            file = Directory.GetFileSystemEntries(aDataDirectory, "*-sensewear*.csv");
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
                        sensewearUnixTime = Convert.ToInt64(tokens[0].Trim()) - (8 * 60 * 60 * 1000);//UnixTime.GetUnixTime(sensewearTime);
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

            AXML.Annotation aannotation = null;
            SXML.SensorAnnotation sannotation = null;
            //GeneralConfiguration configuration = null;
            try
            {
                //configuration = new ConfigurationReader(aDataDirectory).parse();
                AXML.Reader reader = new AXML.Reader(masterDirectory, aDataDirectory, "AnnotationIntervals.xml");
                aannotation = reader.parse();
                aannotation.RemoveData(filter);
                aannotation.DataDirectory = aDataDirectory;
                SXML.Reader sreader = new SXML.Reader(masterDirectory, aDataDirectory);
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

            try
            {
                masterCSV = new StreamWriter(aDataDirectory + "\\MITesSummaryData.csv");
                hrCSV = new StreamWriter(aDataDirectory + "\\HeartRate_MITes.csv");
                for (int i = 0; (i < actigraphCSV.Length); i++)
                    actigraphCSV[i] = new StreamWriter(aDataDirectory + "\\Actigraph" + (i + 1) + ".csv");
                if (sensewearFound)
                    sensewearCSV = new StreamWriter(aDataDirectory + "\\Sensewear.csv");
                if (zephyrFound)
                    zephyrCSV = new StreamWriter(aDataDirectory + "\\Zephyr.csv");
                if (oxyconFound)
                    oxyconCSV = new StreamWriter(aDataDirectory + "\\Oxycon.csv");
                if (omronFound)
                    omronCSV = new StreamWriter(aDataDirectory + "\\Omron.csv");
            }
            catch (Exception e)
            {
                throw new Exception("Unable to open CSV: cannot open file " + e.Message);
            }

            foreach (AXML.Category category in aannotation.Categories)
                master_csv_header += "," + category.Name;


            foreach (SXML.Sensor sensor in sannotation.Sensors)
            {
                int sensor_id = Convert.ToInt32(sensor.ID);
                string location = sensor.Location.Replace(' ', '-');
                if (sensor_id > 0) //exclude HR
                {
                    activityCountCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\MITes_" + sensor_id.ToString("00") + "_SAD_" + location + ".csv");
                    activityCountCSVs[sensor_id].WriteLine(csv_line1);
                    rmCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\MITes_" + sensor_id.ToString("00") + "_RM_" + location + ".csv");
                    rmCSVs[sensor_id].WriteLine(csv_line1);
                    aucCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\MITes_" + sensor_id.ToString("00") + "_AUC_" + location + ".csv");
                    aucCSVs[sensor_id].WriteLine(csv_line1);
                    vmagCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\MITes_" + sensor_id.ToString("00") + "_VMAG_" + location + ".csv");
                    vmagCSVs[sensor_id].WriteLine(csv_line6);
                    averagedRaw[sensor_id] = new StreamWriter(aDataDirectory + "\\MITes_" + sensor_id.ToString("00") + "_1s-RawMean_" + location + ".csv");
                    averagedRaw[sensor_id].WriteLine(csv_line1);
                    samplingCSVs[sensor_id] = new StreamWriter(aDataDirectory + "\\MITes_" + sensor_id.ToString("00") + "_SampleRate_" + location + ".csv");
                    samplingCSVs[sensor_id].WriteLine(csv_line2);
                    master_csv_header += ",MITes" + sensor_id.ToString("00") + "_SR," + "MITes" + sensor_id.ToString("00") + "_AVRaw_X," +
                        "MITes" + sensor_id.ToString("00") + "_AVRaw_Y," + "MITes" + sensor_id.ToString("00") + "_AVRaw_Z," + "MITes" + sensor_id.ToString("00") + "_SAD_X," +
                        "MITes" + sensor_id.ToString("00") + "_SAD_Y," + "MITes" + sensor_id.ToString("00") + "_SAD_Z," + "MITes" + sensor_id.ToString("00") + "_AUC_X," +
                        "MITes" + sensor_id.ToString("00") + "_AUC_Y," + "MITes" + sensor_id.ToString("00") + "_AUC_Z," + "MITes" + sensor_id.ToString("00") + "_AUC_XYZ," +
                        "MITes" + sensor_id.ToString("00") + "_RM_X," + "MITes" + sensor_id.ToString("00") + "_RM_Y," + "MITes" + sensor_id.ToString("00") + "_RM_Z," +
                        "MITes" + sensor_id.ToString("00") + "_RM_SIZE," + "MITes" + sensor_id.ToString("00") + "_VMAG";

                }
            }

            master_csv_header += ",HR,";
            for (int i = 0; (i < actigraphData.Length); i++)
            {
                master_csv_header += "Actigraph" + (i + 1) + ",";
                actigraphCSV[i].WriteLine(actigraph_csv_header);
            }
            master_csv_header += "SensewearSR,Sensewear_AVTranAcc,Senserwear_AVLongAcc,Sensewear_AVForAcc";
            master_csv_header += ",ZephyrHeart Rate Data,ZephyrECG - Amplitude Data,ZephyrECG - Noise Data,ZephyrRES - Breathing Wave Amplitude (V) Data,ZephyrRES - Respiration Rate Data,ZephyrTEM - Skin Temperature Data,ZephyrBAT - Battery Voltage (V) Data,ZephyrPOS - Posture Data,ZephyrACC - Activity Data,ZephyrACC - Peak Acceleration (g) Data,ZephyrACC - Vertical Acc Minimum (g) Data,ZephyrACC - Vertical Acc Peak (g) Data,ZephyrACC - Lateral Acc Minimum (g) Data,ZephyrACC - Lateral Acc Peak (g) Data,ZephyrACC - Sagittal Acc Minimum (g) Data,ZephyrACC - Sagittal Acc Peak (g)";
            master_csv_header += ",OxyconHR,OxyconBF,OxyconVE,OxyconVO2,OxyconVO2kg,OxyconMET,OxyconEE,OxyconRER";//OxyconRER,Oxyconttot,Oxycontex";
            master_csv_header += ",OmronSteps";
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

            int channel = 0, x = 0, y = 0, z = 0;
            double unixtimestamp = 0.0;
            int activityIndex = 0;
            AXML.AnnotatedRecord annotatedRecord = ((AXML.AnnotatedRecord)aannotation.Data[activityIndex]);
            string current_activity = "";
            for (int j = 0; (j < annotatedRecord.Labels.Count); j++)
            {
                if (j == annotatedRecord.Labels.Count - 1)
                    current_activity += "";
                else
                    current_activity += ",";
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
            RMCount = new int[sannotation.MaximumSensorID + 1];

            for (int i = 0; (i < head.Length); i++)
            {
                head[i] = 0;
                RMX[i] = 0;
                RMY[i] = 0;
                RMZ[i] = 0;
                RMSize[i] = 0;
                RMCount[i] = 0;
                VMAG[i] = 0;
                for (int j = 0; (j < 3); j++)
                    AUC[i, j] = 0;
            }

            //Initialize MITes Decoders + configuration
            MITesDecoder aMITesDecoder = new MITesDecoder();
            MITesHRAnalyzer aMITesHRAnalyzer = new MITesHRAnalyzer(aMITesDecoder);
            MITesLoggerReader aMITesLoggerReader = new MITesLoggerReader(aMITesDecoder, aDataDirectory);
            //Extractor.Initialize(aMITesDecoder, aDataDirectory, aannotation, sannotation, configuration);
            bool isData = aMITesLoggerReader.GetSensorData(10);
            //Decode MITes Data            
            //TextWriter tww = new StreamWriter("sequences1.csv");
            long refUnix = -1;
            long first0TS = -1;
            int lastChannel = -1;
            do
            {

                channel = aMITesDecoder.GetSomeMITesData()[0].channel;
                x = aMITesDecoder.GetSomeMITesData()[0].x;
                y = aMITesDecoder.GetSomeMITesData()[0].y;
                z = aMITesDecoder.GetSomeMITesData()[0].z; 
                unixtimestamp = aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp;

                rawData[channel, 0, head[channel]] = x;
                rawData[channel, 1, head[channel]] = y;
                rawData[channel, 2, head[channel]] = z;
                timeData[channel, head[channel]] = (long)unixtimestamp;


                DateTime mitesTime = new DateTime();
                UnixTime.GetDateTime((long)unixtimestamp, out mitesTime);


                if (CSVProgress == "")
                    CSVProgress = "Synchronizing " + mitesTime.ToLongDateString() + " " + mitesTime.ToLongTimeString();

                //Heart Rate Data
                int hr = aMITesHRAnalyzer.UpdateOffline();
                if (hr > 0)
                {
                    sumHR += hr;
                    hrCount++;
                }

                double lastTimeStamp = unixtimestamp;
                if (unixtimestamp > annotatedRecord.EndUnix)
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


                if ((lastTimeStamp >= annotatedRecord.StartUnix) &&
                     (lastTimeStamp <= annotatedRecord.EndUnix))
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


                //Calculate Running Means
                double runningMeanX = 0;
                double runningMeanY = 0;
                double runningMeanZ = 0;
                int numMeanPts = 0;
                int headPtr = head[channel];

                while ((timeData[channel, headPtr] > 0) && ((unixtimestamp - timeData[channel, headPtr]) <= MEAN_SIZE) && (numMeanPts <= 499))
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
                RMX[channel] += runningMeanX;
                RMY[channel] += runningMeanY;
                RMZ[channel] += runningMeanZ;
                RMSize[channel] += numMeanPts;
                RMCount[channel] = RMCount[channel] + 1;


                //Calculate MITes Raw Values
                if (channel <= sannotation.MaximumSensorID) //if junk comes ignore it
                {
                    if ((prevX[channel] > 0) && (prevY[channel] > 0) && (prevZ[channel] > 0) && (x > 0) && (y > 0) && (z > 0))
                    {
                        averageX[channel] = averageX[channel] + Math.Abs(prevX[channel] - x);
                        averageRawX[channel] = averageRawX[channel] + x;
                        averageY[channel] = averageY[channel] + Math.Abs(prevY[channel] - y);
                        averageRawY[channel] = averageRawY[channel] + y;
                        averageZ[channel] = averageZ[channel] + Math.Abs(prevZ[channel] - z);
                        averageRawZ[channel] = averageRawZ[channel] + z;
                        acCounters[channel] = acCounters[channel] + 1;
                    }

                    prevX[channel] = x;
                    prevY[channel] = y;
                    prevZ[channel] = z;


                    //current data item
                    headPtr = head[channel];
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

                        AUC[channel, 0] = AUC[channel, 0] + (int)Math.Abs((x - runningMeanX));
                        AUC[channel, 1] = AUC[channel, 1] + (int)Math.Abs((y - runningMeanY));
                        AUC[channel, 2] = AUC[channel, 2] + (int)Math.Abs((z - runningMeanZ));
                        VMAG[channel] = VMAG[channel] + Math.Sqrt(Math.Pow((double)(x - runningMeanX), 2.0) + Math.Pow((double)(y - runningMeanY), 2.0) + Math.Pow((double)(z - runningMeanZ), 2.0));
                    }
                }



                head[channel] = (head[channel] + 1) % 500;


                #region Store data every second

                if (previousUnixTime < 0)
                    previousUnixTime = unixtimestamp;
                else if ((unixtimestamp - previousUnixTime) >= 1000) //output data
                {
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
                    #endregion Initialize CSV lines

                    DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
                    DateTime now = new DateTime();
                    string timeKey = "";
                    TimeSpan diff;
                    string timestamp = "";

                    //Check for missing MITes data
                    while ((unixtimestamp - previousUnixTime) >= 2000)
                    {

                        UnixTime.GetDateTime((long)(previousUnixTime + 1000), out now);
                        timeKey = now.Year + "-" + now.Month + "-" + now.Day + "-" + now.Hour + "-" + now.Minute + "-" + now.Second;
                        diff = now.Subtract(origin);
                        timestamp = diff.TotalMilliseconds + "," + now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                        previousUnixTime = previousUnixTime + 1000;

                        if (CSVProgress == "")
                            CSVProgress = "Synchronizing " + now.ToLongDateString() + " " + now.ToLongTimeString();

                        #region Update current activity
                        if (previousUnixTime > annotatedRecord.EndUnix)
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

                        if ((previousUnixTime >= annotatedRecord.StartUnix) &&
                             (previousUnixTime <= annotatedRecord.EndUnix))
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
                        #endregion Update current activity


                        //Set the time stamp
                        master_csv_line = timestamp;
                        hr_csv_line = timestamp;
                        for (int i = 0; (i < actigraphData.Length); i++)
                            actigraph_csv_line[i] = timestamp;
                        sensewear_csv_line = timestamp;
                        zephyr_csv_line = timestamp;
                        oxycon_csv_line = timestamp;
                        omron_csv_line = timestamp;
                        master_csv_line += "," + current_activity;

                        //attempt to write everything except MITes
                        foreach (SXML.Sensor sensor in sannotation.Sensors)
                        {
                            csv_line1 = timestamp;
                            csv_line2 = timestamp;
                            csv_line3 = timestamp;
                            csv_line4 = timestamp;
                            csv_line5 = timestamp;
                            csv_line6 = timestamp;

                            int sensor_id = Convert.ToInt32(sensor.ID);
                            if (sensor_id > 0) //No HR
                            {
                                csv_line1 += ",,,,";
                                csv_line3 += ",,,,";
                                csv_line2 += ",0";
                                csv_line4 += ",,,,";
                                csv_line5 += ",,,,,";
                                csv_line6 += ",";
                                master_csv_line += ",0,,,,,,,,,,,,,,,";

                                activityCountCSVs[sensor_id].WriteLine(csv_line1);
                                samplingCSVs[sensor_id].WriteLine(csv_line2);
                                averagedRaw[sensor_id].WriteLine(csv_line3);
                                rmCSVs[sensor_id].WriteLine(csv_line4);
                                aucCSVs[sensor_id].WriteLine(csv_line5);
                                aucCSVs[sensor_id].WriteLine(csv_line6);
                            }
                            else
                                hrCSV.WriteLine(hr_csv_line + ",");



                            averageX[sensor_id] = 0;
                            averageY[sensor_id] = 0;
                            averageZ[sensor_id] = 0;
                            averageRawX[sensor_id] = 0;
                            averageRawY[sensor_id] = 0;
                            averageRawZ[sensor_id] = 0;
                            prevX[sensor_id] = 0;
                            prevY[sensor_id] = 0;
                            prevY[sensor_id] = 0;
                            acCounters[sensor_id] = 0;
                            RMX[sensor_id] = 0;
                            RMY[sensor_id] = 0;
                            RMZ[sensor_id] = 0;
                            RMSize[sensor_id] = 0;
                            RMCount[sensor_id] = 0;
                            VMAG[sensor_id] = 0;
                            for (int j = 0; (j < 3); j++)
                                AUC[sensor_id, j] = 0;
                        }
                        master_csv_line = master_csv_line + ",,";

                        #region Write CSV lines for Actigraphs
                        for (int i = 0; (i < actigraphData.Length); i++)
                        {
                            if (actigraphData[i].ContainsKey(timeKey) == false)
                            {
                                actigraphCSV[i].WriteLine(actigraph_csv_line[i] + ",");
                                master_csv_line = master_csv_line + ",";
                            }
                            else
                            {

                                actigraphCSV[i].WriteLine(actigraph_csv_line[i] + "," + actigraphData[i][timeKey]);
                                master_csv_line = master_csv_line + actigraphData[i][timeKey] + ",";
                            }
                        }
                        #endregion Write CSV lines for Actigraphs

                        #region Write CSV line for Sensewear
                        if ((sensewearFound) && (sensewearCSV != null))
                        {
                            if (SSR.ContainsKey(timeKey))
                            {
                                sensewearCSV.WriteLine(sensewear_csv_line + "," + (int)SSR[timeKey] + "," + (double)STrans[timeKey] +
                                    "," + (double)SLong[timeKey] + "," + (double)SAcc[timeKey]);
                                master_csv_line = master_csv_line + (int)SSR[timeKey] + "," + (double)STrans[timeKey] +
                                    "," + (double)SLong[timeKey] + "," + (double)SAcc[timeKey];
                            }
                            else
                            {
                                sensewearCSV.WriteLine(sensewear_csv_line + ",,,,");
                                master_csv_line = master_csv_line + ",,,";
                            }
                        }
                        else
                            master_csv_line = master_csv_line + ",,,";
                        #endregion Write CSV line for Sensewear

                        #region Write CSV line for Zephyr
                        if ((zephyrFound) && (zephyrCSV != null))
                        {
                            if (zephyrData.ContainsKey(timeKey))
                            {
                                zephyrCSV.WriteLine(zephyr_csv_line + "," + ((string)zephyrData[timeKey]));
                                master_csv_line = master_csv_line + "," + ((string)zephyrData[timeKey]);
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
                            if (oxyconData.ContainsKey(timeKey))
                            {
                                oxyconCSV.WriteLine(oxycon_csv_line + "," + ((string)oxyconData[timeKey]));
                                master_csv_line = master_csv_line + "," + ((string)oxyconData[timeKey]);
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
                            if (omronData.Contains(timeKey))
                            {
                                omronCSV.WriteLine(omron_csv_line + "," + ((int)omronData[timeKey]));
                                master_csv_line = master_csv_line + "," + ((int)omronData[timeKey]);
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

                        #region Write master CSV line
                        masterCSV.WriteLine(master_csv_line);
                        #endregion Write master CSV line

                        hrCount = 0;
                        sumHR = 0;
                    }


                    UnixTime.GetDateTime((long)unixtimestamp, out now);
                    timeKey = now.Year + "-" + now.Month + "-" + now.Day + "-" + now.Hour + "-" + now.Minute + "-" + now.Second;
                    diff = now.Subtract(origin);
                    timestamp = diff.TotalMilliseconds + "," + now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                    previousUnixTime = unixtimestamp;

                    #region Set CSV lines timestamp
                    master_csv_line = timestamp;
                    hr_csv_line = timestamp;
                    for (int i = 0; (i < actigraphData.Length); i++)
                        actigraph_csv_line[i] = timestamp;
                    sensewear_csv_line = timestamp;
                    zephyr_csv_line = timestamp;
                    oxycon_csv_line = timestamp;
                    omron_csv_line = timestamp;
                    master_csv_line += "," + current_activity;
                    #endregion Set CSV lines timestamp

                    #region Write CSV line for MITes
                    foreach (SXML.Sensor sensor in sannotation.Sensors)
                    {
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

                                csv_line4 += "," + ((double)(RMX[sensor_id] / RMCount[sensor_id])).ToString("00.00") + ",";
                                csv_line4 += ((double)(RMY[sensor_id] / RMCount[sensor_id])).ToString("00.00") + ",";
                                csv_line4 += ((double)(RMZ[sensor_id] / RMCount[sensor_id])).ToString("00.00");

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

                                master_csv_line += ((double)(RMX[sensor_id] / RMCount[sensor_id])).ToString("00.00") + ",";
                                master_csv_line += ((double)(RMY[sensor_id] / RMCount[sensor_id])).ToString("00.00") + ",";
                                master_csv_line += ((double)(RMZ[sensor_id] / RMCount[sensor_id])).ToString("00.00") + ",";
                                master_csv_line += ((double)(RMSize[sensor_id] / RMCount[sensor_id])).ToString("00.00") + ",";
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

                        averageX[sensor_id] = 0;
                        averageY[sensor_id] = 0;
                        averageZ[sensor_id] = 0;
                        averageRawX[sensor_id] = 0;
                        averageRawY[sensor_id] = 0;
                        averageRawZ[sensor_id] = 0;
                        prevX[sensor_id] = 0;
                        prevY[sensor_id] = 0;
                        prevY[sensor_id] = 0;
                        acCounters[sensor_id] = 0;
                        RMX[sensor_id] = 0;
                        RMY[sensor_id] = 0;
                        RMZ[sensor_id] = 0;
                        RMSize[sensor_id] = 0;
                        RMCount[sensor_id] = 0;
                        VMAG[sensor_id] = 0;
                        for (int j = 0; (j < 3); j++)
                            AUC[sensor_id, j] = 0;

                    }
                    #endregion Write CSV line for MITes

                    #region Write CSV line for MITes HR
                    if (hrCount > 0)
                    {
                        hrCSV.WriteLine(hr_csv_line + "," + (int)(sumHR / hrCount));
                        master_csv_line = master_csv_line + "," + (int)(sumHR / hrCount) + ",";
                    }
                    else
                    {
                        hrCSV.WriteLine(hr_csv_line + ",");
                        master_csv_line = master_csv_line + ",,";
                    }
                    #endregion Write CSV line for MITes HR

                    #region Write CSV lines for Actigraphs
                    for (int i = 0; (i < actigraphData.Length); i++)
                    {
                        if (actigraphData[i].ContainsKey(timeKey) == false)
                        {
                            actigraphCSV[i].WriteLine(actigraph_csv_line[i] + ",");
                            master_csv_line = master_csv_line + ",";
                        }
                        else
                        {

                            actigraphCSV[i].WriteLine(actigraph_csv_line[i] + "," + actigraphData[i][timeKey]);
                            master_csv_line = master_csv_line + actigraphData[i][timeKey] + ",";
                        }
                    }
                    #endregion Write CSV lines for Actigraphs

                    #region Write CSV line for Sensewear
                    if ((sensewearFound) && (sensewearCSV != null))
                    {
                        if (SSR.ContainsKey(timeKey))
                        {
                            sensewearCSV.WriteLine(sensewear_csv_line + "," + (int)SSR[timeKey] + "," + (double)STrans[timeKey] +
                                "," + (double)SLong[timeKey] + "," + (double)SAcc[timeKey]);
                            master_csv_line = master_csv_line + (int)SSR[timeKey] + "," + (double)STrans[timeKey] +
                                "," + (double)SLong[timeKey] + "," + (double)SAcc[timeKey];
                        }
                        else
                        {
                            sensewearCSV.WriteLine(sensewear_csv_line + ",,,,");
                            master_csv_line = master_csv_line + ",,,";
                        }
                    }
                    else
                        master_csv_line = master_csv_line + ",,,";
                    #endregion Write CSV line for Sensewear

                    #region Write CSV line for Zephyr
                    if ((zephyrFound) && (zephyrCSV != null))
                    {
                        if (zephyrData.ContainsKey(timeKey))
                        {
                            zephyrCSV.WriteLine(zephyr_csv_line + "," + ((string)zephyrData[timeKey]));
                            master_csv_line = master_csv_line + "," + ((string)zephyrData[timeKey]);
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
                        if (oxyconData.ContainsKey(timeKey))
                        {
                            oxyconCSV.WriteLine(oxycon_csv_line + "," + ((string)oxyconData[timeKey]));
                            master_csv_line = master_csv_line + "," + ((string)oxyconData[timeKey]);



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
                        if (omronData.Contains(timeKey))
                        {
                            omronCSV.WriteLine(omron_csv_line + "," + ((int)omronData[timeKey]));
                            master_csv_line = master_csv_line + "," + ((int)omronData[timeKey]);
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

                    #region Write master CSV line
                    masterCSV.WriteLine(master_csv_line);
                    #endregion Write master CSV line

                    hrCount = 0;
                    sumHR = 0;
                }

                #endregion Store data every second


            } while (isData = aMITesLoggerReader.GetSensorData(10));
            //tww.Flush();
            //tww.Close();
            //Completed Synchronizing - Flush and close files
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

            masterCSV.Flush();
            hrCSV.Flush();
            masterCSV.Close();
            hrCSV.Close();
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
        }














    }
}