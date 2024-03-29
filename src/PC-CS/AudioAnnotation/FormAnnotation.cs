using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

using System.Reflection;
using System.Globalization;

using Wockets.Data.Annotation;
using WMPLib;





namespace AudioAnnotation
{

    public partial class FormAnnotation : Form
    {


        #region  Declare variables

        //Audio Files
        //private DirectoryInfo folder;
        private FileInfo[] files = null;
        private FileInfo[] files_wav = null;
        private FileInfo file_session = null;
        private string NO_AUDIO_ROW_STR = "-----";
        private string file_offset = "audio_offset.txt";
        private TimeSpan AudioOffset = new TimeSpan(0, 0, 0);
        private Int16 IsOffsetApplied = 0;

        //DataGridView
        private struct COLUMN_INDEX
        {
            public int ID;
            public int Lock;
            public int category_label, StartEnd;
            public int Time, Time_Label, Notes;

            public int Status, StartID, EndID;
            public int Combo_Type, Combo_Label;
            
            public int TimeMS;
            public int TimeLastWrite;
            public int TimeDuration;

            public COLUMN_INDEX(int category)
            {
                ID = 0;
                Time = 7;
                Time_Label = 8;
                Notes = 9;
                
                TimeLastWrite = 20;
                TimeDuration = 21;
                TimeMS = 22;

                if (category == 1)
                {
                    Lock = 1;
                    category_label = 2;
                    StartEnd = 3;

                    Status = 10;
                    StartID = 11;
                    EndID = 12;

                    Combo_Type = 13;
                    Combo_Label = 14;
                    
                }
                else
                {
                    Lock = 4;
                    category_label = 5;
                    StartEnd = 6;

                    Status = 15;
                    StartID = 16;
                    EndID = 17;

                    Combo_Type = 18;
                    Combo_Label = 19;
                }

            }

            public void SetValues(int category)
            {
                ID = 0;
                Time = 7;
                Time_Label = 8;
                Notes = 9;

                TimeLastWrite = 20;
                TimeDuration = 21;
                TimeMS = 22;

                if (category == 1)
                {
                    Lock = 1;
                    category_label = 2;
                    StartEnd = 3;

                    Status = 10;
                    StartID = 11;
                    EndID = 12;

                    Combo_Type = 13;
                    Combo_Label = 14;
                }
                else
                {
                    Lock = 4;
                    category_label = 5;
                    StartEnd = 6;

                    Status = 15;
                    StartID = 16;
                    EndID = 17;

                    Combo_Type = 18;
                    Combo_Label = 19;
                }

            }
        }

        private COLUMN_INDEX C1 = new COLUMN_INDEX(1);
        private COLUMN_INDEX C2 = new COLUMN_INDEX(2);
        private COLUMN_INDEX CINDEX = new COLUMN_INDEX(1);


        private struct COLUMN_STATUS
        {
            public int column, row;
            public string tlabel, status_tlabel;
            public string start_label, end_label;
            public int open_row, close_row;
            public bool is_unlocked, is_label_open;

            public COLUMN_STATUS(int c, int r, string tl, string sl, string start, string end,
                                 int or, int cr, bool lu, bool lo)
            {
                column = c;
                row = r;


                tlabel = tl;
                status_tlabel = sl;
                start_label = start;
                end_label = end;

                open_row = or;
                close_row = cr;

                is_unlocked = lu;
                is_label_open = lo;

            }


            public COLUMN_STATUS(int c, int r)
            {
                column = c;
                row = r;

                tlabel = " ";
                status_tlabel = " ";
                start_label = " ";
                end_label = " ";

                open_row = -1;
                close_row = -1;

                is_unlocked = false;
                is_label_open = true;

            }

        }


        private string StartDate = "";
        private string EndDate = "";

        private int is_busy = 0;
        private int nrows = 0;

        //string tlabel = " ";
        string next_tlabel = " ";
        //string status_tlabel = " ";

        private int current_row = 0;
        private int current_column = 0;

        private DataGridViewCellStyle prev_cellStyle = null;
        private DataGridViewCellStyle cur_cellStyle = null;
        DataGridViewComboBoxCell cellComboBox = null;

        private BindingList<string> list_category_name = new BindingList<string>();
        private BindingList<string> list_category_1    = new BindingList<string>();
        private BindingList<string> list_category_2    = new BindingList<string>();

        private BindingList<string> LabelsList_1 = new BindingList<string>();
        private BindingList<string> LabelsList_2 = new BindingList<string>();


        private TextWriter tw;
        private TextReader tr;

        private string DataSessionName = "";
        private string SessionFileName = "";
        private string DataSessionDir = "";

        private string DataAudioDir = "";
        private string DataOutputDir = "";

        private string Folder_session = "";
        private string Folder_annotation = "";
        private string Folder_audioannotation = "";
        private string Folder_annotator_files = "";

        private int SessionPart = 1;
        private bool SessionStarted = false;

        private bool is_data_grid_loaded = false;

        private Session XmlSession = null;
        


        private BindingList<ActivityList> CActivityList = null;


        //Time and Time Zone
        TimeZone localZone; 
        DaylightTime daylight; 

        #endregion


        #region Initialize

        public FormAnnotation()
        {
            
           
            InitializeComponent();


            //datagridview settings
            InitializeDataGridView(dataGridView1);

            button_remove.Image = Resources.Im_delete;
            button_add.Image = Resources.Im_plus;
            button_category_select.Image = Resources.Im_next;

            button_save.Image = Resources.Im_save;
            button_generate.Image = Resources.Im_gear;
            button_exit.Image = Resources.Im_stop;


            //Initialize Time and Time Zone
            localZone = TimeZone.CurrentTimeZone;
            daylight = localZone.GetDaylightChanges(DateTime.Now.Year);

        }

        private void InitializeDataGridView(DataGridView dgview)
        {

            CCategory_1.SortMode = DataGridViewColumnSortMode.NotSortable;
            CCategory_1.Sorted = false;

            CCategory_2.SortMode = DataGridViewColumnSortMode.NotSortable;
            CCategory_2.Sorted = false;


            CStartEnd_1.SortMode = DataGridViewColumnSortMode.NotSortable;
            CStartEnd_1.Sorted = false;

            CStartEnd_2.SortMode = DataGridViewColumnSortMode.NotSortable;
            CStartEnd_2.Sorted = false;


            // Next Status 1
            CStatus_1.Items.Add(" ");         // "label" value not set
            CStatus_1.Items.Add("start");     // start label begins
            CStatus_1.Items.Add("start_on");  // start label was set
            CStatus_1.Items.Add("end");       // end label ends

            // Next Status 1
            CStatus_2.Items.Add(" ");         // "label" value not set
            CStatus_2.Items.Add("start");     // start label begins
            CStatus_2.Items.Add("start_on");  // start label was set
            CStatus_2.Items.Add("end");       // end label ends


            CStatus_1.SortMode = DataGridViewColumnSortMode.NotSortable;
            CStatus_1.Sorted = false;

            CStatus_2.SortMode = DataGridViewColumnSortMode.NotSortable;
            CStatus_2.Sorted = false;

            //Time
            CTime.SortMode = DataGridViewColumnSortMode.NotSortable;
            CTimeLabel.SortMode = DataGridViewColumnSortMode.NotSortable;

            //Time duration information
            CTime_MS.SortMode = DataGridViewColumnSortMode.NotSortable;
            CTime_MS.Visible = false;

            CTime_Duration.SortMode = DataGridViewColumnSortMode.NotSortable;
            CTime_Duration.Visible = false;

            CTime_LastWritten.SortMode = DataGridViewColumnSortMode.NotSortable;
            CTime_LastWritten.Visible = false;
            



            // hide the row headers
            //dgview.RowHeadersVisible = false;
            //dgview.ColumnHeadersBorderStyle = ProperColumnHeadersBorderStyle;

            dgview.Dock = DockStyle.None;

            // Bind the DataGridView to its own Columns collection.
            dgview.AutoGenerateColumns = false;

            // data-bound
            //dgview.DataSource = dgview.Columns; 

            // Configure the DataGridView so that users can manually change 
            // only the column widths, which are set to fill mode. 
            dgview.AllowUserToAddRows = false;
            dgview.AllowUserToDeleteRows = false;
            dgview.AllowUserToResizeRows = false;
            dgview.RowHeadersWidthSizeMode =
                DataGridViewRowHeadersWidthSizeMode.DisableResizing;
            dgview.ColumnHeadersHeightSizeMode =
                DataGridViewColumnHeadersHeightSizeMode.DisableResizing;
            dgview.AutoSizeColumnsMode =
                DataGridViewAutoSizeColumnsMode.Fill;
            dgview.ScrollBars = ScrollBars.Vertical;

            // Configure the top left header cell as a reset button.
            dataGridView1.TopLeftHeaderCell.Value = "Play";
            dataGridView1.TopLeftHeaderCell.Style.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;


        }

        // Border Style
        static DataGridViewHeaderBorderStyle ProperColumnHeadersBorderStyle
        {
            get
            {
                return (SystemFonts.MessageBoxFont.Name == "Segoe UI") ?
                    DataGridViewHeaderBorderStyle.None :
                    DataGridViewHeaderBorderStyle.Raised;
            }
        }

        #endregion


        #region Load Grid Data

        //Load data to grid
        private bool LoadData()
        {

            bool is_data_loaded = false;


            try
            {
                Folder_annotation = Folder_session + "annotation\\";
                // check if anotation folder exist, if it doesn't exist, create it.
                if (Directory.Exists(Folder_annotation) == false)
                {   Directory.CreateDirectory(Folder_annotation); }

                Folder_audioannotation = Folder_annotation + "audioannotation\\";
                if (Directory.Exists(Folder_audioannotation) == false)
                { Directory.CreateDirectory(Folder_audioannotation); }

                Folder_annotator_files = Folder_audioannotation + "annotator_files\\";
                if (Directory.Exists(Folder_annotator_files) == false)
                { Directory.CreateDirectory(Folder_annotator_files); }

                // Load Session File  //string name = textBox_3.Text.Trim();
                //string name = Folder_annotator_files + "annotation_session.txt";
                string name = "annotation_session.txt";
               

                

                if (SessionDir_Exist())
                {
                    if (LoadActivityLabels())
                    {
                        if (LoadGridColumnHeaders())
                        {
                            if (name.CompareTo("") != 0)
                            {
                                if (name.Contains(".txt") == false)
                                { name = name + ".txt"; }

                                SessionFileName = name;
                                SessionFileToDataDir();

                                name = DataSessionDir + name;


                                string[] session_files = Directory.GetFiles(DataSessionDir);
                                DataSessionName = "";

                                for (int i = 0; i < session_files.Length; i++)
                                {
                                    if (name.CompareTo(session_files[i]) == 0)
                                    {
                                        int is_started = IsSessionStarted();
                                        if (is_started == 1)
                                        { DataSessionName = session_files[i]; }
                                        else if (is_started == -1)
                                        {
                                            // delete previous Xml object
                                            XmlSession = null;
                                            return false;
                                        }

                                        break;
                                    }
                                }


                                //if session name file not found, create new session
                                if (DataSessionName.CompareTo("") == 0)
                                {
                                    DataSessionName = name;

                                    //Load list
                                    if (LoadList(dataGridView1) == false)
                                    {
                                        label_play.Text = "No audio files were found. Please check the directory name.";

                                        // delete previous Xml object
                                        XmlSession = null;
                                    }
                                    else
                                    { is_data_loaded = true; }

                                }
                                else  //if session file name found, load previous session
                                {
                                    //LoadAudioFiles
                                    if (files == null)
                                    {
                                        LoadAudioFiles();
    
                                    }


                                    //If audio files were found
                                    if (files != null)
                                    {
                                        if (files.Length > 0)
                                        {
                                            StartDate = files[0].LastWriteTime.ToShortDateString();
                                            EndDate = files[files.Length - 1].LastWriteTime.ToShortDateString();

                                            // !note: this should return an OK value
                                            LoadRowsToGrid(DataSessionName);
                                            is_data_loaded = true;
                                            

                                        }
                                    }
                                    else
                                    {
                                        label_play.Text = "No audio files were found. Please check the directory name.";
                                        XmlSession = null;
                                    }



                                }

                            } //if textbox is blank
                            else
                            {
                                DataSessionName = DataSessionDir + "annotation_session.txt";
                                
                                //Load list
                                if (LoadList(dataGridView1) == false)
                                {
                                    label_play.Text = "No audio files were found. Please check the directory name.";

                                    // delete previous Xml object
                                    XmlSession = null;
                                }
                                else
                                { is_data_loaded = true; }

                            }
                        }
                        else
                        {
                            label_play.Text = "Problem in the ActivityLabelsRealtime.xml file, at least two categories need to be specified. The category labels cannot be loaded.";

                            // delete previous Xml object
                            XmlSession = null;
                        }

                    }// if Xml file not loaded
                    else
                    {
                        label_play.Text = " Protocol file (ActivityLabelsRealtime.xml) was not found. The category labels cannot be loaded.";

                        // delete previous Xml object
                        XmlSession = null;
                    }


                }
                else //if SessionDir doesn't exist
                {
                    label_play.Text = "No audio files where found in the session\\annotation\\voice directory.";
                    XmlSession = null;
                }


                return is_data_loaded;
            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);


                return false;
            }
        }


        // Load Data from the DataSet into the ListView
        private bool LoadList(DataGridView dgview)
        {
            DateTime time, end_file_time;
            bool data_loaded = false;
            double secs_duration = 0.0;
            string duration = "";


            //Clean previous entries
            DeleteAllRows();


            //Load audio files
            if (files == null)
            {
                LoadAudioFiles();
                
            }


            //If there are audio files, create/add rows
            if (files.Length > 0)
            {

                for (int n = 0; n < files.Length; n++)
                {

                    dgview.Rows.Add();

                    // ID
                    dgview.Rows[n].Cells[C1.ID].Value = n.ToString();


                    //Category Labels 
                    // Category 1
                    dgview.Rows[n].Cells[C1.Lock].Value = true;
                    cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[n].Cells[C1.category_label];
                    set_ComboBox(cellComboBox, n, C1.category_label, 2, " ");
                    dataGridView1.Rows[n].Cells[C1.category_label].Value = " ";

                    // Category 2
                    dgview.Rows[n].Cells[C2.Lock].Value = true;
                    cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[n].Cells[C2.category_label];
                    set_ComboBox(cellComboBox, n, C2.category_label, 2, " ");
                    dataGridView1.Rows[n].Cells[C2.category_label].Value = " ";


                    //-------- Here compute the creation time ---------------
                    end_file_time = files[n].LastWriteTime;

                    //If there is an offset add it, to the creation time
                    //If there is an offset add it, to the current time
                    if ((Math.Abs(AudioOffset.TotalSeconds) > 0.0) &&
                        ((IsOffsetApplied == 0) || (IsOffsetApplied == 2)))
                    {
                        //time = time.Add(AudioOffset);
                        end_file_time = end_file_time.Add(AudioOffset);
                    }
                            

                    secs_duration = 0.0;
                    
                    duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);
                    //duration = GetDuration(files[n].FullName, files[n].Length, out secs_duration);
                    
                    time = end_file_time.Subtract(TimeSpan.FromSeconds(secs_duration));

                   

                    //Load the time row in labels
                    dgview.Rows[n].Cells[C1.Time].Value = time.ToLongTimeString(); 
                    
                    //Add milliseconds granularity
                    dgview.Rows[n].Cells[C1.TimeMS].Value = String.Format("{0:HH:mm:ss.fff}", time);
                    dgview.Rows[n].Cells[C1.Time_Label].Value = time.ToLongTimeString(); 

                    //Add duration info
                    dgview.Rows[n].Cells[C1.TimeLastWrite].Value = String.Format("{0:HH:mm:ss.fff}", end_file_time);

                    dgview.Rows[n].Cells[C1.TimeDuration].Value = duration;

                    //--------------------------------------------------------

                    // Status
                    dgview.Rows[n].Cells[C1.Status].Value = " ";
                    dgview.Rows[n].Cells[C1.StartID].Value = -1;
                    dgview.Rows[n].Cells[C1.EndID].Value = -1;

                    dgview.Rows[n].Cells[C2.Status].Value = " ";
                    dgview.Rows[n].Cells[C2.StartID].Value = -1;
                    dgview.Rows[n].Cells[C2.EndID].Value = -1;

                    

                }

                

                time = files[0].LastWriteTime;
                StartDate = time.Year + "-" + time.Month + "-" + time.Day;

                time = files[files.Length - 1].LastWriteTime;
                EndDate = time.Year + "-" + time.Month + "-" + time.Day;


                // End/Start
                CStartEnd_1.Items.Add(" ");
                CStartEnd_1.Items.Add("End");
                CStartEnd_1.Items.Add("Start");

                CStartEnd_2.Items.Add(" ");
                CStartEnd_2.Items.Add("End");
                CStartEnd_2.Items.Add("Start");



                data_loaded = true;
            }
            else
            {
                label_play.Text = "No audio files were found.Please check directory name.";
            }

            return data_loaded;
        }

      
        private bool SessionDir_Exist()
        {
            bool result = false;
            DataAudioDir = Folder_annotation + "voice\\"; 

      
            if( Directory.Exists(DataAudioDir) == true)
            {
              
                DataSessionDir = Folder_annotator_files;
                DataOutputDir = Folder_annotator_files;

                result = true;
            }

            return result;
        }


        private bool LoadGridColumnHeaders()
        {
            bool result = false;

            if (list_category_name != null)
            {
                if ((list_category_name.Count > 0) && (list_category_name.Count >= 2))
                {
                    /*if (SessionPart == 1)
                    { dataGridView1.Columns[CINDEX.category_label].HeaderText = list_category_name[0].ToUpper(); }
                    else if(SessionPart == 2)
                    { dataGridView1.Columns[CINDEX.category_label].HeaderText = list_category_name[1].ToUpper(); }                
                     */

                    dataGridView1.Columns[C1.category_label].HeaderText = list_category_name[0];
                    dataGridView1.Columns[C2.category_label].HeaderText = list_category_name[1];

                    result = true;
                }  
            }

            return result;

        }

        private void LoadViewGrid(string vw)
        {
            if (vw.CompareTo("grid") == 0)
            {
                //------ hide ------------
                textBox_1.Visible = false;
                //textBox_2.Visible = false;
                textBox_instructions_1.Visible = false;
                textBox_instructions_2.Visible = false;

                label_files_path.Visible = false;
                //label_protocol_file.Visible = false;

                button_1.Visible = false;
                button_2.Visible = false;
                //button_3.Visible = false;

                panel_controls_1.Visible = false;
                label_panel1_1.Visible = false;
                label_panel1_2.Visible = false;

                label_play.Text = "OK";


                //------ show ------------
                label_instructions_1.Visible = true;

                button_add.Visible = true;
                label_add_button.Visible = true;

                button_remove.Visible = true;
                label_remove_button.Visible = true;

                button_save.Visible = true;
                label_save_button.Visible = true;

                button_generate.Visible = true;
                button_generate.Enabled = false;
                label_generate_button.Visible = true;

                button_exit.Visible = true;
                label_exit_button.Visible = true;

                button_category_select.Visible = true;
                label_category_button.Visible = true;

                dataGridView1.Visible = true;

                label_instructions_2.Visible = true;
                label_instructions_3.Visible = true;
                label_play.Visible = true;

                label_date.Visible = true;
                label_date.Text = "Experiment Date: " + StartDate;

                checkBox_SiglePassMode.Visible = true;
                checkBox_ExitWithoutSaving.Visible = true;
                panel_controls_2.Visible = true;

                label_instructions_1.Text = "Press F1 to play audio file.   Press F2 to edit field.";
                label_instructions_2.Text = "Status";

                //---------------------------



            }
            else if (vw.CompareTo("select") == 0)
            {

            }
        }


        #endregion


        #region Buttons


        //Browse session button
        private void button_load_Click(object sender, EventArgs e)
        {
            try
            {

                this.folderBrowserDialog.ShowNewFolderButton = false;

                if (textBox_1.Text.Trim().CompareTo("") != 0)
                {
                    if (Directory.Exists(textBox_1.Text))
                    { this.folderBrowserDialog.SelectedPath = textBox_1.Text.ToString(); }
                    else
                    { this.folderBrowserDialog.RootFolder = System.Environment.SpecialFolder.Desktop; }
                }
                else
                {
                    this.folderBrowserDialog.RootFolder = System.Environment.SpecialFolder.Desktop;
                }

                DialogResult result = this.folderBrowserDialog.ShowDialog();


                if (result == DialogResult.OK)
                {
                    string fullPath = this.folderBrowserDialog.SelectedPath;
                    textBox_1.Text = fullPath;

                    if (textBox_1.Text.Trim().CompareTo("") == 0)
                    {
                        textBox_instructions_1.Text = "Please provide a valid path containing the session data, then click Start.";
                    }
                    else
                    {

                        #region commented
                        //----------------------------------------------------------
                        /*
                        //read audio files
                        folder = new DirectoryInfo(fullPath + "\\annotation\\voice\\");

                    
                        //files_wav = folder.GetFiles("*.wav");
                        //files = folder.GetFiles("*.msv");

                        files_wav = folder.GetFiles("*.mp3");
                        files = folder.GetFiles("*.mp3");

                        // sort the recorder audio files by creation time (Oct-22-2009)
                        Array.Sort(files, new CompareFileInfoByDate());


                        if (files_wav.Length != files.Length)
                        { textBox_instructions_1.Text = "Warning: mistmatch between number of msv and wav files!"; }

                        //----------------------------------------------------------------
                        */
                        #endregion

                        DataAudioDir = fullPath + "\\annotation\\voice\\";

                        if (Directory.Exists(DataAudioDir))
                        {
                            if (LoadAudioFiles())
                            {
                                if (files_wav.Length > 0)
                                {
                                    textBox_instructions_1.Text = "The audio files were loaded.";

                                    #region commented
                                    //DataAudioDir = files_wav[0].DirectoryName;

                                    //if (textBox_1.Text.Trim().CompareTo("") == 0)
                                    //{ textBox_instructions_1.Text = "Please provide a valid path for the audio files, then click Start."; }
                                    //else
                                    //{ textBox_instructions_1.Text = ""; }
                                    #endregion

                                }
                                else
                                {
                                    textBox_instructions_1.Text = "No audio files were found. Please check you have the files in the directory: session\annotation\voice";
                                }
                            }
                            else
                            {
                                textBox_instructions_1.Text = "No audio files were found. Please check you have the files in the directory: session\annotation\voice";
                            }
                        }
                        else
                        {
                            textBox_instructions_1.Text = "The audio files directory was not found. Please check that the  \\annotation\\voice\\ folder exists.";
                        }

                    }
                }


            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }
        }


       
        private void button_add_label_Click(object sender, EventArgs e)
        {

            if (dataGridView1.Rows.Count == 0)
            {
                current_row = 0;

                dataGridView1.Rows.Insert(current_row, 1);


                initialize_row(current_row, 2, " ", current_row + 1, CINDEX.category_label);

            }
            else
            {

                if ((((current_column == C1.category_label) || (current_column == C1.StartEnd)) &&
                       (CCategory_1.ReadOnly == false)
                     )
                     ||
                     ((current_column == C2.category_label || (current_column == C2.StartEnd)) &&
                        (CCategory_2.ReadOnly == false)
                     )
                   )
                {
                    int index_new_row = current_row + 1;
                    int startRow = current_row;

                    int typeCombo = 1;
                    string label_row = " ";

                    //Determine if a start label is open
                    int is_open = 1;
                    int row_open = search_open_row_backwards(current_row);

                    if ((row_open == current_row) || (current_row == 0))
                    { is_open = 0; }


                    if (is_open == 0)
                    {
                        if (dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value != null)
                        {
                            if (dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value.GetType().Equals(typeof(int)) == false)
                            { dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value = Convert.ToInt32(dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value.ToString()); }

                            startRow = (int)dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value;
                        }
                        else
                        { dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value = startRow; }

                        if (startRow < 0)
                        {
                            startRow = 0;
                            dataGridView1.Rows[current_row].Cells[CINDEX.StartID].Value = 0;
                        }

                        if (dataGridView1.Rows[startRow].Cells[CINDEX.category_label].Value != null)
                        { label_row = dataGridView1.Rows[startRow].Cells[CINDEX.category_label].Value.ToString(); }
                        typeCombo = 2;
                    }
                    else
                    {
                        typeCombo = 2;
                    }

                    // insert the row


                    if (index_new_row >= dataGridView1.Rows.Count)
                    { index_new_row = dataGridView1.Rows.Count - 1; }


                    dataGridView1.Rows.Insert(index_new_row, 1);


                    // initialize the row according if start label is open or not
                    initialize_row(index_new_row, typeCombo, label_row, index_new_row + 1, CINDEX.category_label);
                }
                else
                {
                    label_play.Text = "The row cannot be added. The selected category field should be editable.";

                }
            }
        }


        private void button_remove_label_Click(object sender, EventArgs e)
        {

            if ((dataGridView1.Rows.Count > 0) && (current_row < dataGridView1.Rows.Count))
            {
                if (dataGridView1.Rows[current_row].Cells[CINDEX.ID].Value.ToString().CompareTo("-----") == 0)
                {
                    if (current_row >= dataGridView1.Rows.Count)
                    {

                        if (dataGridView1.Rows[current_row].Cells[C1.category_label].Value == null)
                        { dataGridView1.Rows[current_row].Cells[C1.category_label].Value = " "; }
                        if (dataGridView1.Rows[current_row].Cells[C2.category_label].Value == null)
                        { dataGridView1.Rows[current_row].Cells[C2.category_label].Value = " "; }



                        if ((((current_column == C1.category_label) || (current_column == C1.StartEnd)) &&
                              (dataGridView1.Rows[current_row - 1].Cells[C2.category_label].Value.ToString().CompareTo(" ") == 0) &&
                              (CCategory_1.ReadOnly == false)
                            )
                            ||
                            ((current_column == C2.category_label || (current_column == C2.StartEnd)) &&
                              (dataGridView1.Rows[current_row - 1].Cells[C1.category_label].Value.ToString().CompareTo(" ") == 0) &&
                              (CCategory_2.ReadOnly == false)
                            )
                          )
                        {
                            //if ((dataGridView1.Rows[current_row-1].Cells[C1.category_label].Value.ToString().CompareTo(" ") == 0) &&
                            //     (dataGridView1.Rows[current_row-1].Cells[C2.category_label].Value.ToString().CompareTo(" ") == 0))
                            //{
                            dataGridView1.Rows.RemoveAt(current_row - 1);
                            current_row = current_row - 1;
                        }
                        else
                        {
                            //label_play.Text = "Both category fields should be set to 'blank' to remove a row.";
                            label_play.Text = "The row cannot be removed. The selected category field should be editable and the non-selected category field should be 'blank'.";

                        }

                    }
                    else
                    {
                        if (dataGridView1.Rows[current_row].Cells[C1.category_label].Value == null)
                        { dataGridView1.Rows[current_row].Cells[C1.category_label].Value = " "; }
                        if (dataGridView1.Rows[current_row].Cells[C2.category_label].Value == null)
                        { dataGridView1.Rows[current_row].Cells[C2.category_label].Value = " "; }



                        if ((((current_column == C1.category_label) || (current_column == C1.StartEnd)) &&
                              (dataGridView1.Rows[current_row].Cells[C2.category_label].Value.ToString().CompareTo(" ") == 0) &&
                              (CCategory_1.ReadOnly == false)
                            )
                            ||
                            ((current_column == C2.category_label || (current_column == C2.StartEnd)) &&
                              (dataGridView1.Rows[current_row].Cells[C1.category_label].Value.ToString().CompareTo(" ") == 0) &&
                              (CCategory_2.ReadOnly == false)
                            )
                          )
                        {
                            //if ((dataGridView1.Rows[current_row].Cells[C1.category_label].Value.ToString().CompareTo(" ") == 0) &&
                            //     (dataGridView1.Rows[current_row].Cells[C2.category_label].Value.ToString().CompareTo(" ") == 0))
                            //{
                            dataGridView1.Rows.RemoveAt(current_row);
                        }
                        else
                        {

                            label_play.Text = "The row cannot be removed. The selected category field should be editable and the non-selected category field should be 'blank'.";
                        }
                    }
                }
                else
                {
                    label_play.Text = "The row cannot be removed. This row is associated to an audio file and audio file rows cannot be removed. Instead, leave it blank.";
                }
            }

        }



        private void dataGridView1_RowHeaderMouseDoubleClick_1(object sender, DataGridViewCellMouseEventArgs e)
        {
            PlayFile(e.RowIndex);
        }


        #endregion



        #region Audio Files

        //=======  Compute the sound length ==================
       
        private bool LoadAudioFiles()
        {
            try
            {
                bool success = false;


                DirectoryInfo dir = new DirectoryInfo(DataAudioDir);

                if (dir.Exists)
                {

                    // read audio files
                    files = dir.GetFiles("*.msv");

                    if (files.Length > 0)
                    {
                        files_wav = dir.GetFiles("*.wav");
                    }
                    else if (files.Length == 0)
                    {
                        files_wav = dir.GetFiles("*.mp3");
                        DirectoryInfo dir_labels = new DirectoryInfo(DataAudioDir+"voice_time_labels\\");
                        files = dir.GetFiles("*.mp3");
                    }


                    if (files.Length > 0)
                    {   
                        // sort the recorder audio files by creation time (Oct-22-2009)
                        Array.Sort(files, new CompareFileInfoByDate());
                        FileInfo[] array_files_output;
                        CompareInfoOrder(files, files_wav, out array_files_output);

                       if (array_files_output != null)
                       {


                           files_wav = array_files_output;


                           if (files_wav.Length != files.Length)
                           { label_play.Text = "Warning: mistmatch between number of msv and wav files!"; }
                           else
                           {
                               success = true;
                               IsOffsetApplied = 0;

                               if (File.Exists(DataAudioDir + file_offset))
                               {
                                   //ReadOffset
                                   TextReader txr = new StreamReader(DataAudioDir + file_offset);
                                   string str_offset = txr.ReadLine();
                                   AudioOffset = TimeSpan.Parse(str_offset);

                                   IsOffsetApplied = Int16.Parse(txr.ReadLine());

                                   txr.Close();
                                   txr.Dispose();

                                   //WriteOffset
                                   if (IsOffsetApplied == 0)
                                   {
                                       TextWriter txw = new StreamWriter(DataAudioDir + file_offset);
                                       txw.WriteLine(str_offset);
                                       txw.WriteLine("1");
                                       txw.Close();
                                       txw.Dispose();
                                   }

                               }// if offset file exist

                           }// if the size of files is the same

                       }// if the wav files were ordered

                    }//if the length of the files is > than zero
                    else
                    {
                        label_play.Text = "No audio files found!";
                    }

                    
                }

                return success;

            } // end try

            catch
            {
                //Console.WriteLine(err.Message);
                return false;
            }

        }


  public  void CompareInfoOrder(FileInfo[] array_order, FileInfo[] array_src, out FileInfo[] array_output)
    {
        
        array_output = null;

        if (array_order.Length > 0 && array_src.Length > 0)
        {
            if (array_order.Length == array_src.Length)
            {
                

                string[] fname;
                bool is_name_equal = false;
                int[] indexes = new int[array_order.Length];
                array_output = new FileInfo[array_order.Length];



                for (int j = 0; j < indexes.Length; j++)
                { indexes[j] = 0; }


                for (int i = 0; i < array_order.Length; i++)
                {
                    fname = array_order[i].Name.Split('.');
                    is_name_equal = false;


                    for (int k = 0; k < array_src.Length; k++)
                    {
                        if (indexes[k] == 0)
                        {
                            is_name_equal = array_src[k].Name.Contains(fname[0]);

                            if (is_name_equal)
                            {
                                array_output[i] = array_src[k];
                                indexes[k] = 1;
                                break;
                            }
                        }
                    }

                }
            }
        }

       
    }




        private WindowsMediaPlayerClass wmp = new WindowsMediaPlayerClass();
        private IWMPMedia mediainfo;

        private int header = 44;
        private int sample_rate = 44100;
        private int bit_rate = 16;
        //private int num_channels = 2;

        public string GetDuration(string path,long file_length ,out double secs_duration)
        {
            try
            {
                string audio_duration = "-1";
                mediainfo = null;
                secs_duration = 0.0;

                if (File.Exists(path))
                {
                    if (path.ToUpper().Contains("MP3"))
                    {
                        mediainfo = wmp.newMedia(path);


                        if (mediainfo.duration > 0.0)
                        {
                            //audio_duration = mediainfo.durationString;
                            audio_duration = mediainfo.duration.ToString();
                            secs_duration = mediainfo.duration;
                        }

                        
                    }
                    else if( path.ToUpper().Contains("WAV"))
                    {
                        secs_duration = Math.Round( ((file_length - header) / (sample_rate * (bit_rate / 8.0)))/2.0 , 3);
                        audio_duration = secs_duration.ToString();                  
                    }
                    else
                    {
                        label_play.Text = ("Audio file extension not identified: " + path);
                    }

                }
                else
                {
                    label_play.Text = ("Audio file not found: " + path);
                }


                return audio_duration;
            }
            catch
            {
                secs_duration = 0.0;
                return "-1";

            }
        }




        // Play Audio Files
        private void button_play_Click(object sender, EventArgs e)
        {
            for (int i = 0; i < files_wav.Length; i++)
            {
                label_play.Text = "Playing audio file: " + i.ToString();
                                  

                Application.DoEvents();

               
               PlayAudio(i);
                
            }
        }

        

        private void PlayFile(int index)
        {
            int play_id = index;

            if ((dataGridView1.Rows[index].Cells[CINDEX.ID].Value != null) &&
                      (dataGridView1.Rows[index].Cells[CINDEX.ID].Value.ToString().CompareTo("-----") != 0))
            {
                play_id = System.Convert.ToInt16(dataGridView1.Rows[index].Cells[CINDEX.ID].Value.ToString());

                label_play.Text = "playing file " + play_id.ToString();
                Application.DoEvents();

                PlayAudio(play_id);
                label_play.Text = "...";
            }
            else
            {
                label_play.Text = "No audio file associated to this row. The row was created by user. ";
                Application.DoEvents();

            }

        }

        private void PlayAudio(int index)
        {
            if (files_wav != null)
            {
                if (files_wav.Length > 0)
                {
                    try
                    {
                        //myPlayer.SoundLocation = files_wav[index].FullName;
                        //myPlayer.PlaySync();
                        wmp.currentMedia = wmp.newMedia(files_wav[index].FullName);
                        wmp.controls.play();

                        //double secs_duration = 0.0;
                        //string audio_str = GetDuration(files_wav[index].FullName, files_wav[index].Length, out secs_duration);
                    }
                    catch
                    {   // error playing file
                    }
                }
            }

        }



        #endregion


        #region Row Operations

        private void initialize_row(int row, int TypeCombo, string row_label, int row_label_time, int index_label)
        {

            // initialize values
            dataGridView1.Rows[row].Cells[CINDEX.ID].Value = NO_AUDIO_ROW_STR;  //"-----";

            // initialize locks
            dataGridView1.Rows[row].Cells[C1.Lock].Value = true;
            dataGridView1.Rows[row].Cells[C2.Lock].Value = true;

            //initialize category labels            
            if (index_label == C1.category_label)
            {
                set_ComboBox(cellComboBox, row, C1.category_label, TypeCombo, row_label);
                set_ComboBox(cellComboBox, row, C2.category_label, 2, " ");
            }
            else
            {
                set_ComboBox(cellComboBox, row, C1.category_label, 2, " ");
                set_ComboBox(cellComboBox, row, C2.category_label, TypeCombo, row_label);
            }


            //check is not the end of the list, if end of the list set the time of the previous row
            if ((row_label_time < dataGridView1.Rows.Count) && (row_label_time > -1))
            {
                //obtain what the next row has in its label_time field
                dataGridView1.Rows[row].Cells[CINDEX.Time_Label].Value = dataGridView1.Rows[row_label_time].Cells[CINDEX.Time_Label].Value;

                //Adding milliseconds granularity
                dataGridView1.Rows[row].Cells[CINDEX.TimeMS].Value = dataGridView1.Rows[row_label_time].Cells[CINDEX.TimeMS].Value;

                //Add duration info
                dataGridView1.Rows[row].Cells[CINDEX.TimeLastWrite].Value = dataGridView1.Rows[row_label_time].Cells[CINDEX.TimeLastWrite].Value;
                dataGridView1.Rows[row].Cells[CINDEX.TimeDuration].Value = dataGridView1.Rows[row_label_time].Cells[CINDEX.TimeDuration].Value;

            }
            else if (( (row-1) < dataGridView1.Rows.Count) && ( (row-1) > -1))
            {
                //set the time label according to previous row label available
                dataGridView1.Rows[row].Cells[CINDEX.Time_Label].Value = dataGridView1.Rows[row -1 ].Cells[CINDEX.Time_Label].Value;
                
                //Adding milliseconds granularity
                dataGridView1.Rows[row].Cells[CINDEX.TimeMS].Value = dataGridView1.Rows[row - 1].Cells[CINDEX.TimeMS].Value;

                //Add duration info
                dataGridView1.Rows[row].Cells[CINDEX.TimeLastWrite].Value = dataGridView1.Rows[row - 1].Cells[CINDEX.TimeLastWrite].Value;
                dataGridView1.Rows[row].Cells[CINDEX.TimeDuration].Value = dataGridView1.Rows[row - 1].Cells[CINDEX.TimeDuration].Value;

            }


            // Status
            // check if I need to setup the parameters according with previous row
            dataGridView1.Rows[row].Cells[C1.Status].Value = " ";
            dataGridView1.Rows[row].Cells[C1.StartID].Value = -1;
            dataGridView1.Rows[row].Cells[C1.EndID].Value = -1;

            dataGridView1.Rows[row].Cells[C2.Status].Value = " ";
            dataGridView1.Rows[row].Cells[C2.StartID].Value = -1;
            dataGridView1.Rows[row].Cells[C2.EndID].Value = -1;

            
            //Paint the cells according with the appropriate view
            if( checkBox_SiglePassMode.Checked )
            {   
                //load single view
                paintcells_view(row,3);
            }
            else if (SessionPart == 2)
            {
                //load view 2
                paintcells_view(row, 2);
            }
            else if (SessionPart == 1)
            {
                //load view 1
                paintcells_view(row, 1);
            }

        }


        private void fill_row(int row, int TypeCombo, string row_label, int row_label_time, int index_label,
                              string status, int open_row, int end_row, bool is_row_new)
        {

            if (is_row_new == true)
            { initialize_row(row, TypeCombo, row_label, row_label_time, index_label); }


            dataGridView1.Rows[row].Cells[index_label].Value = row_label;

            // Status
            if (status.CompareTo("end") == 0)
            {
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "end";
                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "End";
                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = row;
            }
            else if (status.CompareTo("start") == 0)
            {
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";
                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "Start";
                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = row;
                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = end_row;
            }
            else if (status.CompareTo("start_on") == 0)
            {
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start_on";
                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";
                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = end_row;
            }
            else if (status.CompareTo(" ") == 0)
            {
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = " ";
                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";
                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = end_row;
            }

        }

        private int add_start_row(int row, out int nrows, string row_label, int index_label, int close_row, bool set_label_time)
        {
            int start_row;

            // need to insert an end row below
            dataGridView1.Rows.Insert(row, 1);


            // update number of rows, and close_row
            nrows = dataGridView1.Rows.Count;
            start_row = row;

            // fill "end" in inserted row and close label
            if (set_label_time == true)
            { fill_row(start_row, 2, row_label, close_row, index_label, "start", start_row, close_row, true); }
            else
            { fill_row(start_row, 2, row_label, -1, index_label, "start", start_row, close_row, true); }

            return start_row;
        }


        private int add_end_row(int row, out int nrows, string row_label, int index_label, int open_row, bool set_label_time)
        {
            int close_row;

            // need to insert an end row below
            dataGridView1.Rows.Insert(row, 1);


            // update number of rows, and close_row
            nrows = dataGridView1.Rows.Count;
            close_row = row;

            // fill "end" in inserted row and close label
            if (set_label_time == true)
            {
                //fill_row(close_row, 1, row_label, close_row + 1, index_label, "end", open_row, close_row, true); 
                fill_row(close_row, 2, row_label, close_row + 1, index_label, "end", open_row, close_row, true);
            }
            else
            {
                //fill_row(close_row, 1, row_label, -1, index_label, "end", open_row, close_row, true);
                fill_row(close_row, 2, row_label, -1, index_label, "end", open_row, close_row, true);
            }

            return close_row;
        }



        private int cleanup_forward(int start_row, int end_row, string row_label)
        {
            int error = 0;

            // cleanup
            if (set_status_forward(start_row, end_row, row_label, 3, false, start_row) == -1)
            {
                //System.Console.WriteLine("Error, end label was found before"); 
                error = -1;
            }

            return error;
        }


        private void SaveRowsToFile(string fname)
        {
            string row_string = "";


            file_session = new FileInfo(fname);


            if (file_session.Exists == true)
            {
                file_session.Delete();
            }


            tw = new StreamWriter(fname);
            tw.WriteLine(StartDate + ";" + EndDate + ";");

            if (dataGridView1.Rows.Count > 0)
            {
                for (int i = 0; i < dataGridView1.Rows.Count; i++)
                {
                    get_string(i, out row_string);
                    tw.WriteLine(row_string);

                }
            }

            tw.Close();

            label_play.Text = "The session has been saved.";

        }

        private void get_string(int row, out string st)
        {
            st = "";
            string value = "";


            for (int i = 0; i < dataGridView1.Columns.Count; i++)
            {

                if (i == (C1.Lock))
                {
                    if (dataGridView1.Rows[row].Cells[C1.Lock].Value != null)
                    {
                        if (((bool)dataGridView1.Rows[row].Cells[C1.Lock].Value) == true)
                        { value = "True"; }
                        else
                        { value = "False"; }
                    }
                    else
                    {
                        dataGridView1.Rows[row].Cells[C1.Lock].Value = false;
                        value = "False";
                    }
                }
                else if (i == (C2.Lock))
                {
                    if (dataGridView1.Rows[row].Cells[C2.Lock].Value != null)
                    {
                        if (((bool)dataGridView1.Rows[row].Cells[C2.Lock].Value) == true)
                        { value = "True"; }
                        else
                        { value = "False"; }
                    }
                    else
                    {
                        dataGridView1.Rows[row].Cells[C2.Lock].Value = false;
                        value = "False";
                    }
                }
                else if (i == C1.Combo_Type)
                {
                    if (dataGridView1.Rows[row].Cells[C1.category_label] != null)
                    {

                        cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[C1.category_label];

                        if ((cellComboBox.Items.Count == list_category_1.Count) ||
                                (cellComboBox.Items.Count == 0))
                        { value = "F"; }
                        else
                        { value = "S"; }


                        #region commented
                        /*if (SessionPart == 1)
                        {
                            if ( (cellComboBox.Items.Count == list_category_1.Count) ||
                                 (cellComboBox.Items.Count == 0))
                            { value = "F"; }
                            else 
                            { value = "S"; }
                        }
                        else if (SessionPart == 2)
                        {
                            if ((cellComboBox.Items.Count == list_category_2.Count) ||
                                 (cellComboBox.Items.Count == 0))
                            { value = "F"; }
                            else
                            { value = "S"; }
                        }
                       */
                        #endregion 

                    }
                    else
                    {
                        value = "F";
                    }

                }
                else if (i == C2.Combo_Type)
                {
                    if (dataGridView1.Rows[row].Cells[C2.category_label] != null)
                    {

                        cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[C2.category_label];

                        if ((cellComboBox.Items.Count == list_category_2.Count) ||
                                (cellComboBox.Items.Count == 0))
                        { value = "F"; }
                        else
                        { value = "S"; }

                    }
                    else
                    {
                        value = "F";
                    }

                }
                else if (i == C1.Combo_Label)
                {
                    if (dataGridView1.Rows[row].Cells[C1.category_label].Value != null)
                    {
                        value = dataGridView1.Rows[row].Cells[C1.category_label].Value.ToString();
                    }
                    else
                    { value = " "; }

                }
                else if (i == C2.Combo_Label)
                {
                    if (dataGridView1.Rows[row].Cells[C2.category_label].Value != null)
                    {
                        value = dataGridView1.Rows[row].Cells[C2.category_label].Value.ToString();
                    }
                    else
                    { value = " "; }

                }
                else
                {
                    if (dataGridView1.Rows[row].Cells[i].Value != null)
                    {
                        value = dataGridView1.Rows[row].Cells[i].Value.ToString();
                    }
                    else
                    {
                        value = " ";
                    }
                }


                st = st + value + ";";

            }

        }

        
        
        
        
        private int previous_row_audio_file = 0;
        private string previous_time_audio_file = "";
       

        private bool LoadRowsToGrid(string fname)
        {

            bool data_loaded = false;
          

            try
            {
                if (files != null)
                {
                    if (files.Length > 0)
                    {
                        string row_string = "";
                        
                        file_session = new FileInfo(fname);

                        if (file_session.Exists == false)
                        {
                            label_play.Text = "Session file was not found. A new session file will be created.";

                        }
                        else
                        {

                            DeleteAllRows();


                            // Set End-Start
                            CStartEnd_1.Items.Add(" ");
                            CStartEnd_1.Items.Add("End");
                            CStartEnd_1.Items.Add("Start");

                            CStartEnd_2.Items.Add(" ");
                            CStartEnd_2.Items.Add("End");
                            CStartEnd_2.Items.Add("Start");

                            tr = new StreamReader(fname);
                            row_string = tr.ReadLine();


                            if (row_string != null)
                            {

                                string[] ncells = row_string.Split(';');
                                StartDate = ncells[0];
                                EndDate = ncells[1];

                                row_string = tr.ReadLine();
                            }


                            previous_row_audio_file = 0;
                            //int correction_made = 0;
                            //int needed_correction = 0;

                            while (row_string != null)
                            {
                                //ReadRow(row_string);
                                //needed_correction = ReadRow(row_string, true);
                                //if( (correction_made == 0) && (needed_correction >0))
                                //{
                                //    correction_made = needed_correction;
                                //}
                                ReadRow(row_string, true);
                                row_string = tr.ReadLine();
                            }


                            tr.Close();

                            data_loaded = true;


                            //output_str = "The Session has been loaded.";
                      
                            //if a correction was made, check which type and notify 
                            //if (correction_made == 1)
                            //{ output_str = output_str + "Time stamps were corrected:the file duration was computed."; }
                            //else if (correction_made == 2)
                            //{ output_str = output_str + "Time stamps were corrected:the time duration was corrupted."; }
                            
                    

                            
                        }

                    }
                }

            }
            catch
            { }

            return data_loaded;

        }


        //Read a row from previous saved session
        //Check if it is necessary to correct the time stamp
        private void ReadRow(string st)
        {
            string[] ncells = st.Split(';');

            int row = dataGridView1.Rows.Add();


            for (int i = 0; i < (ncells.Length - 1); i++)
            {

                if (i == C1.Lock)
                {
                    if (ncells[i].CompareTo("True") == 0)
                    { dataGridView1.Rows[row].Cells[i].Value = true; }
                    else
                    { dataGridView1.Rows[row].Cells[i].Value = false; }
                }
                else if (i == C2.Lock)
                {
                    if (ncells[i].CompareTo("True") == 0)
                    { dataGridView1.Rows[row].Cells[i].Value = true; }
                    else
                    { dataGridView1.Rows[row].Cells[i].Value = false; }
                }
                else if ((i == C1.category_label) || (i == C2.category_label))
                {
                    // Do nothing
                }
                else if (i == C1.Combo_Label)
                {
                    dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                    if (dataGridView1.Rows[row].Cells[C1.Combo_Type].Value.ToString().CompareTo("S") == 0)
                    { set_ComboBox(cellComboBox, row, C1.category_label, 1, ncells[i]); }
                    else
                    { set_ComboBox(cellComboBox, row, C1.category_label, 2, ncells[i]); }

                    dataGridView1.Rows[row].Cells[C1.category_label].Value = ncells[C1.category_label];
                }
                else if (i == C2.Combo_Label)
                {
                    dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                    if (dataGridView1.Rows[row].Cells[C2.Combo_Type].Value.ToString().CompareTo("S") == 0)
                    { set_ComboBox(cellComboBox, row, C2.category_label, 1, ncells[i]); }
                    else
                    { set_ComboBox(cellComboBox, row, C2.category_label, 2, ncells[i]); }

                    dataGridView1.Rows[row].Cells[C2.category_label].Value = ncells[C2.category_label];
                }
                else
                {
                    dataGridView1.Rows[row].Cells[i].Value = ncells[i];
                }

            }



        }


        //Read a row from previous saved session
        //Check if it is necessary to correct the time stamp
        private int ReadRow(string st, bool check_time_stamp)
        {

            int n = 0;
            DateTime end_file_time, time, time_ms, prev_time_ms;
            TimeSpan time_diff;
            string duration = "";
            double secs_duration;

            
            bool ID_value_set = false;
            bool Time_value_set = false;
            bool is_audio_row = false;


            string[] ncells = st.Split(';');

            int row = dataGridView1.Rows.Add();
            int nCellsLenght = ncells.Length - 1;
            //int needed_correction = 0;
            int success = 0;

            int i = 0;


            try
            {
                for (i = 0; i < nCellsLenght; i++)
                {

                  
                    if (i == C1.Lock)
                    {
                        if (ncells[i].CompareTo("True") == 0)
                        { dataGridView1.Rows[row].Cells[i].Value = true; }
                        else
                        { dataGridView1.Rows[row].Cells[i].Value = false; }
                    }
                    else if (i == C2.Lock)
                    {
                        if (ncells[i].CompareTo("True") == 0)
                        { dataGridView1.Rows[row].Cells[i].Value = true; }
                        else
                        { dataGridView1.Rows[row].Cells[i].Value = false; }
                    }
                    else if (i == C1.Combo_Label)
                    {
                        dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                        if (dataGridView1.Rows[row].Cells[C1.Combo_Type].Value.ToString().CompareTo("S") == 0)
                        { set_ComboBox(cellComboBox, row, C1.category_label, 1, ncells[i]); }
                        else
                        { set_ComboBox(cellComboBox, row, C1.category_label, 2, ncells[i]); }


                        dataGridView1.Rows[row].Cells[C1.category_label].Value = ncells[C1.category_label];

                        DataGridViewComboBoxCell combo = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[2];
                        
                    
                    }
                    else if (i == C2.Combo_Label)
                    {
                        dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                        if (dataGridView1.Rows[row].Cells[C2.Combo_Type].Value.ToString().CompareTo("S") == 0)
                        { set_ComboBox(cellComboBox, row, C2.category_label, 1, ncells[i]); }
                        else
                        { set_ComboBox(cellComboBox, row, C2.category_label, 2, ncells[i]); }

                        dataGridView1.Rows[row].Cells[C2.category_label].Value = ncells[C2.category_label];

                    }
                    else if ((i == C1.category_label) || (i == C2.category_label))
                    {  
                        // do nothing 

                    }
                    // C1.ID and C2.ID have the same values, so compare only one of them
                    else if (i == C1.ID)
                    {

                        dataGridView1.Rows[row].Cells[i].Value = ncells[i];
                        ID_value_set = true;

                        if (ncells[i].CompareTo(NO_AUDIO_ROW_STR) != 0)
                        {
                            is_audio_row = true;
                        }
                        else
                        { is_audio_row = false; }


                    }
                    // C1.Time and C2.Time have the same values, so compare only one
                    else if ((i == C1.Time) && (check_time_stamp == true))
                    {

                        time = DateTime.Parse("00:00:00.0");
                        time_ms = time;
                        prev_time_ms = time;


                        #region Compute Time

                        //--------------- Check the Audio File ------------------

                                //If the row has an audio file, read id from file
                        if (is_audio_row == true)
                        {
                            n = Int32.Parse(ncells[C1.ID]);
                            
                            //update the last seen audio file row value
                            previous_row_audio_file = n;
                            end_file_time = files[n].LastWriteTime;


                            //----If there is an offset add it, to the current end time -----
                            if ((Math.Abs(AudioOffset.TotalSeconds) > 0.0) &&
                                ((IsOffsetApplied == 0) || (IsOffsetApplied == 2)))
                            { end_file_time = end_file_time.Add(AudioOffset);  }
                            
                           //----if there is not offset, check if it is daylight saving time
                            //else if (!TimeZone.IsDaylightSavingTime(end_file_time, daylight))
                            //{
                            //    end_file_time = end_file_time.Add(TimeSpan.Parse("01:00:00.0"));
                            //}
                            

                           

                            //Take the TimeMS from the "TimeLabel" field
                            if (C1.TimeMS < nCellsLenght)
                            {   //If the "TimeLabel" field is not empty
                                time_ms = DateTime.Parse(end_file_time.ToShortDateString() + " " + ncells[C1.TimeMS]); 
                            }
                            else
                            {   //If the "TimeLabel" field is empty, copy the time corresponding to the previous audio file
                                if (ncells[C1.Time].Trim().CompareTo("") != 0) // i=7
                                {
                                    time_ms = DateTime.Parse(end_file_time.ToShortDateString() + " " + ncells[C1.Time]);
                                }
                            }
                         }
                        //-------------------------------------------------------------------------
                        // if the row doesn't have an audio file, assign the time stamp 
                        // according to the last seen audio row
                        // Becareful, this can easily mess up things when the labels have been modified
                        else
                        {
                            if (previous_row_audio_file < files.Length - 1)
                            { n = previous_row_audio_file + 1; }
                            else
                            { n = previous_row_audio_file; }


                            end_file_time = files[n].LastWriteTime;


                             //----If there is an offset add it, to the current end time -----
                             if ((Math.Abs(AudioOffset.TotalSeconds) > 0.0) &&
                                 ((IsOffsetApplied == 0) || (IsOffsetApplied == 2)))
                             {
                                end_file_time = end_file_time.Add(AudioOffset);
                             }
                             //----if there is not offset, check if it is daylight saving time
                             //else if (!TimeZone.IsDaylightSavingTime(end_file_time, daylight))
                             //{
                             //        end_file_time = end_file_time.Add(TimeSpan.Parse("01:00:00.0"));
                             //}
                            


                            if (C1.TimeMS < nCellsLenght)
                            { 
                                    //Take the time from the "TimeMS" field
                                    time_ms = DateTime.Parse(end_file_time.ToShortDateString() + " " + ncells[C1.TimeMS]); 
                            }
                            else
                            {
                                //Take the TimeMS from the "TimeLabel" field
                                if (ncells[C1.Time_Label].Trim().CompareTo("") != 0) //i+1 = 8
                                { 
                                    //If the "TimeLabel" field is not empty
                                    time_ms = DateTime.Parse(end_file_time.ToShortDateString() + " " + ncells[C1.Time_Label]); 
                                }
                                else
                                {   //If the "TimeLabel" field is empty, copy the time corresponding to the previous audio file
                                    time_ms = DateTime.Parse(end_file_time.ToShortDateString() + " " + previous_time_audio_file);
                                }
                            }
                        }
                        

                        #endregion




                        //-------- Compute the creation time ---------------
                            //time_ms = time;  //provisional while testing
                            if (row > 0)
                            {
                                if (dataGridView1.Rows[row - 1].Cells[C1.TimeMS].Value != null)
                                { prev_time_ms = DateTime.Parse(end_file_time.ToShortDateString() + " " 
                                                 + dataGridView1.Rows[row - 1].Cells[C1.TimeMS].Value.ToString()); 
                                }
                            }


                           // Compute the creation time
                           // Where end_time == audio_file_time
                            secs_duration = 0.0;
                            duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);
                            time = end_file_time.Subtract(TimeSpan.FromSeconds(secs_duration));
                               
                          
                            #region commented
                            /*
                            // if the time difference is equal zero or less than zero, less 30min
                            // greater than 30 min
                            // the time stamp needs to be corrected
                            if ((time_diff.TotalSeconds == 0.0) ||
                                ((time_diff.TotalSeconds < 0.0) && (Math.Abs(time_diff.TotalSeconds) < 1800) ) &&
                                ((IsOffsetApplied == 1) || (IsOffsetApplied == 0)))
                            {
                                // compute the creation time
                                secs_duration = 0.0;
                                duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);
                                time = end_file_time.Subtract(TimeSpan.FromSeconds(secs_duration));

                                needed_correction = 1;

                            }
                            else if(IsOffsetApplied == 2) 
                            {
                                // compute the creation time
                                time = end_file_time;

                                secs_duration = 0.0;
                                duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);

                                time = time.Subtract(TimeSpan.FromSeconds(secs_duration)); 


                                needed_correction = 2;
                            }
                            else if ((Math.Abs(time_diff.TotalSeconds) >= 3000) && (IsOffsetApplied == 3))
                            {
                                // compute the creation time
                                time = end_file_time.Subtract(time_diff);

                                secs_duration = 0.0;
                                duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);
                                time = time.Subtract(TimeSpan.FromSeconds(secs_duration));

                     
                                needed_correction = 3;
                            }
                            else if (IsOffsetApplied == 4)
                            {
                                //Take the time of thraw audio file to compute the creation time
                                
                                time = end_file_time;

                                secs_duration = 0.0;
                                duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);
                                time = time.Subtract(TimeSpan.FromSeconds(secs_duration));

                                needed_correction = 4;
                            }
                            else
                            {
                                // The end_file time and TimeTS time are correct, 
                                // only compute the duration of the audio file 
                                duration = time_diff.TotalSeconds.ToString();
                            }


                       */

                            #endregion

                            //Check the time sequence between files: substract creation time from the end time
                            //time_diff = end_file_time.Subtract(time);

                            #region creation time check
                        
                           /*
                            // Case 1: Audio creation time == Audio end time
                            // Case 2: Creation time occurs after Audio end time
                            // Case 3: The creation time has a duration bigger than 1 hour
                            if (( time_diff.TotalSeconds == 0.0) ||
                                ( time_diff.TotalSeconds  < 0.0) ||
                                (Math.Abs(time_diff.TotalSeconds) >= 1800))
                              {
                                // end_time == audio_file_time
                                // time == computed creation time
                                // //secs_duration = 0.0;
                                // //duration = GetDuration(files_wav[n].FullName, files_wav[n].Length, out secs_duration);
                                // //time = end_file_time.Subtract(TimeSpan.FromSeconds(secs_duration));
                                // time_ms = time;

                                //Flag that this creation time has a problem
                            }
                            // when the creation time has not problems
                            else 
                            {
                                //Check the time sequence between fields: substract creation time from the end time
                                time_diff = end_file_time.Subtract(time_ms);


                            }
                           */
                        #endregion


                            //Check the time sequence between fields: substract creation time from the end time
                            time_diff = time_ms.Subtract(time);

                            #region
                            // Do not correct if --> time_diff == 0   ||
                            //                   --> abs( time_diff) < Threshold||
                            //                       Threshold = 900
                            //                   --> time_ms > prev_time_ms: load time_ms

                           // Do correct if    --> time_diff >Threshold: time_ms = time
                           //                  --> time_ms < prev_time_ms: if ( time > prev_time_ms) time_ms = time
                           //                                            : else time_ms = prev_time_ms
                            //
                            #endregion

                            #region TimeMS check


                            //if the diff from the creation time is more than 900 secs/15 min.
                            //correct the TimeMS by replacing it with the creation time or previous TimeMS
                            if ((Math.Abs(time_diff.TotalSeconds) >= 900))
                            {  time_ms = time; }
                            else if( row > 0) 
                            {
                                time_diff = time_ms.Subtract(prev_time_ms);

                                if ( time_diff.TotalSeconds < 0.0)
                                {
                                    time_diff = time.Subtract(prev_time_ms);

                                    if ( time_diff.TotalSeconds >= 0.0)
                                        time_ms = time;
                                    else
                                        time_ms = prev_time_ms;
                                }
                            }
                        
                            #endregion



                            //------------------  Write Results To Table  -------------------------
                       //C1.Time "Audio File Creation Time Field"
                        if (is_audio_row == true)
                        {   dataGridView1.Rows[row].Cells[C1.Time].Value = time.ToLongTimeString();
                        
                            dataGridView1.Rows[row].Cells[C1.TimeLastWrite].Value = String.Format("{0:HH:mm:ss.fff}", end_file_time);
                            dataGridView1.Rows[row].Cells[C1.TimeDuration].Value = duration;
                        }
                        else
                        { dataGridView1.Rows[row].Cells[C1.Time].Value = "";
                        
                          dataGridView1.Rows[row].Cells[C1.TimeLastWrite].Value = "";
                          dataGridView1.Rows[row].Cells[C1.TimeDuration].Value = "";
                        }

                        //C1.TimeMS "Annotation Time In Miliseconds Field"
                        if( time_ms.TimeOfDay.TotalMilliseconds == 0.0 )
                        {
                            dataGridView1.Rows[row].Cells[C1.TimeMS].Value = String.Format("{0:HH:mm:ss.fff}", time);                                                  
                        }
                        else 
                        {
                            dataGridView1.Rows[row].Cells[C1.TimeMS].Value = String.Format("{0:HH:mm:ss.fff}", time_ms);
                        }


                        // C1.TimeLabel Reflects the TimeMS in "Annotated Time Label", in long time format
                        dataGridView1.Rows[row].Cells[C1.Time_Label].Value = String.Format("{0:T}", time_ms);


                        //save previous audio time
                        previous_time_audio_file = dataGridView1.Rows[row].Cells[C1.TimeMS].Value.ToString();

                        //-------------------------------------------------------------------------

 
                    }
                    else if (  ( (i == C1.Time_Label) || (i == C1.TimeMS) ||
                                 (i == C1.TimeLastWrite) || (i == C1.TimeDuration)) )
                               //&& (check_time_stamp == true))
                    {
                        //Do nothing, since the value was modified along with the previous field

                    }
                    
                    else
                    {
                        dataGridView1.Rows[row].Cells[i].Value = ncells[i];
                    }

                }


                return success;

            }
            catch
            {
                return -1;
            }
        }



        private void DeleteAllRows()
        {
            if (dataGridView1.Rows.Count > 0)
            {
                //NumberOfRows = dataGridView1.Rows.Count;

                while (dataGridView1.Rows.Count > 0)
                {
                    dataGridView1.Rows.RemoveAt(dataGridView1.Rows.Count - 1);
                }
            }
        }

        #endregion


        #region Sessions

        private void SaveCurrentSessionToFile()
        {
            string row_string = "";
            string fname = DataSessionName;



            //fname = DataSessionDir + "session_p1.txt";
            file_session = new FileInfo(fname);

            #region
            /*
            if (SessionPart == 1)
            {
                fname = DataSessionDir + "session_p1.txt";
                file_session = new FileInfo(fname);
            }
            else if (SessionPart == 2)
            {
                fname = DataSessionDir + "session_p2.txt";
                file_session = new FileInfo(fname);
            }
            */
            #endregion

            // backup previous sessions first
            if (file_session.Exists == true)
            {
                BackUp_PreviousSessions();
                file_session.Delete();
            }
            else
            {
                fname = DataSessionDir + SessionFileName;
            }


            tw = new StreamWriter(fname);
            tw.WriteLine(StartDate + ";" + EndDate + ";");

            if (dataGridView1.Rows.Count > 0)
            {
                for (int i = 0; i < dataGridView1.Rows.Count; i++)
                {
                    get_string(i, out row_string);
                    tw.WriteLine(row_string);

                }
            }

            tw.Close();

            SaveOutputSessionFile();
            label_play.Text = "The session has been saved.";

        }


        private void LoadSessionToGrid()
        {
            string row_string = "";
            string fname = DataSessionName;


            //fname = DataSessionDir + "session_p1.txt";
            file_session = new FileInfo(fname);

            #region
            /*
            if (SessionPart == 1)
            {
                fname = DataSessionDir + "session_p1.txt";
                file_session = new FileInfo(fname);
            }
            else if (SessionPart == 2)
            {
                fname = DataSessionDir + "session_p2.txt";
                file_session = new FileInfo(fname);
            }
            */
            #endregion


            if (file_session.Exists == false)
            {
                label_play.Text = "A saved session file was not found in folder. A new session will be created.";

                // return -1;
            }
            else
            {

                DeleteAllRows();

                // Set End-Start
                CStartEnd_1.Items.Add(" ");
                CStartEnd_1.Items.Add("End");
                CStartEnd_1.Items.Add("Start");

                CStartEnd_2.Items.Add(" ");
                CStartEnd_2.Items.Add("End");
                CStartEnd_2.Items.Add("Start");



                tr = new StreamReader(fname);
                row_string = tr.ReadLine();


                if (row_string != null)
                {

                    string[] ncells = row_string.Split(';');
                    StartDate = ncells[0];
                    EndDate = ncells[1];

                    row_string = tr.ReadLine();
                }



                while (row_string != null)
                {
                    //ReadRow(row_string);
                    ReadRow(row_string, true);
                    row_string = tr.ReadLine();

                }


                tr.Close();

                label_play.Text = "The Session has been loaded.";


            }



        }


        private int IsSessionStarted()
        {
            int is_started = -1;

            PopUp_Message_Window dlg = new PopUp_Message_Window();

            this.Enabled = false;
            //textBox_instructions.ForeColor = System.Drawing.Color.Gainsboro;
            //label_files_path.ForeColor = System.Drawing.Color.Gainsboro;
            //label_protocol_path.ForeColor = System.Drawing.Color.Gainsboro;


            DialogResult dlg_res = dlg.ShowDialog();

            // if create session was selected
            if (dlg_res == DialogResult.No)
            {

                BackUp_PreviousSessions();

                SessionStarted = true;
                is_started = 0;

                //this.BackColor = System.Drawing.Color.DimGray;
                //textBox_instructions.BackColor = System.Drawing.Color.YellowGreen;
                this.Enabled = true;

            } // if load session was selected
            else if (dlg_res == DialogResult.OK)
            {


                SessionStarted = true;
                is_started = 1;

                //this.BackColor = System.Drawing.Color.DimGray;
                //textBox_instructions.BackColor = System.Drawing.Color.YellowGreen;
                this.Enabled = true;

            }// if session selection was canceled
            else if (dlg_res == DialogResult.Cancel)
            {
                SessionStarted = false;
                XmlSession = null;


                //this.BackColor = System.Drawing.Color.DimGray;
                //textBox_instructions.BackColor = System.Drawing.Color.YellowGreen;
                this.Enabled = true;

                label_play.Text = "To create or load a previous session must be selected. Otherwise, the annotation program cannot start.";

            }


            return is_started;


        }


        private void BackUp_PreviousSessions()
        {
            string fname;
            string fname_bk;

            
            fname = DataSessionName;
            fname_bk = DataSessionDir + "bk_" + SessionFileName;


            if (File.Exists(fname))
            {
                if (File.Exists(fname_bk))
                { File.Delete(fname_bk); }

                File.Copy(fname, fname_bk);
                File.Delete(fname); 
              
            }



        }


        private void SaveOutputSessionFile()
        {

            if (DataSessionDir.CompareTo(DataOutputDir) != 0)
            {
                string fname = DataOutputDir + SessionFileName;
                string fname_bk = DataOutputDir + "bk_" + SessionFileName;

                if (File.Exists(fname))
                {
                    if (File.Exists(fname_bk))
                    { File.Delete(fname_bk); }

                    File.Copy(fname, fname_bk);
                    File.Delete(fname);
                }

                if (File.Exists(DataSessionName))
                { File.Copy(DataSessionName, fname); }

            }
        }

        private void SessionFileToDataDir()
        {

            if (DataOutputDir.CompareTo(DataSessionDir) != 0)
            {
                string foutput = DataOutputDir + SessionFileName;
                string fname = DataSessionDir + SessionFileName;
                string fname_bk = DataSessionDir + "bk_" + SessionFileName;


                if (File.Exists(fname))
                {
                    if (File.Exists(fname_bk))
                    { File.Delete(fname_bk); }

                    File.Copy(fname, fname_bk);
                    File.Delete(fname);
                }

                if (File.Exists(foutput))
                { File.Copy(foutput, fname); }

            }
        }




        #endregion


        #region Status


        private void check_cell_status(int row)
        {
            int prev_row = row - 1;
            string tlabel;

            // check row status
            tlabel = dataGridView1.Rows[row].Cells[CINDEX.Status].Value.ToString();

            if ((tlabel.CompareTo(" ") == 0) && (row > 0))
            {
                // search back what should be the right status label
                next_tlabel = dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value.ToString();

                if ((next_tlabel.CompareTo("start") == 0) || (next_tlabel.CompareTo("start_on") == 0))
                {
                    dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start_on";
                }

            }
        }


        private int check_label_lock(bool is_unlocked, bool is_label_open, int row,
                                     int index_label, string cur_label, int open_row,
                                     string open_label)
        {
            string prev_label = " ";
            string prev_status = " ";
            int prev_row = row - 1;

            int result = -1;

            if (row > 0)
            {
                if (dataGridView1.Rows[prev_row].Cells[index_label].Value != null)
                { prev_label = dataGridView1.Rows[prev_row].Cells[index_label].Value.ToString(); }

                if (dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value != null)
                { prev_status = dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value.ToString(); }
            }

            if (is_label_open)
            {
                if (is_unlocked)
                {
                    if (cur_label.CompareTo(" ") != 0) // label no blank
                    {
                        if (cur_label.CompareTo(prev_label) != 0) // current label different to previous
                        {
                            if ((prev_status.CompareTo("start") == 0) ||
                                 (prev_status.CompareTo("start_on") == 0))
                            {

                                if (prev_label.CompareTo(" ") != 0)
                                {
                                    prev_row = row;

                                    //insert row above
                                    dataGridView1.Rows.Insert(prev_row, 1);


                                    // update row number, row++
                                    row = row + 1;

                                    // fill "end" in inserted row and close label
                                    fill_row(prev_row, 2, prev_label, row, CINDEX.category_label, "end", prev_row - 1, prev_row, true);
                                    result = 1;
                                }
                                else
                                {
                                    if (cur_label.CompareTo(open_label) != 0)
                                    {
                                        fill_row(prev_row, 2, open_label, row, CINDEX.category_label, "end", prev_row - 1, prev_row, false);
                                        result = 0;
                                    }

                                }
                            }

                        }
                    }
                }
            }

            return result;
        }


        private int set_status_forward(int start_row, int end_row, string row_label, int TypeFill, bool block, int t_open_row)
        {
            // TypeFill = 1 is simple combo
            // TypeFill = 2 is full combo
            // TypeFill = 3 is full combo & cleanup


            int error_row = 0;
            string search_label = "";

            // fill forwards
            for (int i = start_row; i <= end_row; i++)
            {

                // check row status
                search_label = dataGridView1.Rows[i].Cells[CINDEX.Status].Value.ToString();

                if ((i > start_row) || (block == false))
                {
                    cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[i].Cells[CINDEX.category_label];

                    if (TypeFill == 1)
                    {
                        cellComboBox.Items.Clear();
                        cellComboBox.Items.Add(" ");
                        cellComboBox.Items.Add(row_label);
                    }
                    else if ((TypeFill == 2) || (TypeFill == 3))
                    {
                        cellComboBox.Items.Clear();

                        if (CINDEX.category_label == C1.category_label)
                        {
                            for (int j = 0; j < list_category_1.Count; j++)
                            { cellComboBox.Items.Add(list_category_1[j]); }
                        }
                        else if (CINDEX.category_label == C2.category_label)
                        {
                            for (int j = 0; j < list_category_2.Count; j++)
                            { cellComboBox.Items.Add(list_category_2[j]); }
                        }
                    }
                }




                if (search_label.CompareTo("start") == 0)
                {
                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = -1;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = -1;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " ";

                    }
                    else
                    {
                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = "Start";
                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = row_label;

                    }
                }
                else if (search_label.CompareTo("start_on") == 0)
                {
                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " ";

                    }
                    else
                    {
                        //dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = t_open_row;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = " ";

                    }

                }
                else if (search_label.CompareTo(" ") == 0)
                {

                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start_on";

                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " ";
                    }
                    else
                    {
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start_on";
                        //dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;

                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = t_open_row;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = end_row;
                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " ";

                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = " ";

                    }

                }
                else if (search_label.CompareTo("end") == 0)
                {

                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = i;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = " ";
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " ";
                    }
                    else
                    {
                        //dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[CINDEX.StartID].Value = t_open_row;

                        dataGridView1.Rows[i].Cells[CINDEX.EndID].Value = i;

                        dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = "End";

                        dataGridView1.Rows[i].Cells[CINDEX.category_label].Value = row_label;

                    }

                    if (i != end_row)
                    {
                        error_row = -1;
                        break;
                    }
                }

            }//ends for

            return error_row;
        }


        private void set_ComboBox(DataGridViewComboBoxCell combo, int row, int index_label, int fill_type, string rlabel)
        {

            combo = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[index_label];


            if (fill_type == 1) // simple
            {
                if ((rlabel.CompareTo(" ") != 0) &&
                    (rlabel.CompareTo("") != 0))
                {
                    combo.Items.Clear();
                    combo.Items.Add(" ");
                    combo.Items.Add(rlabel);
                }
                else //full
                {
                    combo.Items.Clear();

                    if (index_label == C1.category_label)
                    {
                        for (int j = 0; j < list_category_1.Count; j++)
                        { combo.Items.Add(list_category_1[j]); }

                        #region commented 
                        /*
                         * if (SessionPart == 1)
                        {
                            for (int j = 0; j < list_category_1.Count; j++)
                            { combo.Items.Add(list_category_1[j]); }
                        }
                        else if (SessionPart == 2)
                        {
                            for (int j = 0; j < list_category_2.Count; j++)
                            { combo.Items.Add(list_category_2[j]); }
                        }
                         */
                        #endregion 


                    }
                    else if (index_label == C2.category_label)
                    {
                        for (int j = 0; j < list_category_2.Count; j++)
                        { combo.Items.Add(list_category_2[j]); }
                    }


                }
            }
            else //if (fill_type == 2) //full
            {
                combo.Items.Clear();

                if (index_label == C1.category_label)
                {
                    for (int j = 0; j < list_category_1.Count; j++)
                    { combo.Items.Add(list_category_1[j]); }
                }
                else if (index_label == C2.category_label)
                {
                    for (int j = 0; j < list_category_2.Count; j++)
                    { combo.Items.Add(list_category_2[j]); }
                }

            }

        }


        #endregion


        #region Search

        private int search_start_backwards(int row)
        {
            int prev_row = row - 1;
            int start_row = -1;
            string search_label = " ";

            // search backwards
            while (prev_row > start_row)
            {
                // check row status
                if (dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value == null)
                { dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value = " "; }
                else
                { search_label = dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value.ToString(); }

                if (search_label.CompareTo("start") == 0)
                {
                    start_row = prev_row;
                    prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo("start_on") == 0)
                {
                    prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo(" ") == 0)
                {
                    // dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value = "start_on";  
                    prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo("end") == 0)
                {
                    start_row = prev_row + 1;
                    dataGridView1.Rows[start_row].Cells[CINDEX.Status].Value = "start";

                    dataGridView1.Rows[start_row].Cells[CINDEX.StartEnd].Value = "Start";
                    dataGridView1.Rows[start_row].Cells[CINDEX.StartID].Value = start_row;
                }
            }

            return start_row;
        }

        private int search_end_backwards(int row)
        {
            int prev_row = row - 1;
            int end_row = -1;
            string search_label = " ";

            // search backwards
            while ((prev_row > end_row) && (prev_row > -1))
            {

                // check row status
                if (dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value == null)
                { dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value = " "; }
                else
                { search_label = dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value.ToString(); }


                if (search_label.CompareTo("end") == 0)
                {
                    end_row = prev_row;
                    //prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo("start_on") == 0)
                {
                    //prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo(" ") == 0)
                {
                    // dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value = "start_on";  
                    //prev_row = prev_row - 1;
                }

                prev_row = prev_row - 1;
            }

            return end_row;
        }


        private int search_start_forward(int row, int max_rows)
        {
            int start_row = row;
            string search_label = " ";

  
            // search backwards
            for (int i = row; i < max_rows; i++)
            {

                //========== check row status  ===================================
                if (dataGridView1.Rows[i].Cells[CINDEX.Status].Value == null)
                { dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " "; }

                #region commented
                //Commented to be more robust to errors & replaced with function below
               // else
                // { search_label = dataGridView1.Rows[i].Cells[CINDEX.Status].Value.ToString(); }
                #endregion


                //========== check row start/end label  ===================================
                if (dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value == null)
                { dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " "; }
                else
                { search_label = dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value.ToString(); }


                if (i < (max_rows - 1))
                {
                    #region commented
                    /*if (search_label.CompareTo(" ") == 0)
                    {
                        // this line was commented from before
                        //dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start_on";
                    }
                    //else if (search_label.CompareTo("start") == 0)
                    */
                    #endregion

                    if (search_label.CompareTo("Start") == 0)
                    {
                        start_row = i;
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start"; 
                        break;
                    }

                }
                else if (start_row == row)
                {
                    // check if I need to add "End" label
                    start_row = i;

                }


            }//ends for

            return start_row;
        }


        private int search_end_forward(int row, int max_rows)
        {
            int end_row = row;
            string search_label = " ";

            // search backwards
            for (int i = row; i < max_rows; i++)
            {

                //========================== check row status =============================
                if (dataGridView1.Rows[i].Cells[CINDEX.Status].Value == null)
                {   dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " "; }

                #region commented
                //Commented to make the code more robust
                //else
                //{ search_label = dataGridView1.Rows[i].Cells[CINDEX.Status].Value.ToString(); }
                #endregion commented


                //========================== check row label  =============================
                if (dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value == null)
                { dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value = " "; }
                else
                { search_label = dataGridView1.Rows[i].Cells[CINDEX.StartEnd].Value.ToString(); }



                if (i < (max_rows - 1))
                {
                    
                    #region  commented
                    /*
                    if (search_label.CompareTo(" ") == 0)
                    {
                       // This line was commneted from before 
                       // //dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start_on";
                    }
                    else if (search_label.CompareTo("end") == 0)
                    */
                    #endregion commneted

                    if (search_label.CompareTo("End") == 0)
                     {
                        end_row = i;
                        dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "end";
                        break;
                    }

                }
                else if (end_row == row)
                {
                    // check if I need to add "End" label
                    end_row = i;
                }


            }//ends for

            return end_row;
        }

        private int search_end_start_backwards(int row)
        {
            int prev_row = row - 1;
            int end_row = -1;
            string search_label = " ";

            // search backwards
            while ((prev_row > end_row) && (prev_row > -1))
            {

                // check row status
                if (dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value == null)
                { dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value = " "; }
                else
                { search_label = dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value.ToString(); }


                if (search_label.CompareTo("end") == 0)
                {
                    end_row = prev_row;
                    //prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo("start_on") == 0)
                {
                    //prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo(" ") == 0)
                {
                    // dataGridView1.Rows[prev_row].Cells[CINDEX.Status].Value = "start_on";  
                    //prev_row = prev_row - 1;
                }
                else if (search_label.CompareTo("start") == 0)
                {
                    // start was found before, the end is missing
                    end_row = prev_row - 1;
                }
                prev_row = prev_row - 1;
            }

            return end_row;
        }


        private int search_open_row_backwards(int row)
        {
            int open_row = search_end_start_backwards(row) + 1;

            while (open_row < row)
            {
                if (dataGridView1.Rows[open_row].Cells[CINDEX.Status].Value.ToString().CompareTo("start") == 0)
                {

                    break;
                }
                else
                {
                    open_row = open_row + 1;

                }
            }

            return open_row;
        }

        private int search_close_row_forward(int row, int maxrows, int open_row, bool is_label_open)
        {
            int next_end;
            int next_start;
            int next;

            string next_status = " ";



            next_start = search_start_forward(row + 1, maxrows);  // serch for the next start label after this row
            next_end = search_end_forward(row + 1, maxrows);      // search for the next end label after this row


           

            if (next_start <= next_end)
            { next = next_start; }
            else
            { next = next_end; }



            // check that is not end of list 
            if (next < maxrows)
            {
                next_status = dataGridView1.Rows[next].Cells[CINDEX.Status].Value.ToString();

                if (is_label_open == true)
                {
                    if (next_status.CompareTo("start") == 0)
                    { // flag error, status unexpected, need to insert "end" first
                        next = next - 1;
                    }


                }
                else
                {
                    if (next_status.CompareTo("start") == 0)
                    {
                        next = next - 1;
                    }
                }
            }


            return next;
        }



        #endregion


        #region Events

        private void dataGridView1_RowEnter(object sender, DataGridViewCellEventArgs e)
        {
            if (dataGridView1.Focused)
            {
                current_row = e.RowIndex;
                label_play.Text = " ";

            }
        }

        private void dataGridView1_CellEnter(object sender, DataGridViewCellEventArgs e)
        {

            if (dataGridView1.Focused)
            {
                prev_cellStyle = cur_cellStyle;

                if (prev_cellStyle != null)
                {
                    prev_cellStyle.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
                }


                cur_cellStyle = dataGridView1.Columns[e.ColumnIndex].DefaultCellStyle;
                if (cur_cellStyle != null)
                {
                    cur_cellStyle.SelectionBackColor = System.Drawing.Color.Orange;
                }

                current_column = e.ColumnIndex;


            }


        }



        private void dataGridView1_CellValueChanged(object sender, DataGridViewCellEventArgs e)
        {

            if (dataGridView1.Focused)
            {

                int column = e.ColumnIndex;
                int row = e.RowIndex;
                nrows = dataGridView1.Rows.Count;

                ProcessAction(column, row);



            }// finish if focused
            else
            {
                if (is_data_grid_loaded)
                {
                    if (dataGridView1.Rows[e.RowIndex].Cells[e.ColumnIndex].Selected)
                    {


                        int column = e.ColumnIndex;
                        int row = e.RowIndex;
                        nrows = dataGridView1.Rows.Count;

                        ProcessAction(column, row);

                    }
                }

            }





        }




        private void dataGridView1_DataError(object sender, DataGridViewDataErrorEventArgs e)
        {
            e.Cancel = true;

        } //finish class


        private void FormAnnotation_Load(object sender, EventArgs e)
        {
            //-----


            this.panel_controls_2.Left = (int)System.Math.Round(0.5 * (this.Width - this.panel_controls_2.Width));
            this.panel_controls_1.Left = (int)System.Math.Round(0.5 * (this.Width - this.panel_controls_1.Width));

            this.dataGridView1.Left = (int)System.Math.Round(0.025 * this.Width);
            this.dataGridView1.Width = (int)System.Math.Round(0.95 * this.Width);
            //this.dataGridView1.Height = (int)System.Math.Round(0.60 * this.Height);
            this.dataGridView1.Height = this.Height - panel_controls_2.Height - 100;

            //textBox_instructions_2.Text = "Please provide a valid path for the audio and protocol files, then click Start. \n If the session file field is left blank, an annotation session file will be created automatically. \n An existing session file can be provided or a new session file name can be specified. ";
            //textBox_instructions_1.ForeColor = System.Drawing.Color.YellowGreen;
        }


        private void FormAnnotation_FormClosing(object sender, FormClosingEventArgs e)
        {
            if (panel_controls_2.Visible && !checkBox_ExitWithoutSaving.Checked)
            { SaveCurrentSessionToFile(); }
        }




        private void FormAnnotation_SizeChanged(object sender, EventArgs e)
        {
            this.panel_controls_2.Left = (int)System.Math.Round(0.5 * (this.Width - this.panel_controls_2.Width));
            this.panel_controls_1.Left = (int)System.Math.Round(0.5 * (this.Width - this.panel_controls_1.Width));

            this.dataGridView1.Left = (int)System.Math.Round(0.025 * this.Width);

            this.dataGridView1.Width = (int)System.Math.Round(0.95 * this.Width);
            //this.dataGridView1.Height = (int)System.Math.Round(0.60 * this.Height);
            this.dataGridView1.Height = this.Height - panel_controls_2.Height - 100;
        }


        private void dataGridView1_KeyDown(object sender, KeyEventArgs e)
        {
            Keys key = e.KeyCode;

            if (key == Keys.F1)
            {
                PlayFile(current_row);
            }


        }



        #endregion


        #region User Actions


        private void ProcessAction(int column, int row)
        {
            try
            {

                if (((column == ((int)C1.category_label)) ||
                       (column == ((int)C2.category_label))) &&
                     (is_busy == 0))
                {
                    is_busy = 1;
                    ProcessCategory(column, row);
                    is_busy = 0;

                }// ends "is column category" 
                else if (((column == ((int)C1.Lock)) ||
                            (column == ((int)C2.Lock))) &&
                          (is_busy == 0))
                {
                    is_busy = 1;
                    ProcessCategory_Lock(column, row);
                    is_busy = 0;

                }
                else if (((column == ((int)C1.StartEnd)) ||
                          (column == ((int)C2.StartEnd))) &&
                         (is_busy == 0))
                {

                    is_busy = 1;
                    ProcessCategory_StartEnd(column, row);
                    is_busy = 0;
                }
                else if ( ( column == ((int)C1.TimeMS)) &&
                          (is_busy == 0))
                {
                    is_busy = 1;
                    DateTime mytime = DateTime.Parse(dataGridView1.Rows[row].Cells[C1.TimeMS].Value.ToString());
                    dataGridView1.Rows[row].Cells[C1.Time_Label].Value = String.Format("{0:T}",mytime);
                    is_busy = 0;

                }


            }// finish try
            catch
            {

                if (is_busy == 1)
                {
                    //Handle Null Reference to this field
                    if( dataGridView1.Rows[row].Cells[C1.category_label].Value != null)
                    {
                        if (dataGridView1.Rows[row].Cells[C1.category_label].Value.ToString().CompareTo(" ") != 0)
                        { is_busy = 0; }
                    }

                    if (dataGridView1.Rows[row].Cells[C2.category_label].Value != null)
                    {
                        if (dataGridView1.Rows[row].Cells[C2.category_label].Value.ToString().CompareTo(" ") != 0)
                        { is_busy = 0; }
                    }

                }

                //System.Console.WriteLine("Data Error Event");   
            }



        }


        private void ProcessCategory(int column, int row)
        {

            COLUMN_STATUS CStatus = new COLUMN_STATUS(column, row);
            GetCategory_Status(column, row, out CStatus);

            row = CStatus.row;

            bool is_label_open = CStatus.is_label_open;
            bool is_unlocked = CStatus.is_unlocked;

            string end_label = CStatus.end_label;
            string start_label = CStatus.start_label;

            int open_row = CStatus.open_row;
            int close_row = CStatus.close_row;

            string tlabel = CStatus.tlabel;
            string status_tlabel = CStatus.status_tlabel;




            if (is_label_open == false)
            {

                #region label not opened


                if (end_label.CompareTo(" ") == 0) //end label blank
                {
                    if (tlabel.CompareTo(" ") == 1) //current label no blank
                    {
                        dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";
                        dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                        dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "Start";


                        dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = close_row;

                        // set type combo to state 4 == do not change
                        // before 1
                        if (set_status_forward(open_row, close_row, tlabel, 4, true, open_row) == -1)
                        {
                            System.Console.WriteLine("Error, end label was found before");
                        }

                    }
                    else //blank 
                    {
                        dataGridView1.Rows[row].Cells[CINDEX.Status].Value = " ";
                        dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = -1;
                        dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";

                        dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = -1;

                        // cleanup
                        // set type combo to state 4 == do not change
                        // before 3
                        if (set_status_forward(open_row, close_row, tlabel, 3, false, open_row) == -1)
                        { System.Console.WriteLine("Error, end label was found before"); }

                    }
                }
                else //end_label not blank
                {
                    if (status_tlabel.CompareTo("start") == 0)
                    {
                        if (tlabel.CompareTo(" ") == 1) //no blank
                        {
                            dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";


                            dataGridView1.Rows[close_row].Cells[CINDEX.Status].Value = "end";
                            dataGridView1.Rows[close_row].Cells[CINDEX.category_label].Value = tlabel;

                            // set type combo to state 4 == do not change
                            // before 1
                            if (set_status_forward(open_row, close_row, tlabel, 4, true, open_row) == -1)
                            { System.Console.WriteLine("Error, end label was found before"); }


                        }
                        else //blank
                        {

                            dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";
                            dataGridView1.Rows[row].Cells[CINDEX.category_label].Value = " ";

                            if (row != open_row)
                            {
                                dataGridView1.Rows[open_row].Cells[CINDEX.StartEnd].Value = " ";
                                dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value = " ";
                            }

                            dataGridView1.Rows[close_row].Cells[CINDEX.StartEnd].Value = " ";
                            dataGridView1.Rows[close_row].Cells[CINDEX.category_label].Value = " ";



                            // cleanup 
                            // set type combo to state 4 == do not change
                            // before 3
                            if (set_status_forward(open_row, close_row, tlabel, 3, false, open_row) == -1)
                            {
                                System.Console.WriteLine("Error, end label was found before");
                            }

                        }

                    }
                    else
                    {

                        // this start needs to stop with other start
                        // end label is incorrect, should be " "
                        // System.Console.WriteLine("This case needs to be considered");

                        if (tlabel.CompareTo(" ") != 0) //no blank
                        {
                            dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";


                            dataGridView1.Rows[close_row].Cells[CINDEX.Status].Value = "end";
                            dataGridView1.Rows[close_row].Cells[CINDEX.category_label].Value = tlabel;

                            // set type combo to state 4 == do not change
                            // before 1
                            //if (set_status_forward(open_row, close_row, tlabel, 4, true, open_row) == -1)
                            if (set_status_forward(row, close_row, tlabel, 4, true, open_row) == -1)
                            {
                                System.Console.WriteLine("Error, end label was found before");
                            }
                        }
                        else //blank
                        {

                            dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";
                            dataGridView1.Rows[row].Cells[CINDEX.category_label].Value = " ";

                            if (row != open_row)
                            {
                                dataGridView1.Rows[open_row].Cells[CINDEX.StartEnd].Value = " ";
                                dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value = " ";
                            }

                            dataGridView1.Rows[close_row].Cells[CINDEX.StartEnd].Value = " ";
                            dataGridView1.Rows[close_row].Cells[CINDEX.category_label].Value = " ";


                            // cleanup
                            // set type combo to state 4 == do not change
                            // before 3
                            if (set_status_forward(open_row, close_row, tlabel, 3, false, open_row) == -1)
                            {
                                System.Console.WriteLine("Error, end label was found before");
                            }

                        }


                    }
                }

                #endregion

            }
            else //is_label_open == 1
            {

                #region label opened

                if (end_label.CompareTo(" ") == 0)
                {
                    if (tlabel.CompareTo(" ") == 0) // blank
                    {
                        dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start_on";
                        dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                        dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = -1;

                        if (dataGridView1.Rows[row + 1].Cells[CINDEX.Status].Value.ToString().CompareTo("start") != 0) //start is not next
                        {
                            //close_row = search_close_row_forward(row, nrows);
                            start_label = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString();


                            // set type combo to state 4 == do not change
                            //before 1
                            if (set_status_forward(row + 1, close_row, start_label, 4, false, open_row) == -1)
                            {
                                System.Console.WriteLine("Error, end label was found before");
                            }
                        }


                    }
                    else
                    {
                        start_label = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString();

                        if (start_label.CompareTo(tlabel) == 0)
                        {


                            if (status_tlabel.CompareTo("start") != 0) //different to start
                            {
                                // set the end
                                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "end";
                                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "End";
                                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = row;

                                // set type combo to state 4 == do not change
                                // before 3
                                if (set_status_forward(row + 1, close_row, "", 3, false, row + 1) == -1)
                                {
                                    System.Console.WriteLine("Error, end label was found before");
                                }

                            }
                            else
                            {
                                // This needs to be considered !!!!
                                System.Console.WriteLine("This case needs to be considered");
                            }
                        }
                        else
                        {
                            //set the right labels in the combo
                            // set type combo to state 4 == do not change
                            // before 1
                            if (set_status_forward(open_row, close_row, start_label, 4, true, open_row) == -1)
                            {
                                System.Console.WriteLine("Error, end label was found before");
                            }
                        }
                    }// ends tlabel "no blank" endlabel " "
                } // ends end label " "
                else
                {
                    if (tlabel.CompareTo(" ") == 0) // blank
                    {
                        dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start_on";
                        dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                        dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = " ";
                        dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = close_row;
                    }
                    else // if no blank
                    {
                        //set end
                        start_label = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString();

                        if (start_label.CompareTo(tlabel) == 0)
                        {
                            if (row == close_row) //is this the end?
                            {
                                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "end";
                                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "End";
                                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = row;
                            }
                            else if (row < close_row)
                            {
                                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "end";
                                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = open_row;
                                dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "End";
                                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = row;

                                //cleanup the rest
                                // if row label == close label, clean the close label
                                // if labels are different, clomplete 
                                dataGridView1.Rows[row + 1].Cells[CINDEX.Status].Value = "start";
                                dataGridView1.Rows[close_row].Cells[CINDEX.Status].Value = "end";

                                // set type combo to state 4 == do not change
                                // before 3
                                if (set_status_forward(row + 1, close_row, "", 3, false, row + 1) == -1)
                                {
                                    System.Console.WriteLine("Error, end label was found before");
                                }
                            }
                            else
                            {
                                System.Console.WriteLine("Error, end label was found before");
                            }
                        }
                    }
                }

                #endregion


            }// ends "is label open == 1"

            //is_busy = 0;
            //tlabel = " ";
            //status_tlabel = " ";


        }


        private void GetCategory_Status(int column, int row, out COLUMN_STATUS status)
        {


            bool is_unlocked = false;
            bool is_label_open = true;


            status.tlabel = dataGridView1.Rows[row].Cells[column].Value.ToString();


            if (column == (C1.category_label))
            { CINDEX.SetValues(1); }
            else if (column == (C2.category_label))
            { CINDEX.SetValues(2); }


            if (dataGridView1.Rows[row].Cells[CINDEX.Lock].Value != null)
            { is_unlocked = (bool)dataGridView1.Rows[row].Cells[CINDEX.Lock].Value; }

            status.status_tlabel = dataGridView1.Rows[row].Cells[CINDEX.Status].Value.ToString();


            status.open_row = search_open_row_backwards(row);


            if ((status.open_row == row) || (row == 0))
            { is_label_open = false; }


            status.start_label = dataGridView1.Rows[status.open_row].Cells[CINDEX.category_label].Value.ToString();


            if (is_unlocked == true)
            {

                int result = check_label_lock(is_unlocked, is_label_open, row, CINDEX.category_label,
                                               status.tlabel, status.open_row, status.start_label);

                if (result > -1)
                {
                    //Update open_row value
                    if (result == 0)
                    {
                        status.open_row = row;
                        is_label_open = false;
                        status.start_label = status.tlabel;
                    }
                    else if (result == 1)
                    {
                        status.open_row = row + 1;
                        is_label_open = false;
                        status.start_label = status.tlabel;

                        row = row + 1;
                        nrows = dataGridView1.Rows.Count;
                    }
                }
            }



            status.close_row = search_close_row_forward(row, nrows, status.open_row, is_label_open);


            if ((is_label_open == false) && (status.tlabel.CompareTo(" ") != 0))
            {
                if (status.close_row >= nrows)
                {
                    status.close_row = add_end_row(row + 1, out nrows, status.tlabel, CINDEX.category_label, status.open_row, false);
                }
                else if (status.close_row <= status.open_row)
                {
                    // if label needs to be closed, because "end" or "start_on"
                    // perhaps do not work when the end row is separated several lines from open row
                    status.close_row = add_end_row(row + 1, out nrows, status.tlabel, CINDEX.category_label, status.open_row, true);
                }
            }

            if (status.close_row >= nrows)
            {
                status.close_row = nrows - 1;
            }

            if (dataGridView1.Rows[status.close_row].Cells[CINDEX.Status].Value == null)
            {
                dataGridView1.Rows[status.close_row].Cells[CINDEX.Status].Value = " ";
            }
            else if ((status.close_row < nrows) &&
                     (dataGridView1.Rows[status.close_row].Cells[CINDEX.Status].Value.ToString().CompareTo("start") == 0))
            {
                status.close_row = add_end_row(row + 1, out nrows, status.tlabel, CINDEX.category_label, status.open_row, true);
            }


            if (dataGridView1.Rows[status.close_row].Cells[CINDEX.category_label].Value == null)
            { dataGridView1.Rows[status.close_row].Cells[CINDEX.category_label].Value = " "; }

            status.end_label = dataGridView1.Rows[status.close_row].Cells[CINDEX.category_label].Value.ToString();

            // update fields before going out
            status.column = column;
            status.row = row;

            status.is_unlocked = is_unlocked;
            status.is_label_open = is_label_open;

        }



        private void ProcessCategory_Lock(int column, int row)
        {

            bool is_unlocked = false;
            int open_row = row;
            string tlabel = " ";


            if (column == (C1.Lock))
            { CINDEX.SetValues(1); }
            else if (column == (C2.Lock))
            { CINDEX.SetValues(2); }


            if (dataGridView1.Rows[row].Cells[CINDEX.StartID].Value != null)
            {
                if (dataGridView1.Rows[row].Cells[CINDEX.StartID].Value.GetType().Equals(typeof(int)) == false)
                { dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = Convert.ToInt32(dataGridView1.Rows[row].Cells[CINDEX.StartID].Value.ToString()); }

                open_row = (int)dataGridView1.Rows[row].Cells[CINDEX.StartID].Value;
            }

            if (dataGridView1.Rows[row].Cells[CINDEX.Lock].Value != null)
            {
                is_unlocked = (bool)dataGridView1.Rows[row].Cells[CINDEX.Lock].Value;
            }

            if (is_unlocked) // allow select any category
            {
                // set type combo to state 4 == do not change
                //before 2
                set_ComboBox(cellComboBox, row, CINDEX.category_label, 4, "");
            }
            else // set combo to simple == 1
            {
                if (dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value != null)
                { tlabel = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString(); }

                // set type combo to state 4 == do not change
                // before 1
                set_ComboBox(cellComboBox, row, CINDEX.category_label, 4, tlabel);
            }



        }



        private void ProcessCategory_StartEnd(int column, int row)
        {


            string prev_status_label = " ";
            string status_label = " ";
            string next_label = " ";
            string start_label = " ";
            string end_label = " ";

            int next_end = row + 1;


            if (column == (C1.StartEnd))
            { CINDEX.SetValues(1); }
            else if (column == (C2.StartEnd))
            { CINDEX.SetValues(2); }


            #region code

            status_label = dataGridView1.Rows[row].Cells[column].Value.ToString();

            if (status_label.CompareTo("Start") == 0)
            {
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";
                dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = row;


            }
            else if (status_label.CompareTo("End") == 0)
            {
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "end";
                dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = row;

                if (row > 0)
                {
                    // search the start backwards (update all cells)
                    if (dataGridView1.Rows[row - 1].Cells[CINDEX.category_label].Value != null)
                    { start_label = dataGridView1.Rows[row - 1].Cells[CINDEX.category_label].Value.ToString(); }

                    if (dataGridView1.Rows[row].Cells[CINDEX.category_label].Value != null)
                    { end_label = dataGridView1.Rows[row].Cells[CINDEX.category_label].Value.ToString(); }

                    if (dataGridView1.Rows[row + 1].Cells[CINDEX.category_label].Value != null)
                    { next_label = dataGridView1.Rows[row + 1].Cells[CINDEX.category_label].Value.ToString(); }


                    if (start_label.CompareTo(end_label) != 0)
                    {
                        // This code can be compressed in a function

                        if (dataGridView1.Rows[row - 1].Cells[CINDEX.Status].Value != null)
                        { prev_status_label = dataGridView1.Rows[row - 1].Cells[CINDEX.Status].Value.ToString(); }

                        if (prev_status_label.CompareTo("end") == 0)
                        {
                            //insert a start
                            add_start_row(row, out nrows, end_label, CINDEX.category_label, row + 1, true);

                            next_end = row + 2;

                            if (next_end < nrows)
                            { next_end = search_close_row_forward(next_end, nrows, next_end, false); }
                            else
                            { next_end = nrows - 1; }


                            if (cleanup_forward(row + 2, next_end, " ") == -1)
                            { label_play.Text = "Cleanup was not finished successfully. Please check annotations."; }

                        }
                        else if (prev_status_label.CompareTo("start") == 0)
                        {
                            // check start-end labels are similar
                            // if similar do nothing
                            // if not similar, set label to start label, CINDEX combo and sent message
                            set_ComboBox(cellComboBox, row, CINDEX.category_label, 1, start_label);

                            dataGridView1.Rows[row].Cells[CINDEX.category_label].Value = start_label;
                            label_play.Text = "END of label was set to open START label. START/END labels should match. To modify it, change START label.";

                        }
                        else if (prev_status_label.CompareTo(" ") == 0)
                        {
                            //check if the label is close
                            // search the start backwards (update all cells)
                            int open_row = search_open_row_backwards(row);

                            bool is_label_open = true;

                            if ((open_row == row) || (open_row == 0))
                            { is_label_open = false; }

                            int close_row = search_close_row_forward(row + 1, nrows, open_row, is_label_open);

                            if (close_row >= nrows)
                            { close_row = nrows - 1; }
                            else if (close_row <= open_row)
                            {
                                close_row = row + 1;
                            }

                            if (is_label_open == false)
                            {
                                // this end label is wrong, 
                                // only start is possible if next_end > row

                                //dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";
                                //dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "Start";

                                dataGridView1.Rows[row - 1].Cells[CINDEX.Status].Value = "start";
                                dataGridView1.Rows[row - 1].Cells[CINDEX.StartEnd].Value = "Start";

                                //if (set_status_forward(row, close_row, end_label, 1, true, open_row) == -1)
                                //{ System.Console.WriteLine("Error, end label was found before"); }

                                // the value of fill combo box can be set to 4/ combo boxes values are not being changed
                                // original value is set to 2
                                if (set_status_forward(row - 1, row, end_label, 4, true, open_row) == -1)
                                {
                                    System.Console.WriteLine("Error, end label was found before");
                                    label_play.Text = "The END Label could not be set. START/ERROR mismatch. To modified it, edit the START label.";
                                }

                            }
                        }
                        else if (prev_status_label.CompareTo("start_on") == 0)
                        {
                            // Check if label is open --> it is because it is start on
                            // if previous label which is open is different from the current label,
                            // close it in the previous row
                            int open_row = search_open_row_backwards(row);

                            bool is_label_open = true;

                            if ((open_row == row) || (open_row == 0))
                            { is_label_open = false; }

                            int close_row = search_close_row_forward(row + 1, nrows, open_row, is_label_open);

                            if (close_row >= nrows)
                            { close_row = nrows - 1; }
                            else if (close_row <= open_row)
                            {
                                close_row = row + 1;
                            }

                            if (is_label_open == true)
                            {
                                start_label = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString();
                                if (start_label.CompareTo(end_label) != 0)
                                {
                                    if (set_status_forward(open_row, row - 1, start_label, 2, true, open_row) == -1)
                                    {
                                        System.Console.WriteLine("Error, end label was found before");
                                        label_play.Text = "The open label could not be closed. To modified it, use the manual edit.";
                                    }
                                }
                            }

                            // Once previous label open is closed, add an start row and filled with the current label
                            //  update starID, close ID and number of rows + 1
                            prev_status_label = dataGridView1.Rows[row - 1].Cells[CINDEX.Status].Value.ToString();

                            //if (prev_status_label.CompareTo("end") == 0)
                            //{
                            //insert a start
                            add_start_row(row, out nrows, end_label, CINDEX.category_label, row + 1, true);

                            next_end = row + 2;

                            if (next_end < nrows)
                            { next_end = search_close_row_forward(next_end, nrows, next_end, false); }
                            else
                            { next_end = nrows - 1; }


                            if (cleanup_forward(row + 2, next_end, " ") == -1)
                            { label_play.Text = "Cleanup was not finished successfully. Please check annotations."; }
                            //}


                        }
                    }
                    else
                    {   // if previous label and current label are similar, check the status
                        // if status is start, don't do anything and set this to the end
                        // if status is end, check the open_label similar, if so clear previous row

                        if (dataGridView1.Rows[row - 1].Cells[CINDEX.Status].Value != null)
                        { prev_status_label = dataGridView1.Rows[row - 1].Cells[CINDEX.Status].Value.ToString(); }

                        if (prev_status_label.CompareTo("end") == 0)
                        {
                            int open_row = search_open_row_backwards(row - 1);

                            start_label = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString();

                            if (start_label.CompareTo(end_label) == 0)
                            {
                                // clear previous row
                                fill_row(row - 1, 2, " ", row - 1, CINDEX.category_label, "start_on", open_row, row, false);

                            }

                        }

                    }


                    // Make sure that next label is not similar to the current one
                    // if next label is similar, check that is not end
                    // if not end, leave it as it is
                    // if end, make it blank

                    // if current row and next row are similar
                    if (end_label.CompareTo(next_label) == 0)
                    {

                        if (dataGridView1.Rows[row + 1].Cells[CINDEX.Status].Value != null)
                        { prev_status_label = dataGridView1.Rows[row + 1].Cells[CINDEX.Status].Value.ToString(); }

                        if (prev_status_label.CompareTo("end") == 0)
                        {
                            // search the start backwards (update all cells)
                            int open_row = search_open_row_backwards(row);
                            bool is_label_open = true;

                            if ((open_row == row) || (open_row == 0))
                            { is_label_open = false; }

                            next_end = search_close_row_forward(row, nrows, open_row, is_label_open);

                            // search end forward 
                            if (is_label_open == false)
                            {
                                // this end label is wrong, 
                                // only start is possible if next_end > row
                                if ((next_end > row) && (next_end < nrows))
                                {
                                    end_label = dataGridView1.Rows[next_end].Cells[CINDEX.category_label].Value.ToString();

                                    dataGridView1.Rows[row].Cells[CINDEX.Status].Value = "start";
                                    dataGridView1.Rows[row].Cells[CINDEX.StartEnd].Value = "Start";
                                    dataGridView1.Rows[row].Cells[CINDEX.category_label].Value = end_label;

                                    label_play.Text = "The END Label could not be set. START/ERROR mismatch. To modified it, edit the START label.";
                                }

                            }

                        }
                    }

                }
            }
            else  // blank
            {
                // search start/end fwrd-backwards
                dataGridView1.Rows[row].Cells[CINDEX.Status].Value = " ";
                dataGridView1.Rows[row].Cells[CINDEX.category_label].Value = " ";

                //dataGridView1.Rows[row].Cells[CINDEX.StartID].Value = -1;
                //dataGridView1.Rows[row].Cells[CINDEX.EndID].Value = -1;
            }


            #endregion




        }




        #endregion


        #region XML



        public bool LoadActivityLabels()
        {
            bool is_file_found = false;

            string unknown_label = "unknown";
            bool unknow_label_exist = false;


            if (XmlSession == null)
            {
                XmlSession = new Session();
                CActivityList = new BindingList<ActivityList>();


                // Load the "ActivityLabelsRealtime.xml" file
                string labels_file_name = Folder_session + "wockets\\ActivityLabelsRealtime.xml";

                if (File.Exists(labels_file_name))
                {
                    is_file_found = true;

                    Activity[] activityArray;

                    XmlSession.FromXML(labels_file_name);


                    for (int i = 0; i < XmlSession.OverlappingActivityLists.Count; i++)
                    {
                        CActivityList.Add(XmlSession.OverlappingActivityLists[i]);

                        list_category_name.Add(CActivityList[i]._Name);



                        // only two activity categories can be loaded
                        if (i == 0)
                        {
                            #region Load First Category 

                            //extract the activity array
                            activityArray = CActivityList[i].ToArray();
                            
                            //add the blank possition
                            list_category_1.Add(" ");

                            //initialize unknown label flag
                            unknow_label_exist = false;
                            
                            for (int j = 0; j < CActivityList[i].Count; j++)
                            {
                                list_category_1.Add(activityArray[j]._Name);

                                if (activityArray[j]._Name.ToLower().CompareTo(unknown_label) == 0)
                                { unknow_label_exist = true; }
                            }

                            //If "unknown label" doesn't exist, added it
                            if (!unknow_label_exist)
                            { list_category_1.Add(unknown_label); }


                            #endregion 

                        }
                        else if (i == 1)
                        {

                            #region Load Second Category

                            activityArray = CActivityList[i].ToArray();
                            list_category_2.Add(" ");

                            //initialize unknown label flag
                            unknow_label_exist = false;
                            
                            for (int j = 0; j < CActivityList[i].Count; j++)
                            {   
                                list_category_2.Add(activityArray[j]._Name);

                                if (activityArray[j]._Name.ToLower().CompareTo(unknown_label) == 0)
                                { unknow_label_exist = true; }
                            }


                            //If "unknown label" doesn't exist, added it
                            if (!unknow_label_exist)
                            { list_category_2.Add(unknown_label); }

                            #endregion 

                        }

                    }

                }
            }


            return is_file_found;
        }



        //----------------------------------------------------------------------------
        // This function read the label values
        // It verifies that all the labels match
        // If the labels are correct, save the records to the appropiate xml format
        //----------------------------------------------------------------------------
        private int GenerateActivityLabels(out string summary_results)
        {
            int success = 0;
            summary_results = "";

            try
            {

              
                // Check if the labels list is incorrect,
                // return true, if something is wrong
                // return false, if all correct
                if (CheckLabelsList() == false)
                {
                    success = 1;

                    //check if labels are ok according to the Xml protocol
                    // return true, if everything correct
                    // return false, if an invalid value was found
                    if (CheckLabelsListWithXml(out summary_results))
                    {
                        success = 2;

                        // Load annotations
                        // return true, if the xml file was successfully generated
                        if (LoadLabelsListToXml())
                        {
                            success = 3;
                            label_play.Text = "The Xml annotation file has been generated.";
                        }
                        else
                        {
                            success = -3;
                            label_play.Text = "There was a problem generating the Xml annotation file. Please save your session and try again.";
                            
                        }
                    }
                    else
                    {
                        success = -2;
                        label_play.Text = "There are mismatches between your labels and the xml protocol. Please check the labels and end times highlighted. Red=Mistmatch --- Yellow=Problematic.";   
                    }
                }
                else
                {
                    success = -1;
                    label_play.Text = "There are label mismatches. Please check the fields highlighted (violet= check label start/end). After corrections, click the 'Generate Xml' button.";
                }

                //check if this affects the repaint of cells
                LabelsList_1.Clear();
                LabelsList_2.Clear();

                return success;
            }
            catch
            {
                label_play.Text = "Problems generating the Xml annotation file.";
                

                return 0;
            }


        }



        private bool CheckLabelsList()
        {
            int start_row, end_row, _category;
            string label_start, label_end;
            string start_time, end_time;
            string record_string;

            bool incorrect_records = false;

            nrows = dataGridView1.Rows.Count;

            // backup first
            if (File.Exists(DataSessionDir + "Data_Session.txt"))
            {
                if (File.Exists(DataSessionDir + "bk_Data_Session.txt"))
                { File.Delete(DataSessionDir + "bk_Data_Session.txt"); }

                File.Copy(DataSessionDir + "Data_Session.txt", DataSessionDir + "bk_Data_Session.txt");
                File.Delete(DataSessionDir + "Data_Session.txt");
            }

            //Create new output files
            TextWriter txw = new StreamWriter(DataSessionDir + "Data_Session.txt");
            txw.WriteLine(StartDate + ";" + EndDate + ";");

            LabelsList_1.Clear();
            LabelsList_2.Clear();



            // check that both columns labels are correct
            // If not, send the appropriate message to correct them

            #region check labels open-close
            // there are two categories
            for (int c = 1; c <= 2; c++)
            {
                // set category
                CINDEX.SetValues(c);

                //initialize variables
                start_row = 0;
                end_row = 0;
                _category = c - 1;

                label_start = "";
                label_end = "";

                start_time = "";
                end_time = "";

                record_string = "";


                //------------------
                // monitor this part because there is a potential problem
                start_row = search_start_forward(start_row, nrows);
                end_row = search_close_row_forward(start_row, nrows, start_row, true);
                //------------------

                
               

                while (end_row < nrows)
                {


                    label_start = dataGridView1.Rows[start_row].Cells[CINDEX.category_label].Value.ToString();
                    label_end = dataGridView1.Rows[end_row].Cells[CINDEX.category_label].Value.ToString();

                    //start_time = dataGridView1.Rows[start_row].Cells[CINDEX.Time_Label].Value.ToString();
                    //end_time = dataGridView1.Rows[end_row].Cells[CINDEX.Time_Label].Value.ToString();
                    start_time = dataGridView1.Rows[start_row].Cells[CINDEX.TimeMS].Value.ToString();
                    end_time = dataGridView1.Rows[end_row].Cells[CINDEX.TimeMS].Value.ToString();


                    // check if row seq. is correct
                    if (start_row < end_row)
                    {

                        // check if record is correct
                        if (label_start.CompareTo(label_end) == 0)
                        {
                            //write record to list
                            record_string = "ok" + ";" + start_row.ToString() + ";" + end_row.ToString() + ";" +
                                            start_time.ToString() + ";" + end_time.ToString() + ";" +
                                            label_start + ";" + list_category_name[_category] + ";" + _category.ToString();


                            txw.WriteLine(record_string);

                            if ( _category == 0 )
                            { LabelsList_1.Add(record_string); }
                            else if (  _category == 1  )
                            { LabelsList_2.Add(record_string); }



                            #region Repaint Cells
                            //------------------------------------------------
                            // Repaint Cells
                            //Here possibly affecting the repaint of the cells

                            int mrow = 0;

                            while (mrow < 2)
                            {
                                if (mrow == 0)
                                {
                                    prev_cellStyle = dataGridView1.Rows[start_row].Cells[CINDEX.category_label].Style;
                                    cur_cellStyle = dataGridView1.Rows[start_row].Cells[CINDEX.StartEnd].Style;
                                }
                                else if (mrow == 1)
                                {
                                    prev_cellStyle = dataGridView1.Rows[end_row].Cells[CINDEX.category_label].Style;
                                    cur_cellStyle = dataGridView1.Rows[end_row].Cells[CINDEX.StartEnd].Style;
                                }

                                mrow++;


                                if (prev_cellStyle != null)
                                {
                                    if (c == 1)
                                    {
                                        if (checkBox_SiglePassMode.Checked == false)
                                        {
                                            if (SessionPart == 1)
                                            {
                                                prev_cellStyle.BackColor = System.Drawing.Color.White;
                                                prev_cellStyle.ForeColor = System.Drawing.Color.Black;

                                                cur_cellStyle.BackColor = System.Drawing.Color.White;
                                                cur_cellStyle.ForeColor = System.Drawing.Color.Black;
                                            }
                                            else if (SessionPart == 2)
                                            {
                                                prev_cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                                                prev_cellStyle.ForeColor = System.Drawing.Color.DimGray;

                                                cur_cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                                                cur_cellStyle.ForeColor = System.Drawing.Color.DimGray;
                                            }
                                        }
                                        else
                                        {
                                            prev_cellStyle.BackColor = System.Drawing.Color.White;
                                            prev_cellStyle.ForeColor = System.Drawing.Color.Black;

                                            cur_cellStyle.BackColor = System.Drawing.Color.White;
                                            cur_cellStyle.ForeColor = System.Drawing.Color.Black;
                                        }

                                    }
                                    else if (c == 2)
                                    {

                                        if (checkBox_SiglePassMode.Checked == false)
                                        {
                                            if (SessionPart == 1)
                                            {
                                                prev_cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                                                prev_cellStyle.ForeColor = System.Drawing.Color.DimGray;

                                                cur_cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                                                cur_cellStyle.ForeColor = System.Drawing.Color.DimGray;
                                            }
                                            else if (SessionPart == 2)
                                            {
                                                prev_cellStyle.BackColor = System.Drawing.Color.White;
                                                prev_cellStyle.ForeColor = System.Drawing.Color.Black;

                                                cur_cellStyle.BackColor = System.Drawing.Color.White;
                                                cur_cellStyle.ForeColor = System.Drawing.Color.Black;
                                            }
                                        }
                                        else
                                        {
                                            prev_cellStyle.BackColor = System.Drawing.Color.White;
                                            prev_cellStyle.ForeColor = System.Drawing.Color.Black;

                                            cur_cellStyle.BackColor = System.Drawing.Color.White;
                                            cur_cellStyle.ForeColor = System.Drawing.Color.Black;
                                        }
                                    }
                                }

                            }


                            //-------------------------------------------------------
                            #endregion Repaint Cells





                            if ((end_row + 1) < nrows)
                            {
                                start_row = search_start_forward(end_row + 1, nrows);
                                end_row = search_close_row_forward(start_row, nrows, start_row + 1, true);
                            }
                            else
                            { end_row = end_row + 1; }


                        }
                        else
                        {
                            
                            incorrect_records = true;


                            // this probably affecting the repaint of cells
                            prev_cellStyle = dataGridView1.Rows[start_row].Cells[CINDEX.category_label].Style;
                            if (prev_cellStyle != null)
                            { prev_cellStyle.BackColor = System.Drawing.Color.Plum; }


                            cur_cellStyle = dataGridView1.Rows[end_row].Cells[CINDEX.category_label].Style;
                            if (cur_cellStyle != null)
                            { cur_cellStyle.BackColor = System.Drawing.Color.Plum; }




                            //write record to list
                            record_string = "no" + ";" + start_row.ToString() + ";" + end_row.ToString() + ";" +
                                            start_time.ToString() + ";" + end_time.ToString() + ";" +
                                            label_start + ";" + label_end + ";" + list_category_name[_category] + ";" + _category.ToString();

                            txw.WriteLine(record_string);


                            if (_category == 0)
                            { LabelsList_1.Add(record_string); }
                            else if (_category == 1)
                            { LabelsList_2.Add(record_string); }



                            //update variables
                            if ((end_row + 1) < nrows)
                            {
                                start_row = search_start_forward(end_row + 1, nrows);
                                
                                //Check if it is incorrect
                                //end_row = search_close_row_forward(start_row + 1, nrows, start_row + 1, true);
                                
                                end_row = search_close_row_forward(start_row , nrows, start_row, true);
                            
                            }
                            else
                            {
                                end_row = end_row + 1;
                            }


                        }



                    } 
                    // this is affecting the last row when there is not time label written
                    else if (start_row == end_row)
                    {
                        end_row = end_row + 1;

                        // still you have to check that record is correct
                    }
                    else
                    {
                        // check case when  start_row > end_row
                    }


                }
            }

            #endregion 




            // Close the Data Session file
            txw.Flush();
            txw.Close();


            return incorrect_records;

        }



       
        private bool CheckLabelsListWithXml(out string summary_results)
        {
            TextWriter summary_file_csv = null;
            TextWriter summary_file_html = null;

            bool Is_LabelsList_Valid = true;
            summary_results = "";

            string[] str_temp;

            try
            {
               
                DateTime start_time, end_time;
                TimeSpan ts, ts_start, ts_end, total_time, total_time_inv;
                string category, current_label, readline;
                
                //Create Summary Lists
                BindingList<string> List_Annotated = new BindingList<string>();
                BindingList<string> List_NoAnnotated = new BindingList<string>();
                BindingList<string> List_Invalid = new BindingList<string>();
                
                BindingList<TimeSpan> List_Time = new BindingList<TimeSpan>();
                BindingList<TimeSpan> List_Time_Inv = new BindingList<TimeSpan>();
               
                BindingList<string> List_Current_XML;


                //Create the files for summarizing results
                // Create the csv file
                if (File.Exists(Folder_audioannotation + "AnnotationSummary.csv"))
                { File.Delete(Folder_audioannotation + "AnnotationSummary.csv"); }

                summary_file_csv = new StreamWriter(Folder_audioannotation + "AnnotationSummary.csv");
                summary_file_csv.WriteLine("Label,Time(hh:mm:ss)");

                // Create the html file
                if (File.Exists(Folder_audioannotation + "AnnotationSummary.html"))
                { File.Delete(Folder_audioannotation + "AnnotationSummary.html"); }

                summary_file_html = new StreamWriter(Folder_audioannotation + "AnnotationSummary.html");
               
            
                summary_file_html.WriteLine("<table border=\"1\">\n");
                summary_file_html.WriteLine("<tr><td>Label</td><td>Time(hh:mm:ss)</td></tr>");



                // ---------- Load labels ------------------

                int count = 0;
                int index = 0;

                for (int c = 1; c <= 2; c++)
                {
                    //Initialize lists
                    List_Annotated.Clear();
                    List_NoAnnotated.Clear();
                    List_Invalid.Clear();
                    List_Time.Clear();
                    List_Time_Inv.Clear();

                    total_time = TimeSpan.Zero;
                    total_time_inv = TimeSpan.Zero;

                    //Indicate the category
                    if (c == 1)
                    {
                        count = LabelsList_1.Count;
                        List_Current_XML = list_category_1;
                        //category = "Postures";
                        category = list_category_name[0];

                    }
                    else
                    {
                        count = LabelsList_2.Count;
                        List_Current_XML = list_category_2;
                        //category = "Activities";
                        category = list_category_name[1];
                    }


                    //Read each item from the list
                    for (int i = 0; i < count; i++)
                    {
                        if (c == 1)
                        { readline = LabelsList_1[i]; }
                        else
                        { readline = LabelsList_2[i]; }


                        string[] tokens = readline.Split(';');

                        //Check the row has valid start/end times
                        if (tokens[0].CompareTo("ok") == 0)
                        {
                            current_label = tokens[5];

                            

                            //filter labels comming from blank rows
                            if (current_label.Trim().CompareTo("") != 0)
                            {


                                //Check if the label is valid according to the Xml protocol list 
                                //if not, flag the label as invalid
                                if (List_Current_XML.Contains(current_label))
                                {
                                    //Start Time
                                    str_temp = tokens[3].Split('.');

                                    start_time = DateTime.Parse(StartDate + " " + str_temp[0]);
                                    ts_start = (start_time - new DateTime(1970, 1, 1, 0, 0, 0));

                                    //Stop Time
                                    str_temp = tokens[4].Split('.');
                                   
                                    end_time = DateTime.Parse(EndDate + " " + str_temp[0]);
                                    ts_end = (end_time - new DateTime(1970, 1, 1, 0, 0, 0));

                                    ts = ts_end.Subtract(ts_start);


                                    total_time = total_time + ts;

                                        if (!List_Annotated.Contains(current_label))
                                        {
                                            List_Annotated.Add(current_label);
                                            List_Time.Add(ts);
                                        }
                                        else
                                        {
                                            index = List_Annotated.IndexOf(current_label);
                                            //ts_start = List_Time[index];
                                            //ts = ts + ts_start;
                                            List_Time[index] = ts + List_Time[index];
                                        }

                                    
                                    //Check if the total time spend on this label makes sense (greater than 0)
                                    //If so, add the label to the annotated list
                                    //Otherwise, highlighted as problematic and don't generate the xml file
                                    if ( ts.TotalSeconds == 0)
                                    {
                                        Is_LabelsList_Valid = false;

                                        #region  highlight label in yellow

                                        int iloop = 0;
                                        int irow = 0;

                                        while(iloop <2)
                                        {
                                           if(iloop == 0)
                                           {   //Highlight Start Row
                                               irow = Int32.Parse(tokens[1]);
                                           }
                                           else if(iloop == 1)
                                           {    //Highlight End Row
                                                irow = Int32.Parse(tokens[2]);
                                           }
                                           
                                           iloop++;


                                           if (c == 1)
                                           {
                                                dataGridView1.Rows[irow].Cells[C1.category_label].Style.BackColor = System.Drawing.Color.Khaki;
                                                dataGridView1.Rows[irow].Cells[C1.category_label].Style.ForeColor = System.Drawing.Color.DimGray;

                                                dataGridView1.Rows[irow].Cells[C1.StartEnd].Style.BackColor = System.Drawing.Color.Khaki;
                                                dataGridView1.Rows[irow].Cells[C1.StartEnd].Style.ForeColor = System.Drawing.Color.DimGray;
                                           }
                                            else if (c == 2)
                                            {
                                                dataGridView1.Rows[irow].Cells[C2.category_label].Style.BackColor = System.Drawing.Color.Khaki;
                                                dataGridView1.Rows[irow].Cells[C2.category_label].Style.BackColor = System.Drawing.Color.DimGray;

                                                dataGridView1.Rows[irow].Cells[C2.StartEnd].Style.BackColor = System.Drawing.Color.Khaki;
                                                dataGridView1.Rows[irow].Cells[C2.StartEnd].Style.ForeColor = System.Drawing.Color.DimGray;
                                            }

                                        }

                                        #endregion



                                    }
                                    

                                }
                                // if label not found in xml protocol, flag as invalid
                                else
                                {
                                    Is_LabelsList_Valid = false;

                                    #region higlight row in red
                                        int iloop = 0;
                                        int irow = 0;

                                        while (iloop < 2)
                                        {
                                            if (iloop == 0)
                                            {   //Highlight Start Row
                                                irow = Int32.Parse(tokens[1]);
                                            }
                                            else if (iloop == 1)
                                            {    //Highlight End Row
                                                irow = Int32.Parse(tokens[2]);
                                            }

                                            iloop++;

                                            if (c == 1)
                                            {
                                                dataGridView1.Rows[irow].Cells[C1.category_label].Style.BackColor = System.Drawing.Color.Tomato;
                                                dataGridView1.Rows[irow].Cells[C1.category_label].Style.ForeColor = System.Drawing.Color.White;

                                                dataGridView1.Rows[irow].Cells[C1.StartEnd].Style.BackColor = System.Drawing.Color.Tomato;
                                                dataGridView1.Rows[irow].Cells[C1.StartEnd].Style.ForeColor = System.Drawing.Color.White;
                                            }
                                            else if (c == 2)
                                            {
                                                dataGridView1.Rows[irow].Cells[C2.category_label].Style.BackColor = System.Drawing.Color.Tomato;
                                                dataGridView1.Rows[irow].Cells[C2.category_label].Style.BackColor = System.Drawing.Color.White;

                                                dataGridView1.Rows[irow].Cells[C2.StartEnd].Style.BackColor = System.Drawing.Color.Tomato;
                                                dataGridView1.Rows[irow].Cells[C2.StartEnd].Style.ForeColor = System.Drawing.Color.White;
                                            }

                                        }

                                    #endregion


                                    //Start Time
                                    str_temp = tokens[3].Split('.');

                                    start_time = DateTime.Parse(StartDate + " " + str_temp[0]);
                                    ts_start = (start_time - new DateTime(1970, 1, 1, 0, 0, 0));

                                    //Stop Time
                                    str_temp = tokens[4].Split('.');

                                    end_time = DateTime.Parse(EndDate + " " + str_temp[0]);
                                    ts_end = (end_time - new DateTime(1970, 1, 1, 0, 0, 0));


                                    ts = ts_end.Subtract(ts_start);
                                    total_time_inv = total_time_inv + ts;

                                    if (!List_Invalid.Contains(current_label))
                                    {
                                        List_Invalid.Add(current_label);
                                        List_Time_Inv.Add(ts);
                                    }
                                    else
                                    {
                                        index = List_Invalid.IndexOf(current_label);
                                        ts_start = List_Time_Inv[index];
                                        ts = ts + ts_start;
                                        List_Time_Inv[index] = ts;
                                    }
                                }

                            }
                            //else (if label == blank), do nothing
                            
                        }//if token ok

                    }//for labels list per category


                    //------------------------------------------
                    //Compute the No-Annotated Labels
                    //check for blank labels
                    foreach(string ilabel in List_Current_XML)
                    {
                        if (ilabel.Trim().CompareTo("") != 0)
                        {
                            if (!List_Annotated.Contains(ilabel))
                            {
                                List_NoAnnotated.Add(ilabel);
                            }
                        }
                        //else if(label == blank), do nothing
                    }


                    //------------------------------------------
                    // Write the summary of results to file
                    //-------------------------------------------
                    string font_color_open = "";
                    string font_color_close = "";

                    // Annotatated List
                    summary_file_csv.WriteLine("Annotated "+ category + ",");
                    summary_results = summary_results + "Annotated " + category + ":,," + "#" + ";";

                    summary_file_html.WriteLine("<tr bgcolor=\"#E6E6E6\">\n<td><strong>Annotated " + category + "</strong></td><td>&nbsp;</td></tr>");
                    
                    
                  
                    int it = 0;
                    foreach (string clabel in List_Annotated)
                    {
                        ts = List_Time[it];

                        // Save record to the correspondent session
                        summary_file_csv.WriteLine(clabel + "," + ts.ToString());
                        summary_file_html.WriteLine("<tr>\n<td>" + clabel + "</td><td>" + ts.ToString() + "</td></tr>");
                        summary_results = summary_results + clabel + "," + ts.ToString() + ";";
                        it++;
                    }

                    
                    summary_file_csv.WriteLine("Total Time Annotated "+ category + "," + total_time.ToString());
                    summary_file_csv.WriteLine("");

                    font_color_open = "<strong><font color=\"#4E8975\">";
                    font_color_close = "</font><strong>";
                    summary_file_html.WriteLine("<tr>\n<td>"+ font_color_open +"Total Time Annotated " + category + font_color_close +"</td>" +
                                                      "<td>"+ font_color_open + total_time.ToString() + font_color_close + "</td></tr>");
                    summary_file_html.WriteLine("<tr>\n<td>&nbsp;</td><td>&nbsp;</td></tr>");

                    summary_results = summary_results + "Total Time Annotated " + category + "," + total_time.ToString() + ",##;";
                    summary_results = summary_results +";";


                    // No Annotated List
                    summary_file_csv.WriteLine("No Annotated " + category + " in Xml Protocol,");
                    summary_file_html.WriteLine("<tr bgcolor=\"#E6E6E6\">\n<td><strong>No Annotated " + category + " in Xml Protocol</strong></td><td>&nbsp;</td></tr>");
                    summary_results = summary_results + "No Annotated " + category + " in Xml Protocol:,,#" + ";";

                    foreach (string jlabel in List_NoAnnotated)
                    {   summary_file_csv.WriteLine(jlabel);
                        summary_file_html.WriteLine("<tr>\n<td>" + jlabel + "</td><td>&nbsp;</td></tr>");
                        summary_results = summary_results + jlabel + ";";
                    }

                    summary_file_csv.WriteLine("");
                    summary_file_html.WriteLine("<tr>\n<td>&nbsp;</td><td>&nbsp;</td></tr>");
                    summary_results = summary_results + ";";

                    summary_file_csv.WriteLine("Invalid " + category + ",");
                    summary_file_html.WriteLine("<tr bgcolor=\"#E6E6E6\">\n<td><strong> Invalid " + category + "</strong></td><td>&nbsp;</td></tr>");
                    summary_results = summary_results + "Invalid " + category + ":,," + "#" + ";";

                    font_color_open = "<font color=\"#FA5858\">";
                    font_color_close = "</font>";

                    it = 0;
                    foreach (string klabel in List_Invalid)
                    {
                        ts = List_Time_Inv[it];

                        // Save record to the correspondent session
                        summary_file_csv.WriteLine(klabel + "," + ts.ToString());
                        summary_file_html.WriteLine("<tr>\n<td>" + font_color_open + klabel + font_color_close + "</td>" + 
                                                          "<td>" + font_color_open + ts.ToString() + font_color_close + "</td></tr>");
                        summary_results = summary_results + klabel + "," + ts.ToString() + ",###;";

                        it++;
                    }


                    summary_file_csv.WriteLine("Total Time Invalid " + category + "," + total_time_inv.ToString());
                    summary_file_csv.WriteLine("");


                    font_color_open = "<strong><font color=\"#FA5858\">";
                    font_color_close = "</font></strong>";
                    summary_file_html.WriteLine("<tr>\n<td>"+ font_color_open + "Total Time Invalid " + category + font_color_close+"</td>" + 
                                                "<td>"+ font_color_open + total_time_inv.ToString() + font_color_close + "</td></tr>");
                    summary_file_html.WriteLine("<tr>\n<td>&nbsp;</td><td>&nbsp;</td></tr>");

                    
                    summary_results = summary_results + "Total Time Invalid " + category + "," + total_time_inv.ToString() + ",#-;";
                    summary_results = summary_results + ";";
                    
                   //--------------------------------------------

                }//for each category label


               
                
                // Close summary file csv
                summary_file_csv.Flush();
                summary_file_csv.Close();


                // Close summary file csv
                summary_file_html.WriteLine("</table>");
                summary_file_html.Flush();
                summary_file_html.Close();





                return Is_LabelsList_Valid;
            }
            catch
            {
                Is_LabelsList_Valid = false;

                if (summary_file_csv != null)
                {
                    summary_file_csv.Flush();
                    summary_file_csv.Close();

                }


                if (summary_file_html != null)
                {
                    summary_file_html.Flush();
                    summary_file_html.Close();

                }


                
                return Is_LabelsList_Valid;
            }

        }



        //ArrayList records = new ArrayList();
        Annotation currentRecord;
        private bool LoadLabelsListToXml()
        {
            TextWriter intervals_file_xml = null;
            TextWriter intervals_file_csv = null;

            TextWriter intervals_file_xml_1 = null;
            TextWriter intervals_file_csv_1 = null;

            TextWriter intervals_file_xml_2 = null;
            TextWriter intervals_file_csv_2 = null; 

            Session XmlSession_1 = null;
            Session XmlSession_2 = null;


            try
            {
                string readline;
                DateTime start_time, end_time;
                TimeSpan ts;
                string category, current_label;


                #region generate an annotation file for each category


                // ----------backup and create output files ------------------

                // Annotation Intervals Files
                if (File.Exists( Folder_audioannotation + "AnnotationIntervals.xml"))
                { File.Delete( Folder_audioannotation + "AnnotationIntervals.xml"); }

                if (File.Exists(Folder_audioannotation + "AnnotationIntervals.csv"))
                { File.Delete(Folder_audioannotation + "AnnotationIntervals.csv"); }

                intervals_file_xml = new StreamWriter(Folder_audioannotation + "AnnotationIntervals.xml");
                intervals_file_csv = new StreamWriter(Folder_audioannotation + "AnnotationIntervals.csv");


                // Annotation Intervals Files, category 1
                if (File.Exists(DataSessionDir + "AnnotationIntervals_cat_1.xml"))
                { File.Delete(DataSessionDir + "AnnotationIntervals_cat_1.xml"); }

                if (File.Exists(DataSessionDir + "AnnotationIntervals_cat_1.csv"))
                { File.Delete(DataSessionDir + "AnnotationIntervals_cat_1.csv"); }


                intervals_file_xml_1 = new StreamWriter(DataSessionDir + "AnnotationIntervals_cat_1.xml");
                intervals_file_csv_1 = new StreamWriter(DataSessionDir + "AnnotationIntervals_cat_1.csv");


                // Annotation Intervals Files, category 2
                if (File.Exists(DataSessionDir + "AnnotationIntervals_cat_2.xml"))
                { File.Delete(DataSessionDir + "AnnotationIntervals_cat_2.xml"); }

                if (File.Exists(DataSessionDir + "AnnotationIntervals_cat_2.csv"))
                { File.Delete(DataSessionDir + "AnnotationIntervals_cat_2.csv"); }


                intervals_file_xml_2 = new StreamWriter(DataSessionDir + "AnnotationIntervals_cat_2.xml");
                intervals_file_csv_2 = new StreamWriter(DataSessionDir + "AnnotationIntervals_cat_2.csv");


                // ----------initialize sessions ------------------
                XmlSession_1 = new Session();
                XmlSession_1 = XmlSession.copy();

                XmlSession_2 = new Session();
                XmlSession_2 = XmlSession.copy();


                // ---------- Load labels to sessions 1 and 2------------------

                int count = 0;

                for (int c = 1; c <= 2; c++)
                {
                       
                    if( c == 1)
                    {   count = LabelsList_1.Count; }
                    else
                    {   count = LabelsList_2.Count; }


                    for (int i = 0; i < count ; i++)
                    {
                        if (c == 1)
                        { readline = LabelsList_1[i]; }
                        else
                        { readline = LabelsList_2[i]; }


                        string[] tokens = readline.Split(';');

                        if (tokens[0].CompareTo("ok") == 0)
                        {
                            currentRecord = new Annotation();

                            //Start Time
                            start_time = DateTime.Parse(StartDate + " " + tokens[3]);
                            
                            currentRecord._StartDate = start_time.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                            currentRecord._StartHour = start_time.Hour;
                            currentRecord._StartMinute = start_time.Minute;
                            currentRecord._StartSecond = start_time.Second;
                            currentRecord._StartMillisecond = start_time.Millisecond;

                            ts = (start_time - new DateTime(1970, 1, 1, 0, 0, 0));
                            currentRecord._StartUnix = ts.TotalSeconds;

                            //Stop Time
                            end_time = DateTime.Parse(EndDate + " " + tokens[4]);

                            currentRecord._EndDate = end_time.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                            currentRecord._EndHour = end_time.Hour;
                            currentRecord._EndMinute = end_time.Minute;
                            currentRecord._EndSecond = end_time.Second;
                            currentRecord._EndMillisecond = end_time.Millisecond;

                            ts = (end_time - new DateTime(1970, 1, 1, 0, 0, 0));
                            currentRecord._EndUnix = ts.TotalSeconds;


                            // Labels
                            category = tokens[6];
                            current_label = tokens[5];
                            currentRecord.Activities.Add(new Activity(current_label, category));
                           

                            // Save record to the correspondent session
                            if (c == 1)
                            {  XmlSession_1.Annotations.Add(currentRecord); }
                            else
                            {  XmlSession_2.Annotations.Add(currentRecord); }

                        }

                    }
                }


                // Save session 1 to file
                intervals_file_xml_1.WriteLine(XmlSession_1.ToXML());
                intervals_file_csv_1.WriteLine(XmlSession_1.ToCSV());

                // Save session 2 to file
                intervals_file_xml_2.WriteLine(XmlSession_2.ToXML());
                intervals_file_csv_2.WriteLine(XmlSession_2.ToCSV());

                // Close files session 1
                intervals_file_xml_1.Flush();
                intervals_file_xml_1.Close();

                intervals_file_csv_1.Flush();
                intervals_file_csv_1.Close();


                // Close files session 2
                intervals_file_xml_2.Flush();
                intervals_file_xml_2.Close();

                intervals_file_csv_2.Flush();
                intervals_file_csv_2.Close();


                #endregion



                //set the DataDirectory
                //XmlSession._DataDirectory = DataSessionDir;
                Session XmlSessionOutput = XmlSession_1.Merge(XmlSession_2);

                intervals_file_xml.WriteLine(XmlSessionOutput.ToXML());
                intervals_file_csv.WriteLine(XmlSessionOutput.ToCSV());

                intervals_file_xml.Flush();
                intervals_file_xml.Close();

                intervals_file_csv.Flush();
                intervals_file_csv.Close();

                //Save Labels Colors File
                SaveLabelsColorsToFile();

                return true;
            }
            catch
            {

                #region Close Files

                if (intervals_file_xml != null)
                {
                    intervals_file_xml.Flush();
                    intervals_file_xml.Close();

                }

                if (intervals_file_csv != null)
                {
                    intervals_file_csv.Flush();
                    intervals_file_csv.Close();
                }


                if (intervals_file_xml_1 != null)
                {
                    intervals_file_xml_1.Flush();
                    intervals_file_xml_1.Close();

                }

                if (intervals_file_csv_1 != null)
                {
                    intervals_file_csv_1.Flush();
                    intervals_file_csv_1.Close();
                }

                if (intervals_file_xml_2 != null)
                {
                    intervals_file_xml_2.Flush();
                    intervals_file_xml_2.Close();

                }

                if (intervals_file_csv_2 != null)
                {
                    intervals_file_csv_2.Flush();
                    intervals_file_csv_2.Close();
                }

                #endregion



                return false;
            }

        }


        //--- This colors assigned to the annotation bar in the viewer are protocol specific  ----
        private void SaveLabelsColorsToFile()
        {
            //Category 1
            if (File.Exists(Folder_audioannotation + "ActivityLabelsColors_1.csv"))
            { File.Delete(Folder_audioannotation + "ActivityLabelsColors_1.csv"); }

            TextWriter labels_colors_csv_1 = new StreamWriter(Folder_audioannotation + "ActivityLabelsColors_1.csv");
            

            //Category 2
            if (File.Exists(Folder_audioannotation + "ActivityLabelsColors_2.csv"))
            { File.Delete(Folder_audioannotation + "ActivityLabelsColors_2.csv"); }

            TextWriter labels_colors_csv_2 = new StreamWriter(Folder_audioannotation + "ActivityLabelsColors_2.csv");
            

            //Write headers
            labels_colors_csv_1.WriteLine("Category,Label,Color,ARGB");
            labels_colors_csv_2.WriteLine("Category,Label,Color,ARGB");


            string label = "";
            string csv = "";
            string color = "";
            string argb = "";

            for (int i = 0; i < XmlSession.OverlappingActivityLists.Count; i++)
            { 
               //Only two categories can be loaded
               if ( i == 0)
               {   
                   //load postures
                   for (int j = 0; j < list_category_1.Count; j++)
                   {
                       label = list_category_1[j];

                       csv = "";
                       color = "";
                       argb = "";

                       if (label.Trim().CompareTo("") != 0)
                       {
                           csv = list_category_name[i] + "," + label + ",";


                           if (label.Contains("unknown"))
                           {
                               color = Color.Gainsboro.Name;
                               argb =  Color.Gainsboro.ToArgb().ToString();
                               
                           }
                           else if (label.Contains("kneeling:-on-knees"))
                           {
                               color = Color.Plum.Name;
                               argb = Color.Plum.ToArgb().ToString();
                               
                           }
                           else if (label.Contains("lying"))
                           {
                               color = Color.LightBlue.Name;
                               argb = Color.FromArgb(50,Color.Blue).ToArgb().ToString();
                              
                           }
                           else if (label.Contains("sitting"))
                           {
                               color = Color.LightBlue.Name;
                               argb = Color.FromArgb(100,Color.DarkCyan).ToArgb().ToString();
                               
                           }
                           else if (label.Contains("standing:-still"))
                           {
                               color = Color.Blue.Name;
                               argb = Color.FromArgb(100,Color.Blue).ToArgb().ToString();
                               
                           }
                            else if (label.Contains("standing-carrying-load:-still"))
                           {
                               color = Color.Blue.Name;
                               argb = Color.FromArgb(255,Color.Orchid).ToArgb().ToString();
                               
                            }
                           else if (label.Contains("standing-carrying-load"))
                           {
                               color = Color.YellowGreen.Name;
                               argb = Color.FromArgb(230,Color.Tomato).ToArgb().ToString();
                               
                           }
                           else if (label.Contains("standing"))
                           {
                               color = Color.YellowGreen.Name;
                               argb = Color.FromArgb(180,Color.YellowGreen).ToArgb().ToString();
                               
                           }
                           else if (label.Contains("picking-up"))
                           {
                               color = Color.Violet.Name;
                               argb = Color.Violet.ToArgb().ToString();
                               
                           }
                           else if (label.Contains("bending-over"))
                           {
                               color = Color.Violet.Name;
                               argb = Color.Violet.ToArgb().ToString();
                               
                           }
                           else if (label.Contains("upright:-other"))
                           {
                               color = Color.Turquoise.Name;
                               argb = Color.Turquoise.ToArgb().ToString();
                               
                           }


                           labels_colors_csv_1.WriteLine(csv + color + "," + argb);

                       }
                   }

               }
               else if (i == 1)
               {
                   //load activities
                   for (int k = 0; k < list_category_2.Count; k++)
                   {
                       label = list_category_2[k];
                       csv = "";

                       if (label.Trim().CompareTo("") != 0)
                       {
                           csv = list_category_name[i] + "," + label + ",";

                           
                           if (label.Contains("unknown"))
                           {
                               color = Color.Gainsboro.Name;
                               argb = Color.Gainsboro.ToArgb().ToString();

                           }
                           else if (label.Contains("moving"))
                           {
                               color = Color.Orange.Name;
                               argb = Color.FromArgb(255, Color.Yellow).ToArgb().ToString();

                           }
                           else if (label.Contains("jumping-jacks") || label.Contains("running-vigorously-in-place"))
                           {
                               color = Color.Orange.Name;
                               argb = Color.FromArgb(255, Color.Orange).ToArgb().ToString();

                           }
                           else if (label.Contains("lifting-10-pound-box"))
                           {
                               color = Color.Violet.Name;
                               argb = Color.FromArgb(200, Color.Violet).ToArgb().ToString();

                           }
                           else if (label.Contains("walking"))
                           {
                               color = Color.Green.Name;
                               argb = Color.FromArgb(200, Color.Aquamarine).ToArgb().ToString();

                           }
                            else if (label.Contains("treadmill"))
                           {
                               color = Color.Green.Name;
                               argb = Color.FromArgb(255, Color.Green).ToArgb().ToString();

                           }
                            else if (label.Contains("cycling"))
                           {
                               color = Color.Green.Name;
                               argb = Color.FromArgb(230, Color.GreenYellow).ToArgb().ToString();

                           }
                           else if (label.Contains("carrying-load"))
                           {
                               color = Color.Tomato.Name;
                               argb = Color.FromArgb(230, Color.Red).ToArgb().ToString();

                           }
                            else if (label.Contains("stairs"))
                           {
                               color = Color.Tomato.Name;
                               argb = Color.FromArgb(150, Color.Brown).ToArgb().ToString();

                           }
                            else if (label.Contains("sweeping"))
                           {
                               color = Color.Tomato.Name;
                               argb = Color.FromArgb(200, Color.Coral).ToArgb().ToString();

                           }
                           else if (label.Contains("painting"))
                           {
                               color = Color.Tomato.Name;
                               argb = Color.FromArgb(100, Color.Coral).ToArgb().ToString();

                           }
                           else if (label.Contains("elevator"))
                           {
                               color = Color.Blue.Name;
                               argb = Color.FromArgb(250, Color.SteelBlue).ToArgb().ToString();

                           }
                           else if (label.Contains("sitting"))
                           {
                               color = Color.Blue.Name;
                               argb = Color.FromArgb(200, Color.Blue).ToArgb().ToString();

                           }
                           else if (label.Contains("sorting"))
                           {
                               color = Color.Blue.Name;
                               argb = Color.FromArgb(200, Color.DeepSkyBlue).ToArgb().ToString();

                           }
                           
                           labels_colors_csv_2.WriteLine(csv + color + "," + argb);
                       }
                   }
               }
               
            }
                

            //Close files
            labels_colors_csv_1.Flush();
            labels_colors_csv_1.Close();

            labels_colors_csv_2.Flush();
            labels_colors_csv_2.Close();
            
        
        }




        #endregion


        #region Load/Save buttons

        //Start Session Button
        private void button_2_Click(object sender, EventArgs e)
        {
            // Check if the audio files path exist
            if (Directory.Exists(textBox_1.Text))
            {

                DirectoryInfo directory = new DirectoryInfo(textBox_1.Text);
                Folder_session = directory.FullName + "\\";


                //Initialize Components
                if (LoadData())
                {
                    LoadViewGrid("grid");
                    LoadSessionView_1();

                    // create a player to be used in the application
                    //myPlayer = new System.Media.SoundPlayer();

                    is_data_grid_loaded = true;
                }
                else
                {
                    textBox_instructions_1.Text = label_play.Text;
                }


            }
            else
            {
                // send a warning saying that directory doesn't exist.
                if (textBox_1.Text.CompareTo("") == 0)
                {
                    textBox_instructions_1.Text = "To proceed, please enter a directory path.";
                }
                else
                {
                    textBox_instructions_1.Text = "The directory was not found. Please check the path.";
                }
            }

        }


        private void button_save_Click(object sender, EventArgs e)
        {
            SaveCurrentSessionToFile();
        }


        //Generate Labels Button
        PopUp_Result_Window dlg_summary_results = new PopUp_Result_Window();

        private void button_generate_Click(object sender, EventArgs e)
        {
            //Check labels, make summary 
            // and determine if the xml will be generated
            string summary_results = "";

            int success = GenerateActivityLabels(out summary_results);
            
            if( ((int)System.Math.Abs(success)) >= 2)
            {
                // show the summary of results in a new popup window
                if (dlg_summary_results.fill_grid_summary(summary_results))
                { dlg_summary_results.Show(); }
                else
                {
                    dlg_summary_results.Close();
                    
                    dlg_summary_results = new PopUp_Result_Window();
                    
                    if (dlg_summary_results.fill_grid_summary(summary_results))
                    { dlg_summary_results.Show(); }
                }
                this.Focus();
                
            }

        }


        private void button_exit_Click(object sender, EventArgs e)
        {
            if (checkBox_ExitWithoutSaving.Checked == false)
            { SaveCurrentSessionToFile(); }

           
            wmp.close();
            
            

            Application.Exit();
        }

         
        private void button_session_part_Click(object sender, EventArgs e)
        {
            button_category_select.Enabled = false;
            label_category_button.Enabled = false;

             if (SessionPart == 1)
            {
                button_category_select.Image = Resources.Im_previous;
                SessionPart = 2;

                LoadSessionView_2();
            }
            else
            {

                button_category_select.Image = Resources.Im_next;
                SessionPart = 1;

                LoadSessionView_1();

            }


            button_category_select.Enabled = true;
            label_category_button.Enabled = true;

        }


        private void LoadSessionView_1()
        {
            DataGridViewCellStyle cellStyle;


            // hide button
            button_generate.Enabled = true;

            button_category_select.Enabled = true;
            label_category_button.Enabled = true;

            // Category 1
            CCategory_1.ReadOnly = false;
            CStartEnd_1.ReadOnly = false;

            CCategory_1.FlatStyle = FlatStyle.Popup;
            CStartEnd_1.FlatStyle = FlatStyle.Popup;

            // Category 2
            CCategory_2.ReadOnly = true;
            CStartEnd_2.ReadOnly = true;

            CCategory_2.FlatStyle = FlatStyle.Flat;
            CStartEnd_2.FlatStyle = FlatStyle.Flat;



            for (int i = 0; i < dataGridView1.Rows.Count; i++)
            {
                //Category 1
                cellStyle = dataGridView1.Rows[i].Cells[C1.category_label].Style;
                if (cellStyle != null)
                {
                   cellStyle.BackColor = System.Drawing.Color.White;
                   cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[i].Cells[C1.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }


                //Category2
                cellStyle = dataGridView1.Rows[i].Cells[C2.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }

                cellStyle = dataGridView1.Rows[i].Cells[C2.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }

            }

          
        }


        private void LoadSessionView_2()
        {
            DataGridViewCellStyle cellStyle;

            //Show button
            button_generate.Enabled = true;
            button_category_select.Enabled = true;
            label_category_button.Enabled = true;

            // Category 1
            CCategory_1.ReadOnly = true;
            CStartEnd_1.ReadOnly = true;

            CCategory_1.FlatStyle = FlatStyle.Flat;
            CStartEnd_1.FlatStyle = FlatStyle.Flat;


            
            // Category 2
            CCategory_2.ReadOnly = false;
            CStartEnd_2.ReadOnly = false;

            CCategory_2.FlatStyle = FlatStyle.Popup;
            CStartEnd_2.FlatStyle = FlatStyle.Popup;



            for (int i = 0; i < dataGridView1.Rows.Count; i++)
            {
                //Category 1
                cellStyle = dataGridView1.Rows[i].Cells[C1.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }

                cellStyle = dataGridView1.Rows[i].Cells[C1.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }


                //Category2
                cellStyle = dataGridView1.Rows[i].Cells[C2.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[i].Cells[C2.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

            }


        }


        private void LoadSessionView_SinglePass()
        {
            DataGridViewCellStyle cellStyle;

            //Show button
            button_category_select.Enabled = false;
            label_category_button.Enabled = false;

            // Category 1
            CCategory_1.ReadOnly = false;
            CStartEnd_1.ReadOnly = false;

            CCategory_1.FlatStyle = FlatStyle.Popup;
            CStartEnd_1.FlatStyle = FlatStyle.Popup;



            // Category 2
            CCategory_2.ReadOnly = false;
            CStartEnd_2.ReadOnly = false;

            CCategory_2.FlatStyle = FlatStyle.Popup;
            CStartEnd_2.FlatStyle = FlatStyle.Popup;



            for (int i = 0; i < dataGridView1.Rows.Count; i++)
            {
                //Category 1
                cellStyle = dataGridView1.Rows[i].Cells[C1.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[i].Cells[C1.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }


                //Category2
                cellStyle = dataGridView1.Rows[i].Cells[C2.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[i].Cells[C2.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

            }


        }


        private void checkBox_SiglePassMode_CheckedChanged(object sender, EventArgs e)
        {
            if (checkBox_SiglePassMode.Checked)
            {
                LoadSessionView_SinglePass();
            }
            else
            {
                LoadSessionView_1();
            }
        }


        private void checkBox_visualize_all_CheckedChanged(object sender, EventArgs e)
        {
            if (checkBox_visualize_all.Checked)
            {
                CTime_MS.Visible = true;
                CTime_Duration.Visible = true;
                CTime_LastWritten.Visible = true;
            }
            else
            {
                CTime_MS.Visible = false;
                CTime_Duration.Visible = false;
                CTime_LastWritten.Visible = false;
            }
        }


        private void paintcells_view(int irow, int view)
        {
            DataGridViewCellStyle cellStyle;


            if (view == 1)
            {
                //Paint Category 1
                cellStyle = dataGridView1.Rows[irow].Cells[C1.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[irow].Cells[C1.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }


                //Paint Category2
                cellStyle = dataGridView1.Rows[irow].Cells[C2.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }

                cellStyle = dataGridView1.Rows[irow].Cells[C2.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }
            }
            else if (view == 2)
            {
                //Paint Category 1
                cellStyle = dataGridView1.Rows[irow].Cells[C1.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }

                cellStyle = dataGridView1.Rows[irow].Cells[C1.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.Gainsboro;
                    cellStyle.ForeColor = System.Drawing.Color.DimGray;
                }


                //Paint Category2
                cellStyle = dataGridView1.Rows[irow].Cells[C2.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[irow].Cells[C2.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

            }
            else if (view == 3)
            {
                //Paint Category 1
                cellStyle = dataGridView1.Rows[irow].Cells[C1.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[irow].Cells[C1.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }


                //Paint Category2
                cellStyle = dataGridView1.Rows[irow].Cells[C2.category_label].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }

                cellStyle = dataGridView1.Rows[irow].Cells[C2.StartEnd].Style;
                if (cellStyle != null)
                {
                    cellStyle.BackColor = System.Drawing.Color.White;
                    cellStyle.ForeColor = System.Drawing.Color.Black;
                }
            }



        }

        #endregion

       

       



    }
}