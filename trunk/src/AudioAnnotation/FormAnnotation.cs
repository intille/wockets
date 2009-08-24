using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using Wockets.Data.Annotation;
using System.Reflection;




namespace AudioAnnotation
{
    public partial class FormAnnotation : Form
    {

        #region  Declare variables

        private DirectoryInfo folder;
        private FileInfo[] files = null;
        private FileInfo[] files_wav = null;

        private FileInfo file_session = null;

        private System.Media.SoundPlayer myPlayer;


       


        private struct COLUMN_INDEX
        {
            public int  ID;
            public int  Lock;
            public int  category_label, StartEnd;
            public int  Time, Time_Label, Notes;

            public int  Status, StartID, EndID;
            public int  Combo_Type, Combo_Label;

            public COLUMN_INDEX(int category)
            {
                ID = 0;
                Time = 7;
                Time_Label = 8;
                Notes = 9;


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
                                 int  or, int  cr, bool lu, bool lo)
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



        private string StartDate="";
        private string EndDate="";

        
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
        private BindingList<string> list_category_1 = new BindingList<string>();
        private BindingList<string> list_category_2 = new BindingList<string>();

        private BindingList<string> LabelsList = new BindingList<string>();

        private TextWriter tw;
        private TextReader tr;

        private string DataSessionName = "";
        private string DataSessionDir  = "";
        private string DataAudioDir    = "";
        private string DataOutputDir   = "";
        private string SessionFileName = "";

        private int  SessionPart        = 1;
        private bool SessionStarted     = false;

        private bool is_data_grid_loaded = false;

        private Session XmlSession = null; 
        private BindingList<ActivityList> CActivityList = null;


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

        private bool LoadData()
        {

           bool is_data_loaded = false;


            try
            {
                //string name = " ";

                string name = textBox_3.Text.Trim();


                if (name.CompareTo("") == 0)
                {
                    name = "annotation_session.txt";
                    DataOutputDir = "";
                }
                else
                {   //get file session name and output directory
                    FileInfo finfo = new FileInfo(name);
                    if (finfo.Exists)
                    {
                        name = finfo.Name;
                        DataOutputDir = finfo.Directory.FullName + "\\";

                    }
                    else
                    {
                        //if (name.Contains(".txt") == false)
                        // { name = name + ".txt"; }

                        //name = "annotation_session.txt";
                        //DataOutputDir = "";  
                        //File.Create(name);
                        // finfo = new FileInfo(name);
                        name = finfo.Name;
                        DataOutputDir = finfo.Directory.FullName + "\\";

                    }
                }


                /*
                if (SessionPart == 1)
                { //name = textBox_2.Text.Trim(); 
                    name = "session_p1.txt";
                }
                else if (SessionPart == 2)
                {
                    name = "session_p2.txt";
                }
                 */


                if (SessionDir_Exist())
                {
                    if (LoadActivityLabels())
                    {
                        LoadGridColumnHeaders();

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


                            //if session name file not found
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
                            else
                            {
                                // !note: this should return an OK value
                                LoadRowsToGrid(DataSessionName);
                                is_data_loaded = true;

                                if (files == null)
                                {
                                    LoadAudioFiles();
                                }

                                if (files != null)
                                {
                                    if (files.Length > 0)
                                    {
                                        StartDate = files[0].LastWriteTime.ToShortDateString();
                                        EndDate = files[files.Length - 1].LastWriteTime.ToShortDateString();
                                    }
                                }

                            }
                           
                        } //if textbox is blank
                        else
                        {
                            DataSessionName = DataSessionDir + "annotation_session.txt";
                            //"Session_" + DateTime.Now.Year.ToString() + "-" +
                            //DateTime.Now.Month.ToString() + "-" +
                            //DateTime.Now.Day.ToString() + ".txt";

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
                    label_play.Text = "No .wav audio files where found in the selected directory.";
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
            DateTime time;
            bool data_loaded = false;

            DeleteAllRows();

            if (files == null)
            {
                LoadAudioFiles();
            }

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


                    // creation time
                    time = files[n].LastWriteTime;


                    dgview.Rows[n].Cells[C1.Time].Value = time.Hour + ":" + time.Minute + ":" + time.Second; //+"."+time.Millisecond;
                    dgview.Rows[n].Cells[C1.Time_Label].Value = time.Hour + ":" + time.Minute + ":" + time.Second; //+ "." + time.Millisecond;

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

        private void LoadAudioFiles()
        { 
            try
            {

                DirectoryInfo dir = new DirectoryInfo(DataAudioDir);

                if (dir.Exists)
                {

                    files_wav = dir.GetFiles("*.wav");
                    files = dir.GetFiles("*.msv");

                    if (files_wav.Length != files.Length)
                    { label_play.Text = "Warning: mistmatch between number of msv and wav files!"; }

                   
                }
          
            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }
      
        }

        private bool AudioDir_Exist()
        {
            bool result = false;

            if (files.Length > 0)
            {
                DataAudioDir = files[0].DirectoryName;
                result = true;
            }

            return result;
        }
        
        private bool SessionDir_Exist()
        {
            bool result = false;

            if (DataAudioDir.CompareTo("") != 0)
            {
                
               DataSessionDir = DataAudioDir + "\\AnnotationFiles\\";

               if (!Directory.Exists(DataSessionDir))
                    { Directory.CreateDirectory(DataSessionDir); }
               
                if (DataOutputDir.CompareTo("") == 0)
               {   DataOutputDir = DataSessionDir; }

                result = true;
            }
            
            return result;
        }
       
        private void LoadGridColumnHeaders()
        {

            if (list_category_name != null)
            {
                if (list_category_name.Count > 0)
                {
                    /*if (SessionPart == 1)
                    { dataGridView1.Columns[CINDEX.category_label].HeaderText = list_category_name[0].ToUpper(); }
                    else if(SessionPart == 2)
                    { dataGridView1.Columns[CINDEX.category_label].HeaderText = list_category_name[1].ToUpper(); }                
                     */

                    dataGridView1.Columns[C1.category_label].HeaderText = list_category_name[0];
                    dataGridView1.Columns[C2.category_label].HeaderText = list_category_name[1]; 

                }
            }       
        
        }

        private void LoadViewGrid(string vw)
        {
            if (vw.CompareTo("grid") == 0)
            {
                //------ hide ------------
                textBox_1.Visible = false;
                textBox_2.Visible = false;
                textBox_instructions_1.Visible = false;
                textBox_instructions_2.Visible = false;
                
                label_files_path.Visible = false;
                label_protocol_file.Visible = false;

                button_1.Visible = false;
                button_2.Visible = false;
                button_3.Visible = false;

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

        // Play Audio Files
        private void button_play_Click(object sender, EventArgs e)
        {
            for (int i = 0; i < files_wav.Length; i++)
            {
                label_play.Text = "Playing file: " + i.ToString() + "  Time:" +
                                  files[i].LastWriteTime.ToLongDateString();


                Application.DoEvents();

                myPlayer.SoundLocation = files_wav[i].FullName;
                myPlayer.PlaySync();

            }
        }


        // Browse for Audio Files
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

                    folder = new DirectoryInfo(fullPath);
       

                    files_wav = folder.GetFiles("*.wav");
                    files = folder.GetFiles("*.msv");

                    if (files_wav.Length != files.Length)
                    {  textBox_instructions_1.Text = "Warning: mistmatch between number of msv and wav files!"; }

                    if (files_wav.Length > 0)
                    {
                        DataAudioDir = files_wav[0].DirectoryName;

                        if (textBox_2.Text.Trim().CompareTo("") == 0)
                        { textBox_instructions_1.Text = "Please provide a valid path for the protocol file, then click Start."; }
                        else
                        { textBox_instructions_1.Text = ""; }
                    }
                    else
                    {
                        textBox_instructions_1.Text = "No audio files were found. Please check for the right directory.";
                    }
                  
                }


            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }
        }


        // Browse for Xml File
        private void button_3_Click(object sender, EventArgs e)
        {
            try
            {

                this.openFileDialog.Title = "";
               
                if (textBox_2.Text.Trim().CompareTo("") != 0)
                {
                    if (Directory.Exists(textBox_2.Text))
                    { this.openFileDialog.InitialDirectory = textBox_2.Text.ToString(); }
                    else
                    { this.openFileDialog.InitialDirectory = this.folderBrowserDialog.SelectedPath; }
                }
                else
                {
                    this.openFileDialog.InitialDirectory = this.folderBrowserDialog.SelectedPath;

                }

              


                this.openFileDialog.Filter = "All files (*.xml)|*.xml";
                this.openFileDialog.FilterIndex = 2;
                this.openFileDialog.RestoreDirectory = true;


                if (this.openFileDialog.ShowDialog() == DialogResult.OK)
                {
                    string fname = this.openFileDialog.FileName;

                    if (File.Exists(fname))
                    {
                        textBox_2.Text = fname;

                        if (textBox_2.Text.Trim().CompareTo("") == 0)
                        {
                            textBox_instructions_1.Text = "Please provide a valid path for the protocol file, then click Start.";
                        }
                        else
                        { textBox_instructions_1.Text = "";
                          textBox_instructions_1.Text = "";
                        }
                    }
                    else
                    { textBox_2.Text = ""; }

                }
                else
                {
                    textBox_instructions_1.Text = "Protocol file path not valid. Please check for the right directory.";
                }


            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }
        }

        // Browse for txt session File
        private void button_browse_session_Click(object sender, EventArgs e)
        {
            try
            {
                this.openFileDialog_Session.Title = "";

                if (textBox_3.Text.Trim().CompareTo("") != 0)
                {
                    if (Directory.Exists(textBox_3.Text))
                    { this.openFileDialog_Session.InitialDirectory = textBox_3.Text.ToString(); }
                    else
                    { this.openFileDialog_Session.InitialDirectory = this.folderBrowserDialog.SelectedPath; }
                }
                else
                {
                    this.openFileDialog_Session.InitialDirectory = this.folderBrowserDialog.SelectedPath;

                }




                this.openFileDialog_Session.Filter = "All files (*.txt)|*.txt";
                this.openFileDialog_Session.FilterIndex = 2;
                this.openFileDialog_Session.RestoreDirectory = true;


                if (this.openFileDialog_Session.ShowDialog() == DialogResult.OK)
                {
                    string fname = this.openFileDialog_Session.FileName;

                    if (File.Exists(fname))
                    {
                        textBox_3.Text = fname;

                        if (textBox_3.Text.Trim().CompareTo("") == 0)
                        {
                            textBox_instructions_1.Text = "Please provide a valid path for the session file, then click Start.";
                        }
                        else
                        {
                            textBox_instructions_1.Text = "";
                            textBox_instructions_1.Text = "";
                        }
                    }
                    else
                    { textBox_3.Text = ""; }

                }
                else
                {
                    textBox_instructions_1.Text = "Session file path not valid. Please check for the right directory.";
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

            if ( (dataGridView1.Rows.Count > 0) && (current_row < dataGridView1.Rows.Count) )
            {
                if (dataGridView1.Rows[current_row].Cells[CINDEX.ID].Value.ToString().CompareTo("-----") == 0)
                {
                    if (current_row >= dataGridView1.Rows.Count)
                    {

                        if (dataGridView1.Rows[current_row].Cells[C1.category_label].Value == null)
                        { dataGridView1.Rows[current_row].Cells[C1.category_label].Value = " "; }
                        if (dataGridView1.Rows[current_row].Cells[C2.category_label].Value == null)
                        { dataGridView1.Rows[current_row].Cells[C2.category_label].Value = " "; }

                        

                        if( ( ( (current_column == C1.category_label) || (current_column == C1.StartEnd) ) && 
                              ( dataGridView1.Rows[current_row-1].Cells[C2.category_label].Value.ToString().CompareTo(" ") == 0) &&
                              ( CCategory_1.ReadOnly == false)
                            )  
                            ||
                            ( (current_column == C2.category_label || (current_column == C2.StartEnd)) && 
                              (dataGridView1.Rows[current_row-1].Cells[C1.category_label].Value.ToString().CompareTo(" ") == 0) &&
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
                        if(dataGridView1.Rows[current_row].Cells[C1.category_label].Value == null)
                        {  dataGridView1.Rows[current_row].Cells[C1.category_label].Value = " ";}
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


        #region Sound Files

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
            if (files != null)
            {
                if (files.Length > 0)
                {
                    try
                    {
                        myPlayer.SoundLocation = files_wav[index].FullName;
                        myPlayer.PlaySync();
                    }
                    catch
                    {   // console error
                    }
                }
            }

        }
        

        #endregion


        #region Row Operations

        private void initialize_row(int row, int TypeCombo, string row_label, int row_label_time,int index_label)
        {

            // initialize values
            dataGridView1.Rows[row].Cells[CINDEX.ID].Value = "-----";

            // initialize locks
            dataGridView1.Rows[row].Cells[C1.Lock].Value = true;
            dataGridView1.Rows[row].Cells[C2.Lock].Value = true;

            //initialize category labels            
            if ( index_label == C1.category_label )
            { 
                set_ComboBox(cellComboBox, row, C1.category_label, TypeCombo, row_label);
                set_ComboBox(cellComboBox, row, C2.category_label, 2, " ");
            }
            else
            {
                set_ComboBox(cellComboBox, row, C1.category_label, 2, " ");
                set_ComboBox(cellComboBox, row, C2.category_label, TypeCombo, row_label);
            }


           //check is not the end of the list, if end of the list leave it blank
            if ((row_label_time < dataGridView1.Rows.Count) && (row_label_time > -1) )
            {
                //obtain what the next row has in its label_time field
                dataGridView1.Rows[row].Cells[CINDEX.Time_Label].Value = dataGridView1.Rows[row_label_time].Cells[CINDEX.Time_Label].Value;
            }

            // Status
            // check if I need to setup the parameters according with previous row
            dataGridView1.Rows[row].Cells[C1.Status].Value = " ";
            dataGridView1.Rows[row].Cells[C1.StartID].Value = -1;
            dataGridView1.Rows[row].Cells[C1.EndID].Value = -1;

            dataGridView1.Rows[row].Cells[C2.Status].Value = " ";
            dataGridView1.Rows[row].Cells[C2.StartID].Value = -1;
            dataGridView1.Rows[row].Cells[C2.EndID].Value = -1;


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


        private int add_end_row( int row, out int nrows,string row_label, int index_label, int open_row, bool set_label_time)
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
            if ( set_status_forward(start_row, end_row, row_label, 3, false, start_row) == -1)
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
                        if ( ((bool)dataGridView1.Rows[row].Cells[C1.Lock].Value) == true)
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
                    {   value = " "; }

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


        private bool LoadRowsToGrid(string fname)
        {

            bool data_loaded = false;

            try
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



                    while (row_string != null)
                    {
                        ReadRow(row_string);

                        row_string = tr.ReadLine();
                    }


                    tr.Close();

                    label_play.Text = "The Session has been loaded.";
                    data_loaded = true;
                }
            }
            catch
            { }

            return data_loaded;

        }
            

           
        


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
                else if ((i == C1.category_label) ||(i == C2.category_label))
                { 
                    // Do nothing
                }
                else if (i == C1.Combo_Label)
                {
                    dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                    if (dataGridView1.Rows[row].Cells[C1.Combo_Type].Value.ToString().CompareTo("S") == 0)
                    { set_ComboBox(cellComboBox, row, C1.category_label,1, ncells[i]); }
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
                    ReadRow(row_string);

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
            //textBox_instructions.ForeColor = Color.Gainsboro;
            //label_files_path.ForeColor = Color.Gainsboro;
            //label_protocol_path.ForeColor = Color.Gainsboro;


            DialogResult dlg_res = dlg.ShowDialog();

            // if create session was selected
            if (dlg_res == DialogResult.No)
            {

                BackUp_PreviousSessions();

                SessionStarted = true;
                is_started = 0;

                //this.BackColor = Color.DimGray;
                //textBox_instructions.BackColor = Color.YellowGreen;
                this.Enabled = true;

            } // if load session was selected
            else if (dlg_res == DialogResult.OK)
            {


                SessionStarted = true;
                is_started = 1;

                //this.BackColor = Color.DimGray;
                //textBox_instructions.BackColor = Color.YellowGreen;
                this.Enabled = true;

            }// if session selection was canceled
            else if (dlg_res == DialogResult.Cancel)
            {
                SessionStarted = false;
                XmlSession = null;


                //this.BackColor = Color.DimGray;
                //textBox_instructions.BackColor = Color.YellowGreen;
                this.Enabled = true;

                label_play.Text = "To create or load a previous session must be selected. Otherwise, the annotation program cannot start.";

            }


            return is_started;


        }


        private void BackUp_PreviousSessions()
        {
            string fname;
            string fname_bk;

            // Backup previous session files
            //fname = DataSessionDir + "session_p1.txt";
            //fname_bk = DataSessionDir + "session_backup.txt";
            
            fname = DataSessionName;
            fname_bk = DataSessionDir + "bk_" + SessionFileName;


            if (File.Exists(fname))
            {
                if (File.Exists(fname_bk))
                { File.Delete(fname_bk); }

                File.Copy(fname, fname_bk);
                File.Delete(fname);
            }

            /*
            // Backup previous session files
            fname = DataSessionDir + "session_p2.txt";
            fname_bk = DataSessionDir + "session_p2_backup.txt";

            if (File.Exists(fname))
            {
                if (File.Exists(fname_bk))
                { File.Delete(fname_bk); }

                File.Copy(fname, fname_bk);
                File.Delete(fname);
            }
            */


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
           
            if ( DataOutputDir.CompareTo(DataSessionDir) != 0)
            {
                string foutput  = DataOutputDir + SessionFileName;
                string fname    = DataSessionDir + SessionFileName;
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
                        if(cur_label.CompareTo(prev_label) != 0) // current label different to previous
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
                else if(index_label == C2.category_label)
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
            while ( prev_row > start_row)
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
                    prev_row = prev_row -1;
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
            while ( (prev_row > end_row) && (prev_row >-1) )
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
                else if(search_label.CompareTo(" ") == 0)
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

                // check row status
                if (dataGridView1.Rows[i].Cells[CINDEX.Status].Value == null)
                { dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " "; }
                else
                {  search_label = dataGridView1.Rows[i].Cells[CINDEX.Status].Value.ToString(); }
                

                if (i < (max_rows - 1))
                {
                    if (search_label.CompareTo(" ") == 0)
                    {
                        //dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start_on";
                    }
                    else if (search_label.CompareTo("start") == 0)
                    {
                        start_row = i;
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
                
                    // check row status
                if (dataGridView1.Rows[i].Cells[CINDEX.Status].Value == null)
                {   dataGridView1.Rows[i].Cells[CINDEX.Status].Value = " "; }
                else
                { search_label = dataGridView1.Rows[i].Cells[CINDEX.Status].Value.ToString(); }



                    if (i < (max_rows - 1))
                    {
                        if (search_label.CompareTo(" ") == 0)
                        {
                            //dataGridView1.Rows[i].Cells[CINDEX.Status].Value = "start_on";
                        }
                        else if (search_label.CompareTo("end") == 0)
                        {
                            end_row = i;
                            break;
                        }
                    }
                    else if ( end_row == row )
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
                    end_row = prev_row -1;
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

            string next_status= " ";


           
                next_start = search_start_forward(row + 1, maxrows);  // serch for the next start label after this row
                next_end = search_end_forward(row + 1, maxrows);      // search for the next end label after this row

               
                if( next_start <= next_end)
                {   next = next_start; }
                else
                {   next = next_end;   }



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
                    prev_cellStyle.SelectionBackColor = Color.DarkSeaGreen;
                }


                cur_cellStyle = dataGridView1.Columns[e.ColumnIndex].DefaultCellStyle;
                if (cur_cellStyle != null)
                {
                    cur_cellStyle.SelectionBackColor = Color.Orange;
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
            
            
            this.panel_controls_2.Left = (int)System.Math.Round(0.5 * (this.Width - this.panel_controls_2.Width) );
            this.panel_controls_1.Left = (int)System.Math.Round(0.5 * (this.Width - this.panel_controls_1.Width));

            this.dataGridView1.Left = (int)System.Math.Round(0.025 * this.Width);
            this.dataGridView1.Width = (int)System.Math.Round(0.95 * this.Width);
            //this.dataGridView1.Height = (int)System.Math.Round(0.60 * this.Height);
            this.dataGridView1.Height = this.Height - panel_controls_2.Height - 100;

            //textBox_instructions_2.Text = "Please provide a valid path for the audio and protocol files, then click Start. \n If the session file field is left blank, an annotation session file will be created automatically. \n An existing session file can be provided or a new session file name can be specified. ";
            //textBox_instructions_1.ForeColor = Color.YellowGreen;
        }


        private void FormAnnotation_FormClosing(object sender, FormClosingEventArgs e)
        {
            if ( panel_controls_2.Visible && checkBox_ExitWithoutSaving.Checked )
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


            }// finish try
            catch
            {

                if (is_busy == 1)
                {

                    if ((dataGridView1.Rows[row].Cells[C1.category_label].Value.ToString().CompareTo(" ") != 0)
                         ||
                        (dataGridView1.Rows[row].Cells[C2.category_label].Value.ToString().CompareTo(" ") != 0)
                       )
                    { is_busy = 0; }
                }

                //System.Console.WriteLine("Data Error Event");   
            }

            
            
        }


        private void ProcessCategory(int column, int row)
        {

            COLUMN_STATUS CStatus = new COLUMN_STATUS(column, row);
            GetCategory_Status(column,row, out CStatus);

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


            if (column == (C1.category_label) )
            { CINDEX.SetValues(1); }
            else if (column == (C2.category_label) )
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
                        status.open_row = row +1;
                        is_label_open = false;
                        status.start_label = status.tlabel;

                        row = row + 1;
                        nrows = dataGridView1.Rows.Count;
                    }
                }
            }



            status.close_row = search_close_row_forward(row, nrows, status.open_row,is_label_open);


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
                            int open_row = search_open_row_backwards(row-1);

                            start_label = dataGridView1.Rows[open_row].Cells[CINDEX.category_label].Value.ToString();

                            if (start_label.CompareTo(end_label) == 0)
                            {
                                // clear previous row
                                fill_row(row-1, 2, " ", row-1, CINDEX.category_label, "start_on", open_row, row, false);
                                       
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

            if (XmlSession == null)
            {
                XmlSession = new Session();
                CActivityList = new BindingList<ActivityList>();


                //string labels_file_name = DataSessionDir + "ActivityLabelsRealtime.xml";
                //if (File.Exists(labels_file_name) == false)
                //{ labels_file_name = "ActivityLabelsRealtime.xml"; }

                string labels_file_name = textBox_2.Text;


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
                            activityArray = CActivityList[i].ToArray();
                            list_category_1.Add(" ");

                            for (int j = 0; j < CActivityList[i].Count - 1; j++)
                            { list_category_1.Add(activityArray[j]._Name); }
                        }
                        else if (i == 1)
                        {
                            activityArray = CActivityList[i].ToArray();
                            list_category_2.Add(" ");

                            for (int j = 0; j < CActivityList[i].Count - 1; j++)
                            { list_category_2.Add(activityArray[j]._Name); }

                        }

                    }

                }
            }
               

                 return is_file_found;
        }




        ArrayList records = new ArrayList();
        Annotation currentRecord;
       
        private void GenerateActivityLabels()
        { 
           // read the values
           // check all the labels match
           // when ok, fill the records

                    
            try
            {
               

               

            #region loop the category labels

                int start_row, end_row, _category;
                string label_start, label_end;
                string start_time, end_time;
                string record_string;


                nrows = dataGridView1.Rows.Count;

                // backup first
                if (File.Exists(DataSessionDir + "Data_Session.txt"))
                { File.Delete(DataSessionDir + "Data_Session.txt"); }

                TextWriter txw = new StreamWriter(DataSessionDir + "Data_Session.txt");
                txw.WriteLine(StartDate + ";" + EndDate + ";");
                LabelsList.Clear();

                // check that both columns labels are correct
                // If not, send the appropriate message to correct them
           
           

            // there are two categories
            for (int c = 1; c <=2; c++)
            {
                // set category
                CINDEX.SetValues(c);

                //initialize variables
                start_row = 0;
                end_row = 0;
                _category = c-1;

                label_start = "";
                label_end = "";

                start_time = "";
                end_time = "";

                record_string = "";


                //------------------

                start_row = search_start_forward(start_row, nrows);
                end_row = search_close_row_forward(start_row, nrows, start_row, true);



                while (end_row < nrows)
                {
                    label_start = dataGridView1.Rows[start_row].Cells[CINDEX.category_label].Value.ToString();
                    label_end = dataGridView1.Rows[end_row].Cells[CINDEX.category_label].Value.ToString();

                    start_time = dataGridView1.Rows[start_row].Cells[CINDEX.Time_Label].Value.ToString();
                    end_time = dataGridView1.Rows[end_row].Cells[CINDEX.Time_Label].Value.ToString();

                    // check if row seq. is correct
                    if (start_row < end_row)
                    {

                        #region

                        //search for the category
                        /*category = -1;

                        if (CINDEX.category_label == C1.category_label)
                        {
                            category = 0;
                            /*for (int i = 0; i < list_category_1.Count; i++)
                            {
                                label_end = list_category_1[i];

                                if (label_end.CompareTo(" ") == 0)
                                { category = category + 1; }

                                if (label_start.CompareTo(label_end) == 0)
                                {
                                    break;
                                }
                            }
                            
                        }
                        else if (CINDEX.category_label == C2.category_label)
                        {
                            category = 1;
                            
                            /*
                             * for (int i = 0; i < list_category_2.Count; i++)
                            {
                                label_end = list_category_2[i];

                                if (label_end.CompareTo(" ") == 0)
                                { category = category + 1; }

                                if (label_start.CompareTo(label_end) == 0)
                                {
                                    break;
                                }
                            }
                             

                        }
                    //*****/
                        #endregion


                        // check if record is correct
                        if (label_start.CompareTo(label_end) == 0)
                        {
                            //write record to list
                            record_string = start_row.ToString() + ";" + end_row.ToString() + ";" +
                                            start_time.ToString() + ";" + end_time.ToString() + ";" +
                                            label_start + ";" + list_category_name[_category];


                            txw.WriteLine(record_string);
                            LabelsList.Add(record_string);

                            if ((end_row + 1) < nrows)
                            {
                                start_row = search_start_forward(end_row + 1, nrows);
                                end_row = search_close_row_forward(start_row + 1, nrows, start_row + 1, true);
                            }
                            else
                            {   end_row = end_row + 1; }


                        }
                        else
                        {
                            //record is incorrect
                            //end_row = nrows; ???

                            label_play.Text = "The label for category " + list_category_name[_category] +
                                               " in rows: " + start_row.ToString() +
                                              " and " + end_row.ToString() + " do not match. Please check.";

                            //write record to list
                            record_string = start_row.ToString() + ";" + end_row.ToString() + ";" +
                                            start_time.ToString() + ";" + end_time.ToString() + ";" +
                                            label_start + ";" + list_category_name[_category] + ";**";

                            txw.WriteLine(record_string);
                            LabelsList.Add(record_string);

                            //update variables
                            if ((end_row + 1) < nrows)
                            {
                                start_row = search_start_forward(end_row + 1, nrows);
                                end_row = search_close_row_forward(start_row + 1, nrows, start_row + 1, true);
                            }
                            else
                            {
                                end_row = end_row + 1;
                            }

                        }



                    }
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


            // Load annotations
            #region
                /*
            // backup first
            if (File.Exists(DataSessionDir + "AnnotationIntervals.xml"))
            { File.Delete(DataSessionDir + "AnnotationIntervals.xml"); }

            if (File.Exists(DataSessionDir + "AnnotationIntervals.csv"))
            { File.Delete(DataSessionDir + "AnnotationIntervals.csv"); }

            TextWriter intervals_file_xml = new StreamWriter(DataSessionDir + "AnnotationIntervals.xml");
            TextWriter intervals_file_csv = new StreamWriter(DataSessionDir + "AnnotationIntervals.csv");



            for (int i = 0; i < 3; i++)
                {
                    currentRecord = new Annotation();

                    //Start Time
                    currentRecord._StartDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                    currentRecord._StartHour = DateTime.Now.Hour;
                    currentRecord._StartMinute = DateTime.Now.Minute;
                    currentRecord._StartSecond = DateTime.Now.Second;
                    TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                    currentRecord._StartUnix = ts.TotalSeconds;

                    // Label
                    ActivityList category = (ActivityList)XmlSession.OverlappingActivityLists[0];
                    string current_label = list_category_1[i];
                    currentRecord.Activities.Add(new Activity(current_label, category._Name));

                    //Stop Time
                    currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                    currentRecord._EndHour = DateTime.Now.Hour;
                    currentRecord._EndMinute = DateTime.Now.Minute;
                    currentRecord._EndSecond = DateTime.Now.Second;
                    ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                    currentRecord._EndUnix = ts.TotalSeconds;

                    // Save record to session
                    XmlSession.Annotations.Add(currentRecord);
                }

                    // Save to Xml file
                    intervals_file_xml.WriteLine(XmlSession.ToXML());
                    intervals_file_csv.WriteLine(XmlSession.ToCSV());


                    // Close the Xml file
                    intervals_file_xml.Flush();
                    intervals_file_xml.Close();

                    intervals_file_csv.Flush();
                    intervals_file_csv.Close();
                */
            #endregion


                    label_play.Text = "The Xml annotation file has been generated.";
                            
            }
            catch
            {
                label_play.Text = "Problems generating the Xml annotation file.";
            }
        }




        private void SaveActivityLabels()
        {

            Annotation record;
            AnnotationList recordList = XmlSession.Annotations;

            int numberOfLabels = LabelsList.Count -1;
            string[] LList;
           
            int start_row;
            int end_row;

            string start_date;
            string end_date;

            string start_time;
            string end_time;

            string label_name;
            string category_name;


            for (int i = 0; i < numberOfLabels; i++)
            {
                LList = LabelsList[i].Split(';');

                record = SetRecord(false, i);
                recordList.Add(record);
            }

            recordList.ToXML();
            XmlSession.ToXML();
            
        
        }

        private Annotation SetRecord(bool fill_blank, int nlabel)
        {
            Annotation record = new Annotation();
            System.Convert.ToInt32("");

            if (fill_blank)
            {
                record._StartDate = "";
                record._EndDate = "";

                record._StartHour = 0;
                record._StartMinute = 0;
                record._StartSecond = 0;
                record._StartMillisecond = 0;

                record._EndHour = 0;
                record._EndMinute = 0;
                record._EndSecond = 0;
                record._EndMillisecond = 0;

                record.Activities._Name = "";
            }
            else
            {
                // set specific element
            }


            return record;

        }




        #region from PPC
        
        /*
        ArrayList records = new ArrayList();

        private void startAnnotation()
        {
            this.currentRecord = new Annotation();
            this.currentRecord._StartDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            this.currentRecord._StartHour = DateTime.Now.Hour;
            this.currentRecord._StartMinute = DateTime.Now.Minute;
            this.currentRecord._StartSecond = DateTime.Now.Second;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._StartUnix = ts.TotalSeconds;

            //check all buttons values, store them and disable them
            if (this.panel2.Visible)
            {
                foreach (ComboBox combo in categoryDrops)
                {
                    int button_id = Convert.ToInt32(combo.Name);
                    ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                    string current_label = (string)combo.SelectedItem;
                    this.currentRecord.Activities.Add(new Activity(current_label, category._Name));
                }
            }
            else if (this.panel6.Visible)
            {
                for (int i = 0; i < selectedButtons.Count; i++)
                {
                    System.Windows.Forms.Button but = (System.Windows.Forms.Button)selectedButtons[i];
                    this.currentRecord.Activities.Add(new Activity(but.Name.Split(delimiter)[1], but.Name.Split(delimiter)[0]));
                }
            }
        }

        private void stopAnnotation()
        {
            this.currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            this.currentRecord._EndHour = DateTime.Now.Hour;
            this.currentRecord._EndMinute = DateTime.Now.Minute;
            this.currentRecord._EndSecond = DateTime.Now.Second;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._EndUnix = ts.TotalSeconds;
            this.annotatedSession.Annotations.Add(this.currentRecord);
        }

        private void startStopButton_Click(object sender, EventArgs e)
        {
            MenuItem item = (MenuItem)sender;
            //button state is now start
            if (item.Text.Equals("Start"))
            {
                isAnnotating = true;
                item.Text = "Stop";
                this.overallTimer.reset();
                this.overallTimer.start();
                this.goodTimer.reset();
                this.goodTimer.start();
                startAnnotation();
                /*
                //store the current state of the categories
                this.currentRecord = new Annotation();
                this.currentRecord._StartDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                this.currentRecord._StartHour = DateTime.Now.Hour;
                this.currentRecord._StartMinute = DateTime.Now.Minute;
                this.currentRecord._StartSecond = DateTime.Now.Second;
                TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                this.currentRecord._StartUnix = ts.TotalSeconds;

                //check all buttons values, store them and disable them
                if (this.panel2.Visible)
                {
                    foreach (ComboBox combo in categoryDrops)
                    {
                        int button_id = Convert.ToInt32(combo.Name);
                        ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                        string current_label = (string)combo.SelectedItem;
                        this.currentRecord.Activities.Add(new Activity(current_label, category._Name));
                    //    combo.Enabled = false;
                    }
                }
                else if (this.panel6.Visible)
                {
                    for (int i = 0; i < selectedButtons.Count; i++)
                    {
                        System.Windows.Forms.Button but = (System.Windows.Forms.Button)selectedButtons[i];
                        this.currentRecord.Activities.Add(new Activity(but.Name.Split(delimiter)[1], but.Name.Split(delimiter)[0]));
                    }
              //      this.panel6.Enabled = false;
                }
                ///   ****here ignore bracket closes

            }

            else if (item.Text.Equals("Stop"))
            {
                // this.stopSound.Play();
                isAnnotating = false;
                item.Text = "Start";
                this.overallTimer.reset();
                this.goodTimer.reset();
                extractedVectors = 0;

                /*
                //store the current state of the categories
                this.currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                this.currentRecord._EndHour = DateTime.Now.Hour;
                this.currentRecord._EndMinute = DateTime.Now.Minute;
                this.currentRecord._EndSecond = DateTime.Now.Second;
                TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
                this.currentRecord._EndUnix = ts.TotalSeconds;
                this.annotatedSession.Annotations.Add(this.currentRecord);
                 ///   ****here ignore bracket closes

                stopAnnotation();
                //each time an activity is stopped, rewrite the file on disk, need to backup file to avoid corruption
                //this.annotation.ToXMLFile();
                //this.annotation.ToCSVFile();
                TextWriter tw = new StreamWriter(this.storageDirectory + "\\AnnotationIntervals.xml");
                // write a line of text to the file
                tw.WriteLine(this.annotatedSession.ToXML());
                // close the stream
                tw.Close();

                foreach (ComboBox c in this.categoryDrops)
                    c.Enabled = true;



                if (this.panel6.Visible)
                    this.panel6.Enabled = true;

                this.currentRecord = null;
            }
        }


        private void resetButton_Click(object sender, EventArgs e)
        {
            //this.resetSound.Play();
            //this.overallTimer.stop();
            this.overallTimer.reset();
            this.goodTimer.reset();

            foreach (Button category_button in categoryButtons)
            {
                int button_id = Convert.ToInt32(category_button.Name);
                ActivityList category = (ActivityList)this.annotatedSession.OverlappingActivityLists[button_id];
                this.buttonIndex[button_id] = 0;
                category_button.Text = category[0]._Name;
                category_button.Enabled = true;
            }
        }
*/

        #endregion


        #endregion


        #region Load/Save buttons


        private void button_2_Click(object sender, EventArgs e)
        {
            // Check if the audio files path exist
            if( Directory.Exists(textBox_1.Text) )
            {
                
                DirectoryInfo directory = new DirectoryInfo(textBox_1.Text);
                DataAudioDir = directory.FullName;


                //Initialize Components
                
                if( LoadData())
                { 
                    LoadViewGrid("grid");
                    LoadSessionView_1();

                    // create a player to be used in the application
                    myPlayer = new System.Media.SoundPlayer();

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

        private void button_generate_Click(object sender, EventArgs e)
        {

            GenerateActivityLabels();

        }

        private void button_exit_Click(object sender, EventArgs e)
        {

            //SaveRowsToFile(DataSessionName);
            Application.Exit();
        }

        private void button_session_part_Click(object sender, EventArgs e)
        {
            button_category_select.Enabled = false;
            label_category_button.Enabled = false;

            //if (label_category_button.Text.CompareTo("  Next   Category") == 0)
            if(SessionPart  == 1)
            {
                //SaveCurrentSessionToFile();
                //label_category_button.Text = "Previous Category";
                button_category_select.Image = Resources.Im_previous;
                SessionPart = 2;

                //LoadData();

                LoadSessionView_2();

               
                

            }
            else
            {

                //SaveCurrentSessionToFile();
                //button_category_select.Text = "Next Category";
                //label_category_button.Text ="  Next   Category";
                button_category_select.Image = Resources.Im_next;
                SessionPart = 1;


                //LoadData();

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


                  cellStyle = CCategory_1.DefaultCellStyle;
                  if (cellStyle != null)
                  { cellStyle.BackColor = Color.White;
                    cellStyle.ForeColor = Color.Black;
                  }

                  cellStyle = CStartEnd_1.DefaultCellStyle;
                  if (cellStyle != null)
                  { cellStyle.BackColor = Color.White;
                    cellStyle.ForeColor = Color.Black;
                  }


               // Category 2
                  CCategory_2.ReadOnly = true;
                  CStartEnd_2.ReadOnly = true;

                  CCategory_2.FlatStyle = FlatStyle.Flat;
                  CStartEnd_2.FlatStyle = FlatStyle.Flat;

                  cellStyle = CCategory_2.DefaultCellStyle;
                  if (cellStyle != null)
                  { cellStyle.BackColor = Color.Gainsboro;
                    cellStyle.ForeColor = Color.DimGray;
                  }

                  cellStyle = CStartEnd_2.DefaultCellStyle;
                  if (cellStyle != null)
                  { cellStyle.BackColor = Color.Gainsboro;
                    cellStyle.ForeColor = Color.DimGray;
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

            cellStyle = CCategory_1.DefaultCellStyle;
            if (cellStyle != null)
            { cellStyle.BackColor = Color.Gainsboro;
              cellStyle.ForeColor = Color.DimGray;
            }

            cellStyle = CStartEnd_1.DefaultCellStyle;
            if (cellStyle != null)
            {   cellStyle.BackColor = Color.Gainsboro;
                cellStyle.ForeColor = Color.DimGray;
            }


            // Category 2
            CCategory_2.ReadOnly = false;
            CStartEnd_2.ReadOnly = false;

            CCategory_2.FlatStyle = FlatStyle.Popup;
            CStartEnd_2.FlatStyle = FlatStyle.Popup;

            cellStyle = CCategory_2.DefaultCellStyle;
            if (cellStyle != null)
            {   cellStyle.BackColor = Color.White;
                cellStyle.ForeColor = Color.Black;
            }

            cellStyle = CStartEnd_2.DefaultCellStyle;
            if (cellStyle != null)
            {   cellStyle.BackColor = Color.White;
                cellStyle.ForeColor = Color.Black;
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


            cellStyle = CCategory_1.DefaultCellStyle;
            if (cellStyle != null)
            {
                cellStyle.BackColor = Color.White;
                cellStyle.ForeColor = Color.Black;
            }

            cellStyle = CStartEnd_1.DefaultCellStyle;
            if (cellStyle != null)
            {
                cellStyle.BackColor = Color.White;
                cellStyle.ForeColor = Color.Black;
            }



            // Category 2
            CCategory_2.ReadOnly = false;
            CStartEnd_2.ReadOnly = false;

            CCategory_2.FlatStyle = FlatStyle.Popup;
            CStartEnd_2.FlatStyle = FlatStyle.Popup;

            cellStyle = CCategory_2.DefaultCellStyle;
            if (cellStyle != null)
            {
                cellStyle.BackColor = Color.White;
                cellStyle.ForeColor = Color.Black;
            }

            cellStyle = CStartEnd_2.DefaultCellStyle;
            if (cellStyle != null)
            {
                cellStyle.BackColor = Color.White;
                cellStyle.ForeColor = Color.Black;
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


        #endregion

      

      






    }
}