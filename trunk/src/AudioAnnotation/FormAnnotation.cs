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


namespace TestApplication_Annotation
{
    public partial class FormAnnotation : Form
    {

        #region  Declare variables

        private DirectoryInfo folder;
        private FileInfo[] files = null;
        private FileInfo[] files_wav = null;

        private FileInfo file_session = null;

        //private int fptr;
        private System.Media.SoundPlayer myPlayer;

      
        private int index_ID = 0;
        private int index_Posture_Lock = 1;
        private int index_label_Posture = 2;
        private int index_label_StartEnd = 3;
        private int index_activity_lock_2 = 4;
        private int index_label_Activity = 5;
        private int index_label_StartEnd_A = 6;
       
        private int index_time = 7;
        private int index_label_Time = 8;
        private int index_notes= 9;
        private int index_Status = 10;
        private int index_StartID = 11;
        private int index_EndID = 12;

        private int index_combo_type_1  = 13;
        private int index_combo_label_1 = 14;
        private int index_combo_type_2  = 15;
        private int index_combo_label_2 = 16;

        private string StartDate="";
        private string EndDate="";

        
        private int is_busy = 0;
        private int nrows = 0;

        
        string tlabel = " ";
        string next_tlabel = " ";
        
        string status_tlabel = " ";

        private int current_row = 0;
        private int current_column = 0;

        private DataGridViewCellStyle prev_cellStyle = null;
        private DataGridViewCellStyle cur_cellStyle = null;
        DataGridViewComboBoxCell cellComboBox = null;

        private BindingList<string> list_postures = new BindingList<string>();
        private BindingList<string> list_categories = new BindingList<string>();

        private BindingList<string> LabelsList = new BindingList<string>();

        private TextWriter tw;
        private TextReader tr;

        private string DataSessionName = "";
        private string DataSessionDir  = "";
        private string DataAudioDir    = "";

        private bool SessionLoaded     = false;

        #endregion


        private Session XmlSession = new Session();
        private BindingList<ActivityList> CActivityList = new BindingList<ActivityList>();


        public FormAnnotation()
        {
            InitializeComponent();

        }



        #region initialize

        private void InitializeDataGridView(DataGridView dgview)
        {
            
            CPosture.SortMode = DataGridViewColumnSortMode.NotSortable;
            CPosture.Sorted = false;

            CStartEnd.SortMode = DataGridViewColumnSortMode.NotSortable;
            CStartEnd.Sorted = false;


            // Next Status
            CStatus.Items.Add(" ");         // "label" value not set
            CStatus.Items.Add("start");     // start label begins
            CStatus.Items.Add("start_on");  // start label was set
            CStatus.Items.Add("end");       // end label ends
            


            CStatus.SortMode = DataGridViewColumnSortMode.NotSortable;
            CStatus.Sorted = false;



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


        #region Read Data

        // Load Data from the DataSet into the ListView
        private bool LoadList(DataGridView dgview)
        {
            DateTime time;
            bool result = false;

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
                    dgview.Rows[n].Cells[index_ID].Value = n.ToString();


                    //Main Label : Posture
                    dgview.Rows[n].Cells[index_Posture_Lock].Value = false;
                    cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[n].Cells[index_label_Posture];
                    set_ComboBox(cellComboBox, n, index_label_Posture, 2, " ");


                    //Concurrent Label: Activity 2
                    dgview.Rows[n].Cells[index_activity_lock_2].Value = false;
                    cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[n].Cells[index_label_Activity];
                    set_ComboBox(cellComboBox, n, index_label_Activity, 2, " ");



                    // creation time
                    time = files[n].LastWriteTime;


                    dgview.Rows[n].Cells[index_time].Value = time.Hour + ":" + time.Minute + ":" + time.Second; //+"."+time.Millisecond;
                    dgview.Rows[n].Cells[index_label_Time].Value = time.Hour + ":" + time.Minute + ":" + time.Second; //+ "." + time.Millisecond;

                    // Status
                    dgview.Rows[n].Cells[index_Status].Value = " ";
                    dgview.Rows[n].Cells[index_StartID].Value = -1;
                    dgview.Rows[n].Cells[index_EndID].Value = -1;

                }

                time = files[0].LastWriteTime;
                StartDate = time.Year + "-" + time.Month + "-" + time.Day;

                time = files[files.Length - 1].LastWriteTime;
                EndDate = time.Year + "-" + time.Month + "-" + time.Day;


                // End/Start

                CStartEnd.Items.Add(" ");
                CStartEnd.Items.Add("End");
                CStartEnd.Items.Add("Start");

                CStartEnd_Activity.Items.Add(" ");
                CStartEnd_Activity.Items.Add("End");
                CStartEnd_Activity.Items.Add("Start");


                result = true;
            }
            else
            {
                label_play.Text = "No audio files were found.Please check directory name.";
            }

            return result;
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
                
               DataSessionDir = DataAudioDir + "\\WocketsFiles\\";

               if (!Directory.Exists(DataSessionDir))
                    { Directory.CreateDirectory(DataSessionDir); }
                
                result = true;
            }
            
            return result;
        }
       
        private void LoadData()
        {
            try
            {
                

                string name = textBox_2.Text.Trim();

                if ( SessionDir_Exist())
                {
                    LoadActivityLabels();

                    if (name.CompareTo("") != 0)
                    {
                        if (name.Contains(".txt") == false)
                        { name = name + ".txt"; }


                        name = DataSessionDir + name;

                        string[] session_files = Directory.GetFiles(DataSessionDir);
                        DataSessionName = "";

                        for (int i = 0; i < session_files.Length; i++)
                        {
                            if (name.CompareTo(session_files[i]) == 0)
                            {
                                DataSessionName = session_files[i];
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
                            }

                        }
                        else
                        {
                            LoadRowsToGrid(DataSessionName);

                            if (files.Length > 0)
                            {
                                StartDate = files[0].LastWriteTime.ToShortDateString();
                                EndDate = files[files.Length - 1].LastWriteTime.ToShortDateString();
                            }

                        }

                    } //if txtbox is blank
                    else
                    {
                        DataSessionName = DataSessionDir + 
                                           "Session_" + DateTime.Now.Year.ToString() + "-" +
                                           DateTime.Now.Month.ToString() + "-" +
                                           DateTime.Now.Day.ToString() + ".txt";

                        //Load list
                        if (LoadList(dataGridView1) == false)
                        {
                            label_play.Text = "No audio files were found. Please check the directory name.";
                        }

                    }
                }
                else //if SessionDir doesn't exist
                { 
                   label_play.Text = "No .wav audio files where found in the selected directory.";
                }

            } // end try

            catch (Exception err)
            {
                Console.WriteLine(err.Message);
            }
        }

        #endregion


        #region tree view

        private void treeView1_BeforeExpand(object sender, TreeViewCancelEventArgs e)
        {
            getSubDirs(e.Node);					// get the sub-folders for the selected node.
            textBox_1.Text = fixPath(e.Node);	// update the user selection text box.
            folder = new DirectoryInfo(e.Node.FullPath);	// get it's Directory info.		
        }


        private void treeView1_BeforeSelect(object sender, TreeViewCancelEventArgs e)
        {
            getSubDirs(e.Node);					// get the sub-folders for the selected node.
            textBox_1.Text = fixPath(e.Node);	// update the user selection text box.
            folder = new DirectoryInfo(e.Node.FullPath);	// get it's Directory info.
        }

        public DirectoryInfo info
        {
            get { return ((folder != null && folder.Exists)) ? folder : null; }
        }




        private void getSubDirs(TreeNode parent)
        {
            DirectoryInfo directory;
            try
            {
                // if we have not scanned this folder before
                if (parent.Nodes.Count == 0)
                {
                    directory = new DirectoryInfo(parent.FullPath);
                    foreach (DirectoryInfo dir in directory.GetDirectories())
                    {
                        TreeNode newNode = new TreeNode(dir.Name);
                        parent.Nodes.Add(newNode);
                    }
                }

                // now that we have the children of the parent, see if they
                // have any child members that need to be scanned.  Scanning 
                // the first level of sub folders insures that you properly 
                // see the '+' or '-' expanding controls on each node that represents
                // a sub folder with it's own children.
                foreach (TreeNode node in parent.Nodes)
                {
                    // if we have not scanned this node before.
                    if (node.Nodes.Count == 0)
                    {
                        // get the folder information for the specified path.
                        directory = new DirectoryInfo(node.FullPath);

                        // check this folder for any possible sub-folders
                        foreach (DirectoryInfo dir in directory.GetDirectories())
                        {
                            // make a new TreeNode and add it to the treeView.
                            TreeNode newNode = new TreeNode(dir.Name);
                            node.Nodes.Add(newNode);
                        }
                    }
                }
            }
            catch (Exception doh)
            {
                Console.WriteLine(doh.Message);
            }
        }


        private string fixPath(TreeNode node)
        {
            string sRet = "";
            try
            {
                sRet = node.FullPath;
                int index = sRet.IndexOf("\\\\");
                if (index > 1)
                {
                    sRet = node.FullPath.Remove(index, 1);
                }
            }
            catch (Exception doh)
            {
                Console.WriteLine(doh.Message);
            }
            return sRet;
        }

        #endregion


        #region Buttons


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


        private void button_load_Click(object sender, EventArgs e)
        {
            try
            {

                FolderSelection dlg = new FolderSelection(textBox_1.Text);

                if (dlg.ShowDialog() == DialogResult.OK)
                {
                    folder = dlg.info;
                    textBox_1.Text = dlg.fullPath;

                    files_wav = folder.GetFiles("*.wav");
                    files = folder.GetFiles("*.msv");

                    if (files_wav.Length != files.Length)
                    { label_play.Text = "Warning: mistmatch between number of msv and wav files!"; }

                    if (files_wav.Length > 0)
                    {
                        DataAudioDir = files_wav[0].DirectoryName;
                    }
                    else
                    {
                        textBox_instructions.Text = "No audio files were found. Please check for the right directory.";
                    }

                    

                }//end if dlg

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

                initialize_row(current_row, 2, " ", current_row + 1, index_label_Posture);
                
            }
            else
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
                    if (dataGridView1.Rows[current_row].Cells[index_StartID].Value != null)
                    { startRow = (int)dataGridView1.Rows[current_row].Cells[index_StartID].Value; }
                    else
                    { dataGridView1.Rows[current_row].Cells[index_StartID].Value = startRow;  }
                    
                    if (startRow < 0)
                    {
                        startRow = 0;
                        dataGridView1.Rows[current_row].Cells[index_StartID].Value = 0;
                    }

                    if (dataGridView1.Rows[startRow].Cells[index_label_Posture].Value != null)
                    { label_row = dataGridView1.Rows[startRow].Cells[index_label_Posture].Value.ToString(); }
                    typeCombo = 1;
                }
                else
                {
                    typeCombo = 2;
                }

                // insert the row
                dataGridView1.Rows.Insert(index_new_row, 1);

                // initialize the row according if start label is open or not
                initialize_row(index_new_row, typeCombo, label_row, index_new_row +1, index_label_Posture);
            }


        }


        private void button_remove_label_Click(object sender, EventArgs e)
        {

            if (dataGridView1.Rows.Count > 0)
            {
                if (dataGridView1.Rows[current_row].Cells[index_ID].Value.ToString().CompareTo("-----") == 0)
                {
                    if (current_row >= dataGridView1.Rows.Count)
                    {
                        dataGridView1.Rows.RemoveAt(current_row - 1);
                        current_row = current_row - 1;
                    }
                    else
                    {
                        dataGridView1.Rows.RemoveAt(current_row);

                    }
                }
                else
                {
                    label_play.Text = "This row is associated to an audio file. Audio file rows cannot be removed. Instead leave it blank.";
                }
            }
            
        }
       


        private void dataGridView1_RowHeaderMouseDoubleClick_1(object sender, DataGridViewCellMouseEventArgs e)
        {
            PlayFile(e.RowIndex);
        }

       

        private void dataGridView1_KeyDown(object sender, KeyEventArgs e)
        {
            Keys key = e.KeyCode;

            if ( key == Keys.F1 )
            {
                PlayFile(current_row);
            }


        }

        #endregion


        #region Sound Files

        private void PlayFile(int index)
        {
            int play_id = index;

            if ((dataGridView1.Rows[index].Cells[index_ID].Value != null) &&
                      (dataGridView1.Rows[index].Cells[index_ID].Value.ToString().CompareTo("-----") != 0))
            {
                play_id = System.Convert.ToInt16(dataGridView1.Rows[index].Cells[index_ID].Value.ToString());

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
            dataGridView1.Rows[row].Cells[index_ID].Value = "-----";

            dataGridView1.Rows[row].Cells[index_Posture_Lock].Value = false;
            dataGridView1.Rows[row].Cells[index_activity_lock_2].Value = false;

            //Label Posture
            cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[index_label];
            cellComboBox.Items.Clear();

            if (TypeCombo == 1) // simple
            {
                cellComboBox.Items.Add(" ");
                cellComboBox.Items.Add(row_label);
            }
            else if ((TypeCombo == 2) || (TypeCombo == 3)) //full 
            {
                if (index_label == index_label_Posture)
                {
                    for (int i = 0; i < list_postures.Count; i++)
                    { cellComboBox.Items.Add(list_postures[i]); }
                }
                else if (index_label == index_label_Activity)
                {
                    for (int i = 0; i < list_postures.Count; i++)
                    { cellComboBox.Items.Add(list_categories[i]); }
                }

            }


            //check is not the end of the list, if end of the list leave it blank
            if ((row_label_time < dataGridView1.Rows.Count) && (row_label_time > -1) )
            {
                //obtain what the next row has in its label_time field
                dataGridView1.Rows[row].Cells[index_label_Time].Value = dataGridView1.Rows[row_label_time].Cells[index_label_Time].Value;
            }

            // Status
            // check if I need to setup the parameters according with previous row
            dataGridView1.Rows[row].Cells[index_Status].Value = " ";
            dataGridView1.Rows[row].Cells[index_StartID].Value = -1;
            dataGridView1.Rows[row].Cells[index_EndID].Value = -1;
        }



        private void fill_row(int row, int TypeCombo, string row_label, int row_label_time, int index_label, string status, int open_row, int end_row)
        {
        
            initialize_row(row,TypeCombo,row_label,row_label_time,index_label);

            dataGridView1.Rows[row].Cells[index_label].Value = row_label;

            // Status
            if (status.CompareTo("end") == 0)
            {
                dataGridView1.Rows[row].Cells[index_Status].Value = "end";
                dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "End";
                dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                dataGridView1.Rows[row].Cells[index_EndID].Value = row;
            }
            else if (status.CompareTo("start") == 0)
            {
                dataGridView1.Rows[row].Cells[index_Status].Value = "start";
                dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "Start";
                dataGridView1.Rows[row].Cells[index_StartID].Value = row;
                dataGridView1.Rows[row].Cells[index_EndID].Value = end_row;
            }
            else if (status.CompareTo("start_on") == 0)
            {
                dataGridView1.Rows[row].Cells[index_Status].Value = "start_on";
                dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = " ";
                dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                dataGridView1.Rows[row].Cells[index_EndID].Value = end_row;
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
            { fill_row(start_row, 2, row_label, close_row, index_label, "start", start_row, close_row); }
            else
            { fill_row(start_row, 2, row_label, -1, index_label, "start", start_row, close_row); }

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
            { fill_row(close_row, 1, tlabel, close_row + 1, index_label, "end", open_row, close_row); }
            else
            { fill_row(close_row, 1, tlabel, -1, index_label, "end", open_row, close_row); }

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


        private void SaveRowsToGrid(string fname)
        {
            string row_string = "";
            //file_session = new FileInfo("DataSession.txt");

            file_session = new FileInfo(fname);

            if (file_session.Exists == true)
            {
                file_session.Delete();
            }
           
            //tw = new StreamWriter("DataSession.txt");
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

                if (i == index_Posture_Lock)
                {
                    if (dataGridView1.Rows[row].Cells[index_Posture_Lock].Value != null)
                    {
                        if ( ((bool)dataGridView1.Rows[row].Cells[index_Posture_Lock].Value) == true)
                        { value = "True"; }
                        else
                        { value = "False"; }
                    }
                    else
                    {
                        dataGridView1.Rows[row].Cells[index_Posture_Lock].Value = false;
                        value = "False";
                    }
                }
                else if (i == index_activity_lock_2)
                {
                    if (dataGridView1.Rows[row].Cells[index_activity_lock_2].Value != null)
                    {
                        if ( ((bool)dataGridView1.Rows[row].Cells[index_activity_lock_2].Value) == true)
                        { value = "True"; }
                        else
                        { value = "False"; }
                    }
                    else
                    {
                        dataGridView1.Rows[row].Cells[index_activity_lock_2].Value = false;
                        value = "False";
                    }
                }
                else if (i == index_combo_type_1)
                {
                    if (dataGridView1.Rows[row].Cells[index_label_Posture] != null)
                    {
                        cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[index_label_Posture];

                        if ((cellComboBox.Items.Count == list_postures.Count) || (cellComboBox.Items.Count == 0))
                        { value = "F"; }
                        else
                        { value = "S"; }
                    }
                    else
                    {
                           value = "F";
                    }
              
                }
                else if (i == index_combo_type_2)
                {

                    if (dataGridView1.Rows[row].Cells[index_label_Activity] != null)
                    {
                        cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[row].Cells[index_label_Activity];


                        if ((cellComboBox.Items.Count == list_postures.Count) || (cellComboBox.Items.Count == 0))
                        { value = "F"; }
                        else
                        { value = "S"; }
                    }
                    else
                    {
                        value = "F";
                    }
                }
                else if (i == index_combo_label_1)
                {
                    if (dataGridView1.Rows[row].Cells[index_label_Posture].Value != null)
                    {
                        value = dataGridView1.Rows[row].Cells[index_label_Posture].Value.ToString();
                    }
                    else
                    {   value = " "; }

                }
                else if (i == index_combo_label_2)
                {
                    if (dataGridView1.Rows[row].Cells[index_label_Activity].Value != null)
                    {
                        value = dataGridView1.Rows[row].Cells[index_label_Activity].Value.ToString();
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

        private void LoadRowsToGrid(string fname)
        {
            string row_string = "";
            int row = 0;
            int NumberOfRows;

            //file_session = new FileInfo("DataSession.txt");
            file_session = new FileInfo(fname);

            if (file_session.Exists == false)
            {
                label_play.Text = "A saved session file was not found in folder. A new session file will be created.";
                
            }
            else
            {

                DeleteAllRows();

                // Set End-Start
                CStartEnd.Items.Add(" ");
                CStartEnd.Items.Add("End");
                CStartEnd.Items.Add("Start");

                CStartEnd_Activity.Items.Add(" ");
                CStartEnd_Activity.Items.Add("End");
                CStartEnd_Activity.Items.Add("Start");





                tr = new StreamReader(fname);
                row_string = tr.ReadLine();


                if( row_string != null)
                {
                 
                    string[] ncells = row_string.Split(';');
                    StartDate= ncells[0];
                    EndDate = ncells[1];

                    row_string = tr.ReadLine();
                }


              
                while (row_string != null)
                {
                    WriteRow(row_string);

                    row_string = tr.ReadLine();
                    //row = row + 1;
                }


                tr.Close();

                label_play.Text = "The Session has been loaded.";
               

            }
            

           
        }


        private void WriteRow(string st)
        {
            string[] ncells = st.Split(';');

            int row = dataGridView1.Rows.Add();


            for (int i = 0; i < (ncells.Length - 1); i++)
            {
                
                if (i == index_Posture_Lock)
                {
                    if (ncells[i].CompareTo("True") == 0)
                    { dataGridView1.Rows[row].Cells[i].Value = true; }
                    else
                    { dataGridView1.Rows[row].Cells[i].Value = false; }
                }
                else if (i == index_activity_lock_2)
                {
                    if (ncells[i].CompareTo("True") == 0)
                    { dataGridView1.Rows[row].Cells[i].Value = true; }
                    else
                    { dataGridView1.Rows[row].Cells[i].Value = false; }
                }
                else if ((i == index_label_Posture) || (i == index_label_Activity))
                { 
                    // Do nothing
                }
                else if (i == index_combo_label_1)
                {
                    dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                    if (dataGridView1.Rows[row].Cells[index_combo_type_1].Value.ToString().CompareTo("S") == 0)
                    { set_ComboBox(cellComboBox, row, index_label_Posture,1, ncells[i]); }
                    else
                    { set_ComboBox(cellComboBox, row, index_label_Posture, 2, ncells[i]); }

                    dataGridView1.Rows[row].Cells[index_label_Posture].Value = ncells[index_label_Posture];
                }
                else if (i == index_combo_label_2)
                {
                    dataGridView1.Rows[row].Cells[i].Value = ncells[i];

                    if (dataGridView1.Rows[row].Cells[index_combo_type_2].Value.ToString().CompareTo("S") == 0)
                    { set_ComboBox(cellComboBox, row, index_label_Activity, 1, ncells[i]); }
                    else
                    { set_ComboBox(cellComboBox, row,index_label_Activity, 2, ncells[i]); }

                    dataGridView1.Rows[row].Cells[index_label_Activity].Value = ncells[index_label_Activity];
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


        #region Status


        private void check_cell_status(int row)
        {
            int prev_row = row - 1;

            // check row status
            tlabel = dataGridView1.Rows[row].Cells[index_Status].Value.ToString();

            if ((tlabel.CompareTo(" ") == 0) && (row > 0))
            {
                // search back what should be the right status label
                next_tlabel = dataGridView1.Rows[prev_row].Cells[index_Status].Value.ToString();

                if ((next_tlabel.CompareTo("start") == 0) || (next_tlabel.CompareTo("start_on") == 0))
                {
                    dataGridView1.Rows[row].Cells[index_Status].Value = "start_on";
                }

            }
        }


        private int check_label_lock(bool is_unlocked, bool is_label_open, int row, int index_label, string cur_label)
        {
            string prev_label = " ";
            string prev_status = " ";

            if (row > 0)
            {
                if (dataGridView1.Rows[row - 1].Cells[index_label].Value != null)
                { prev_label = dataGridView1.Rows[row - 1].Cells[index_label].Value.ToString(); }

                if (dataGridView1.Rows[row - 1].Cells[index_Status].Value != null)
                { prev_status = dataGridView1.Rows[row - 1].Cells[index_Status].Value.ToString(); }
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

                                int prev_row = row;

                                //insert row above
                                dataGridView1.Rows.Insert(prev_row, 1);

                                // update row number, row++
                                row = row + 1;

                                // fill "end" in inserted row and close label
                                fill_row(prev_row, 1, prev_label, row, index_label_Posture, "end", prev_row - 1, prev_row);


                            }
                            else if (prev_status.CompareTo(" ") == 0)
                            {
                                // check if label is open
                                // if label open, close it. Then, continue
                                // if label no open, continue 
                            }
                            /*
                            else if (prev_status.CompareTo("end") == 0)
                            {
                                // continue, do nothing
                                // don't modify combobox
                            }
                           */ 
                        }
                       
                        /*
                        else // current label similar to previous
                        {
                            // close label, but this is handled by the main software
                        }
                        */  
                         
                    }
                        /*
                    else // if label "blank", do nothing
                    {
                        // System.Console.WriteLine("This branch needs revision");
                    }
                         */
 
                }
               // else
               // { /* do nothing, continue*/ }
            }

            return row;
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
                search_label = dataGridView1.Rows[i].Cells[index_Status].Value.ToString();

                if ((i > start_row) || (block == false))
                {
                    cellComboBox = (DataGridViewComboBoxCell)dataGridView1.Rows[i].Cells[index_label_Posture];

                    if (TypeFill == 1)
                    {
                        cellComboBox.Items.Clear();
                        cellComboBox.Items.Add(" ");
                        cellComboBox.Items.Add(row_label);
                    }

                    else if ((TypeFill == 2) || (TypeFill == 3))
                    {
                        cellComboBox.Items.Clear();
                        for (int j = 0; j < list_postures.Count; j++)
                        { cellComboBox.Items.Add(list_postures[j]); }
                    }
                }




                if (search_label.CompareTo("start") == 0)
                {
                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[index_StartID].Value = -1;
                        dataGridView1.Rows[i].Cells[index_EndID].Value = -1;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[index_label_Posture].Value = " ";
                        dataGridView1.Rows[i].Cells[index_Status].Value = " ";

                    }
                    else
                    {
                        dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = "Start";
                    }
                }
                else if (search_label.CompareTo("start_on") == 0)
                {
                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[index_label_Posture].Value = " ";
                        dataGridView1.Rows[i].Cells[index_Status].Value = " ";

                    }
                    else
                    {
                        //dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_StartID].Value = t_open_row;

                        dataGridView1.Rows[i].Cells[index_EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = " ";
                    }

                }
                else if (search_label.CompareTo(" ") == 0)
                {

                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[index_Status].Value = "start_on";

                        dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_EndID].Value = end_row;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[index_label_Posture].Value = " ";
                        dataGridView1.Rows[i].Cells[index_Status].Value = " ";
                    }
                    else
                    {
                        dataGridView1.Rows[i].Cells[index_Status].Value = "start_on";

                        //dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_StartID].Value = t_open_row;

                        dataGridView1.Rows[i].Cells[index_EndID].Value = end_row;
                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = " ";

                    }

                }
                else if (search_label.CompareTo("end") == 0)
                {

                    if (TypeFill == 3)
                    {
                        dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_EndID].Value = i;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = " ";
                        dataGridView1.Rows[i].Cells[index_label_Posture].Value = " ";
                        dataGridView1.Rows[i].Cells[index_Status].Value = " ";
                    }
                    else
                    {
                        //dataGridView1.Rows[i].Cells[index_StartID].Value = start_row;
                        dataGridView1.Rows[i].Cells[index_StartID].Value = t_open_row;

                        dataGridView1.Rows[i].Cells[index_EndID].Value = i;

                        dataGridView1.Rows[i].Cells[index_label_StartEnd].Value = "End";
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
                    for (int j = 0; j < list_postures.Count; j++)
                    { combo.Items.Add(list_postures[j]); }
                }
            }
            else //if (fill_type == 2) //full
            {
                combo.Items.Clear();
                for (int j = 0; j < list_postures.Count; j++)
                { combo.Items.Add(list_postures[j]); }
            }

        }


        #endregion



        #region Search

        private int search_start_backwards(int row)
        {
            int prev_row = row - 1;
            int start_row = -1;
            string search_label = ""; 

            // search backwards
            while ( prev_row > start_row)
            {
                // check row status
                search_label = dataGridView1.Rows[prev_row].Cells[index_Status].Value.ToString();

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
                   // dataGridView1.Rows[prev_row].Cells[index_Status].Value = "start_on";  
                    prev_row = prev_row -1;
                }
                else if (search_label.CompareTo("end") == 0)
                {
                    start_row = prev_row + 1;
                    dataGridView1.Rows[start_row].Cells[index_Status].Value = "start";

                    dataGridView1.Rows[start_row].Cells[index_label_StartEnd].Value = "Start";
                    dataGridView1.Rows[start_row].Cells[index_StartID].Value = start_row;
                }
            }

            return start_row;
        }

        private int search_end_backwards(int row)
        {
            int prev_row = row - 1;
            int end_row = -1;
            string search_label = "";

            // search backwards
            while ( (prev_row > end_row) && (prev_row >-1) )
            {
                // check row status
                search_label = dataGridView1.Rows[prev_row].Cells[index_Status].Value.ToString();

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
                    // dataGridView1.Rows[prev_row].Cells[index_Status].Value = "start_on";  
                    //prev_row = prev_row - 1;
                }
                prev_row = prev_row - 1;
            }

            return end_row;
        }

        private int search_start_forward(int row, int max_rows)
        {
            int start_row = row;
            string search_label = "";

            // search backwards
            for (int i = row; i < max_rows; i++)
            {

                // check row status
                search_label = dataGridView1.Rows[i].Cells[index_Status].Value.ToString();

                if (i < (max_rows - 1))
                {
                    if (search_label.CompareTo(" ") == 0)
                    {
                        //dataGridView1.Rows[i].Cells[index_Status].Value = "start_on";
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
            string search_label = ""; 

            // search backwards
            for (int i = row; i < max_rows; i++)
            {
                
                    // check row status
                    search_label = dataGridView1.Rows[i].Cells[index_Status].Value.ToString();

                    if (i < (max_rows - 1))
                    {
                        if (search_label.CompareTo(" ") == 0)
                        {
                            //dataGridView1.Rows[i].Cells[index_Status].Value = "start_on";
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


        private int search_open_row_backwards(int row)
        {
            int open_row = search_end_backwards(row) + 1;

            while (open_row < row)
            {
                if (dataGridView1.Rows[open_row].Cells[index_Status].Value.ToString().CompareTo("start") == 0)
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
                    next_status = dataGridView1.Rows[next].Cells[index_Status].Value.ToString();

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
                //prev_cellStyle = dataGridView1.Columns[current_column].DefaultCellStyle;
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

                try
                {
                    #region Label Posture

                    if ( (column == index_label_Posture) && (is_busy ==0) )
                    {
                        bool is_label_open;
                        bool is_end_list;
                        int open_row;
                        int close_row;
                        bool is_unlocked = false;

                        string end_label = " ";
                        string start_label = " ";
                        

                        is_busy = 1;
                        is_label_open = true;
                        is_end_list = false;

                        tlabel= dataGridView1.Rows[row].Cells[column].Value.ToString();

                        if( dataGridView1.Rows[row].Cells[index_Posture_Lock].Value != null)
                        { is_unlocked = (bool) dataGridView1.Rows[row].Cells[index_Posture_Lock].Value;}

                        if (is_unlocked == true)
                        { row = check_label_lock(is_unlocked, is_label_open, row, index_label_Posture, tlabel);
                          nrows = dataGridView1.Rows.Count;
                        }

                      
                        status_tlabel = dataGridView1.Rows[row].Cells[index_Status].Value.ToString();

                        open_row = search_open_row_backwards(row);
                     
                         if( (open_row == row) || (row == 0))
                         { is_label_open = false;}

                        //======================
                         close_row = search_close_row_forward(row, nrows, open_row, is_label_open);

                         if ( (is_label_open == false) && (tlabel.CompareTo(" ") != 0))
                         {
                             if (close_row >= nrows)
                             {
                                 #region
                                 /*
                                 // need to insert an end row below
                                 dataGridView1.Rows.Insert(row + 1, 1);

                                 // update number of rows, and close_row
                                 nrows = dataGridView1.Rows.Count;
                                 close_row = row + 1;
                                 
                                 // fill "end" in inserted row and close label
                                 fill_row(close_row, 1, tlabel, -1, index_label_Posture, "end",open_row, close_row);
                             
                                  */
                                 #endregion

                                 close_row = add_end_row( row +1, out nrows,tlabel, index_label_Posture, open_row,false);
                             }
                             else if (close_row <= open_row)
                             {
                                 // if label needs to be closed, because "end" or "start_on"
                                 // perhaps do not work when the end row is separated several lines from open row
                                     close_row = add_end_row(row + 1, out nrows, tlabel, index_label_Posture, open_row, true);
                                 
                             }
                         }

                         if (close_row >= nrows)
                         {
                             close_row = nrows - 1;
                         }

                        if (dataGridView1.Rows[close_row].Cells[index_Status].Value == null)
                        { dataGridView1.Rows[close_row].Cells[index_Status].Value = " "; }
                        else if( (close_row < nrows ) &&
                            (dataGridView1.Rows[close_row].Cells[index_Status].Value.ToString().CompareTo("start") == 0))
                        {
                            #region
                            /*
                            // need to insert an end row below
                            dataGridView1.Rows.Insert(row + 1, 1);

                            // update number of rows, and close_row
                            nrows = dataGridView1.Rows.Count;
                            close_row = row + 1;

                            // fill "end" in inserted row and close label
                            fill_row(close_row, 1, tlabel,close_row +1, index_label_Posture, "end", open_row, close_row);
                            */
                            #endregion

                            close_row = add_end_row(row + 1, out nrows, tlabel, index_label_Posture, open_row, true);
                        }

                        

                         //=====================

                        if (dataGridView1.Rows[close_row].Cells[index_label_Posture].Value == null)
                        { dataGridView1.Rows[close_row].Cells[index_label_Posture].Value = " "; }

                        end_label = dataGridView1.Rows[close_row].Cells[index_label_Posture].Value.ToString();
                        
                       

                        if(is_label_open == false) 
                        {
                            if (end_label.CompareTo(" ") == 0)
                            {
                                if (tlabel.CompareTo(" ") == 1) // no blank
                                {
                                    dataGridView1.Rows[row].Cells[index_Status].Value = "start";
                                    dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                                    dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "Start";

                                   
                                    dataGridView1.Rows[row].Cells[index_EndID].Value = close_row; 
                                    

                                    if (set_status_forward(open_row, close_row, tlabel, 1, true, open_row) == -1)
                                    {
                                        System.Console.WriteLine("Error, end label was found before");
                                    }
                                    
                                }
                                else //blank 
                                {
                                    dataGridView1.Rows[row].Cells[index_Status].Value = " ";
                                    dataGridView1.Rows[row].Cells[index_StartID].Value = -1;
                                    dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = " ";

                                    dataGridView1.Rows[row].Cells[index_EndID].Value = -1;
                                    
                                    // cleanup
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
                                        dataGridView1.Rows[row].Cells[index_Status].Value = "start";

                                       
                                        dataGridView1.Rows[close_row].Cells[index_Status].Value = "end";
                                        dataGridView1.Rows[close_row].Cells[index_label_Posture].Value = tlabel;

                                        if (set_status_forward(open_row, close_row, tlabel, 1, true, open_row) == -1) 
                                        { System.Console.WriteLine("Error, end label was found before"); }


                                    }
                                    else //blank
                                    {
                                      
                                        dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = " ";
                                        dataGridView1.Rows[row].Cells[index_label_Posture].Value = " ";

                                        if (row != open_row)
                                        {
                                            dataGridView1.Rows[open_row].Cells[index_label_StartEnd].Value = " ";
                                            dataGridView1.Rows[open_row].Cells[index_label_Posture].Value = " ";
                                        }

                                        dataGridView1.Rows[close_row].Cells[index_label_StartEnd].Value = " ";
                                        dataGridView1.Rows[close_row].Cells[index_label_Posture].Value = " ";



                                        // cleanup
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
                                    //System.Console.WriteLine("This case needs to be considered");

                                    if (tlabel.CompareTo(" ") == 1) //no blank
                                    {
                                        dataGridView1.Rows[row].Cells[index_Status].Value = "start";

                                        
                                        dataGridView1.Rows[close_row].Cells[index_Status].Value = "end";
                                        dataGridView1.Rows[close_row].Cells[index_label_Posture].Value = tlabel;

                                        if (set_status_forward(open_row, close_row, tlabel, 1, true, open_row) == -1)
                                        {
                                            System.Console.WriteLine("Error, end label was found before");
                                        }
                                    }
                                    else //blank
                                    {

                                        dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = " ";
                                        dataGridView1.Rows[row].Cells[index_label_Posture].Value = " ";

                                        if (row != open_row)
                                        {
                                            dataGridView1.Rows[open_row].Cells[index_label_StartEnd].Value = " ";
                                            dataGridView1.Rows[open_row].Cells[index_label_Posture].Value = " ";
                                        }

                                        dataGridView1.Rows[close_row].Cells[index_label_StartEnd].Value = " ";
                                        dataGridView1.Rows[close_row].Cells[index_label_Posture].Value = " ";


                                        // cleanup
                                        if (set_status_forward(open_row, close_row, tlabel, 3, false, open_row) == -1)
                                        {
                                            System.Console.WriteLine("Error, end label was found before");
                                        }

                                    }


                                }
                            }
                        }
                        else //is_label_open == 1
                        {
                            if (end_label.CompareTo(" ") == 0)
                            {
                                if (tlabel.CompareTo(" ") == 0) // blank
                                {
                                    dataGridView1.Rows[row].Cells[index_Status].Value = "start_on";
                                    dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                                    dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = " ";
                                    dataGridView1.Rows[row].Cells[index_EndID].Value = -1;

                                    if (dataGridView1.Rows[row + 1].Cells[index_Status].Value.ToString().CompareTo("start") != 0) //start is not next
                                    {
                                        //close_row = search_close_row_forward(row, nrows);
                                        start_label = dataGridView1.Rows[open_row].Cells[index_label_Posture].Value.ToString();

                                        if (set_status_forward(row+1, close_row, start_label, 1, false, open_row) == -1)
                                        {
                                            System.Console.WriteLine("Error, end label was found before");
                                        }
                                    }


                                }
                                else
                                {
                                    start_label = dataGridView1.Rows[open_row].Cells[index_label_Posture].Value.ToString();

                                    if (start_label.CompareTo(tlabel) == 0)
                                    {
                                       

                                        if (status_tlabel.CompareTo("start") != 0) //different to start
                                        {
                                            // set the end
                                            dataGridView1.Rows[row].Cells[index_Status].Value = "end";
                                            dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                                            dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "End";
                                            dataGridView1.Rows[row].Cells[index_EndID].Value = row;

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
                                        if (set_status_forward(open_row, close_row, start_label,1, true, open_row) == -1)
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
                                    dataGridView1.Rows[row].Cells[index_Status].Value = "start_on";
                                    dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                                    dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = " ";
                                    dataGridView1.Rows[row].Cells[index_EndID].Value = close_row; 
                                }
                                else // if no blank
                                { 
                                   //set end
                                    start_label = dataGridView1.Rows[open_row].Cells[index_label_Posture].Value.ToString();

                                    if (start_label.CompareTo(tlabel) == 0)
                                    {
                                        if (row == close_row) //is this the end?
                                        {
                                            dataGridView1.Rows[row].Cells[index_Status].Value = "end";
                                            dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                                            dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "End";
                                            dataGridView1.Rows[row].Cells[index_EndID].Value = row;
                                        }
                                        else if (row < close_row)
                                        {
                                            dataGridView1.Rows[row].Cells[index_Status].Value = "end";
                                            dataGridView1.Rows[row].Cells[index_StartID].Value = open_row;
                                            dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "End";
                                            dataGridView1.Rows[row].Cells[index_EndID].Value = row;

                                            //cleanup the rest
                                            dataGridView1.Rows[row + 1].Cells[index_Status].Value = "start";
                                            dataGridView1.Rows[close_row].Cells[index_Status].Value = "end";

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

                        }// ends "is label open == 1"
                        
                        is_busy = 0;
                        tlabel = " ";
                        status_tlabel = " ";
                       

                    }// ends "is column posture" 
                    
                    #endregion

                    #region Label Posture Lock

                    else if ((column == index_Posture_Lock) && (is_busy == 0))  // Lock index activated
                    { 
                        bool is_unlocked = false;
                        int open_row = row;
                        tlabel = " ";

                        if(  dataGridView1.Rows[row].Cells[index_StartID].Value != null)
                        { open_row = (int)dataGridView1.Rows[row].Cells[index_StartID].Value;}

                        if (dataGridView1.Rows[row].Cells[index_Posture_Lock].Value != null)
                        {
                            is_unlocked = (bool)dataGridView1.Rows[row].Cells[index_Posture_Lock].Value;
                        }

                        if (is_unlocked) // set combo to full == 2
                        {
                            set_ComboBox(cellComboBox, row, index_label_Posture, 2, "");
                        }
                        else // set combo to simple == 1
                        {
                            if (dataGridView1.Rows[open_row].Cells[index_label_Posture].Value  != null)
                            { tlabel = dataGridView1.Rows[open_row].Cells[index_label_Posture].Value.ToString(); }

                            set_ComboBox(cellComboBox, row, index_label_Posture, 1, tlabel);
                        }

                    }
                    #endregion

                    #region Label Posture Start/End

                    else if (column == index_label_StartEnd)
                    {
                        string prev_status_label = " ";
                        string status_label = " ";
                        string next_label = " ";
                        string start_label = " ";
                        string end_label = " ";

                        int next_end = row+1;

                          if( is_busy == 0)
                         {
                             status_label= dataGridView1.Rows[row].Cells[column].Value.ToString();

                             if( status_label.CompareTo("Start") == 0)
                             {
                                 dataGridView1.Rows[row].Cells[index_Status].Value = "start";
                                 dataGridView1.Rows[row].Cells[index_StartID].Value = row;
                                 
                                 // search the end forwards (update all cells)
                                 //dataGridView1.Rows[row].Cells[index_EndID].Value = -1;

                             }
                             else if (status_label.CompareTo("End") == 0)
                             {
                                 dataGridView1.Rows[row].Cells[index_Status].Value = "end";
                                 dataGridView1.Rows[row].Cells[index_EndID].Value = row;

                                 if (row > 0)
                                 {
                                     // search the start backwards (update all cells)
                                     if (dataGridView1.Rows[row - 1].Cells[index_label_Posture].Value != null)
                                     {  start_label = dataGridView1.Rows[row - 1].Cells[index_label_Posture].Value.ToString();}
                                     
                                     if (dataGridView1.Rows[row].Cells[index_label_Posture].Value != null)
                                     {end_label = dataGridView1.Rows[row].Cells[index_label_Posture].Value.ToString();}

                                     if (dataGridView1.Rows[row+1].Cells[index_label_Posture].Value != null)
                                     { next_label = dataGridView1.Rows[row+1].Cells[index_label_Posture].Value.ToString(); }


                                     if(start_label.CompareTo(end_label) != 0) 
                                     {
                                         if (dataGridView1.Rows[row - 1].Cells[index_Status].Value != null)
                                         { prev_status_label = dataGridView1.Rows[row - 1].Cells[index_Status].Value.ToString(); }
                                    
                                        if (prev_status_label.CompareTo("end") == 0)
                                         {
                                             //insert a start
                                             add_start_row(row, out nrows, end_label, index_label_Posture, row + 1, true);

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
                                             // if not similar, set label to start label, lock combo and sent message
                                             set_ComboBox(cellComboBox, row, index_label_Posture, 1, start_label);

                                             dataGridView1.Rows[row].Cells[index_label_Posture].Value = start_label;
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
                                            { close_row = nrows -1; }
                                            else if (close_row <= open_row)
                                            {
                                                close_row = row + 1;
                                            }

                                            if (is_label_open == false)
                                            {
                                                // this end label is wrong, 
                                                // only start is possible if next_end > row
                                             
                                                    dataGridView1.Rows[row].Cells[index_Status].Value = "start";
                                                    dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "Start";
                                                    
                                                   if (set_status_forward(row, close_row, end_label, 1, true, open_row) == -1)
                                                    { System.Console.WriteLine("Error, end label was found before");}

                                                    label_play.Text = "The END Label could not be set. START/ERROR mismatch. To modified it, edit the START label.";
                                            }
                                        }
                                     }

                                     // if row and next similar
                                     if( end_label.CompareTo( next_label) == 0 )
                                     {

                                         if (dataGridView1.Rows[row +1].Cells[index_Status].Value != null)
                                         { prev_status_label = dataGridView1.Rows[row +1].Cells[index_Status].Value.ToString(); }

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
                                                     end_label = dataGridView1.Rows[next_end].Cells[index_label_Posture].Value.ToString();

                                                     dataGridView1.Rows[row].Cells[index_Status].Value = "start";
                                                     dataGridView1.Rows[row].Cells[index_label_StartEnd].Value = "Start";
                                                     dataGridView1.Rows[row].Cells[index_label_Posture].Value = end_label;

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
                                 dataGridView1.Rows[row].Cells[index_Status].Value = " ";
                                 //dataGridView1.Rows[row].Cells[index_StartID].Value = -1;
                                 //dataGridView1.Rows[row].Cells[index_EndID].Value = -1;
                                 dataGridView1.Rows[row].Cells[index_label_Posture].Value = " ";
                             }
                            
                         }
                         
                    }
                    #endregion 

                    #region Activity
                    else if (column == index_label_Activity)
                    {

                    }
                    #endregion

                }// finish try
                catch
                {
                    if( (tlabel.CompareTo(" ") != 0) && (is_busy == 1))
                    {
                        is_busy = 0;
                    }
                    //System.Console.WriteLine("Data Error Event");
                   
                }

            }// finish if
        }
        
        private void dataGridView1_DataError(object sender, DataGridViewDataErrorEventArgs e)
        {
            e.Cancel = true;

        } //finish class


        private void FormAnnotation_Load(object sender, EventArgs e)
        {
            //-----
            this.dataGridView1.Left = (int)System.Math.Round(0.025 * this.Width);
            this.dataGridView1.Width = (int)System.Math.Round(0.95 * this.Width);
           
            this.dataGridView1.Height = (int)System.Math.Round(0.65 * this.Height);

           
        }


        private void FormAnnotation_Resize(object sender, EventArgs e)
        {
            this.dataGridView1.Left = (int)System.Math.Round(0.025 * this.Width);
            this.dataGridView1.Width = (int)System.Math.Round(0.95 * this.Width);
            //this.dataGridView1.Left = (int)System.Math.Round((this.Width - this.dataGridView1.Width) / 2.0);

            this.dataGridView1.Height = (int)System.Math.Round(0.7 * this.Height);
        }




        #endregion


        #region XML



        public void LoadActivityLabels()
        {


            string labels_file_name = DataSessionDir + "ActivityLabelsRealtime.xml";

            if (File.Exists(labels_file_name))
            {
                XmlSession.FromXML(labels_file_name);


                for (int i = 0; i < XmlSession.OverlappingActivityLists.Count; i++)
                {
                    CActivityList.Add(XmlSession.OverlappingActivityLists[i]);

                    list_categories.Add(CActivityList[i]._Name);

                    Activity[] actArray = CActivityList[i].ToArray();

                    list_postures.Add(" ");
                    
                    for (int j = 0; j < CActivityList[i].Count - 1; j++)
                    {

                        list_postures.Add(actArray[j]._Name);

                    }
                }

            }
            else
            { label_play.Text = "ActivityLabelsRealtime.xml file location is not valid. Please make sure the file is in the WocketsFiles directory."; }
                   
        }

        private void GenerateActivityLabels()
        { 
           // read the values
           // check all the labels match
           // when ok, fill the records

            int start_row=0;
            int end_row=0;
            int category=-1;

            string label_start;
            string label_end;
            
            string start_time;
            string end_time;

            //string category_name="none";
            string record_string;

            TextWriter txw = new StreamWriter(DataSessionDir + "DataLabels.txt");

            LabelsList.Clear();
            nrows = dataGridView1.Rows.Count;

            txw.WriteLine(StartDate+ ";"+ EndDate + ";");

            start_row = search_start_forward(start_row, nrows);
            end_row = search_close_row_forward(start_row, nrows, start_row, true);

            while (end_row < nrows)
            {
                label_start = dataGridView1.Rows[start_row].Cells[index_label_Posture].Value.ToString();
                label_end = dataGridView1.Rows[end_row].Cells[index_label_Posture].Value.ToString();
                
                start_time = dataGridView1.Rows[start_row].Cells[index_label_Time].Value.ToString();
                end_time = dataGridView1.Rows[end_row].Cells[index_label_Time].Value.ToString();


                if (start_row < end_row)
                {
                    
                    //search for the category
                    category = -1;

                    for (int i = 0; i < list_postures.Count; i++)
                    {
                        label_end = list_postures[i];

                        if (label_end.CompareTo(" ") == 0)
                        { category = category + 1; }

                        if (label_start.CompareTo(label_end) == 0)
                        {
                            break;
                        }
                    }


                    // record is correct
                    if (label_start.CompareTo(label_end) == 0)
                    {

                        //write record to list
                        record_string = start_row.ToString() +  ";" + end_row.ToString()  + ";" +
                                        start_time.ToString() + ";" + end_time.ToString() + ";" +
                                        label_start + ";" + list_categories[category];


                        txw.WriteLine(record_string);
                        LabelsList.Add(record_string);

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
                }
                else
                {
                    //record is incorrect
                    end_row = nrows;
                    label_play.Text = "The label in rows: " + start_row.ToString() +
                                      " and " + end_row.ToString() + " are incorrect. Please check.";

                    //write record to list
                    record_string = start_row.ToString()  + ";" + end_row.ToString()  + ";" +
                                    start_time.ToString() + ";" + end_time.ToString() + ";" +
                                    label_start + ";" + list_categories[category] + ";**" ;

                    txw.WriteLine(record_string);
                    LabelsList.Add(record_string);
                }
            }

            txw.Close();

            label_play.Text = "The Xml file has been generated.";

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
       
        
        public static bool IsValidDirectory(string aDirPath)
        {
            //string subjectDataFile = aDirPath + "\\SubjectData.xml";
            //string sensorDataFile = aDirPath + "\\SensorData.xml";
            //string activityLabelsFile = aDirPath + "\\ActivityLabelsRealtime.xml";
            
            string activityLabelsFile = "ActivityLabelsRealtime.xml";

            if (//File.Exists(subjectDataFile) &&
                //File.Exists(sensorDataFile) &&
                File.Exists(activityLabelsFile))
                return true;
            else
                return false;

            
        }

       
        #endregion


        #region Load/Save buttons

        private void button_save_Click(object sender, EventArgs e)
        {
           
                SaveRowsToGrid(DataSessionName);
               

        }

        private void button_2_Click(object sender, EventArgs e)
        {
            // Check if the audio files path exist
            DirectoryInfo directory = new DirectoryInfo(textBox_1.Text);

            if (directory.Exists)
            {

                DataAudioDir = directory.FullName;

                //Initialize Components
                // create a player to be used in the application
                myPlayer = new System.Media.SoundPlayer();

                //Fill datagridview settings
                InitializeDataGridView(dataGridView1);

                LoadData();

                LoadViewGrid("grid");
            }
            else
            { 
               // send a warning saying that directory doesn't exist.
            }

        }


        private void LoadViewGrid(string vw)
        {
            if (vw.CompareTo("grid") == 0)
            {
                //------ hide ------------
                textBox_1.Visible = false;
                textBox_2.Visible = false;
                textBox_instructions.Visible = false;

                button_1.Visible = false;
                button_2.Visible = false;

                //------ show ------------
                button_add_label.Visible = true;
                button_remove_label.Visible = true;

                button_save.Visible = true;
                button_generate.Visible = true;

                button_exit.Visible = true;

                dataGridView1.Visible = true;
                
                label_play.Visible = true;
                
                label_date.Visible = true;
                label_date.Text = "Session Date: "+ StartDate;

                label_instructions_1.Text = "Press F1 to play audio file. Press F2 to edit field.";
                label_instructions_2.Text = "Status:";

                //---------------------------



            }
            else if (vw.CompareTo("select") == 0)
            { 
            
            }
        }

        private void button_generate_Click(object sender, EventArgs e)
        {

            GenerateActivityLabels();

        }

        private void button_exit_Click(object sender, EventArgs e)
        {

            SaveRowsToGrid(DataSessionName);
            Application.Exit();
        }

        #endregion







    }
}