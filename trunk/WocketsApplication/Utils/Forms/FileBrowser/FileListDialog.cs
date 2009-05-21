//
// Internal implementation of a list of files in a specific folder
// Designed for Smartphone devices
// (c) 2004 Peter Foot, OpenNETCF
//
using System;
using System.Drawing;
using System.Collections;
using System.ComponentModel;
using System.Windows.Forms;
using System.IO;
using WocketsApplication;

namespace WocketsApplication.Utils.Forms.FileBrowser
{
	/// <summary>
	/// Summary description for FileListDialog.
	/// </summary>
	internal class FileListDialog : System.Windows.Forms.Form
	{
		private System.Windows.Forms.MainMenu mnuFile;
        private System.Windows.Forms.MenuItem mnuOpen;
		private System.Windows.Forms.ListView lvFiles;

		//default to all files shown
		private string m_filterstring = "All Files|*.*";
		private string[] m_filter = new string[2]{"All Files", "*.*"};
		private int m_filterindex = 1;
		//default to users documents folder
		private string m_path = Environment.GetFolderPath(Environment.SpecialFolder.Personal);
		private string m_filename = "";

		private FileBrowserDialog m_fbd;

		private System.Windows.Forms.ColumnHeader clmName;
        private MenuItem menuItem1;
        private System.Windows.Forms.ColumnHeader clmPath;

        public string FilePath
        {
            set
            {
                this.m_path = value;
            }
        }

		public FileListDialog()
		{
			//
			// Required for Windows Form Designer support
			//
			InitializeComponent();

			//
			// TODO: Add any constructor code after InitializeComponent call
			//
			m_fbd = new FileBrowserDialog();
		}

		/// <summary>
		/// Clean up any resources being used.
		/// </summary>
		protected override void Dispose( bool disposing )
		{
			m_fbd.Dispose();

			base.Dispose( disposing );
		}

		#region Windows Form Designer generated code
		/// <summary>
		/// Required method for Designer support - do not modify
		/// the contents of this method with the code editor.
		/// </summary>
		private void InitializeComponent()
		{
            this.lvFiles = new System.Windows.Forms.ListView();
            this.clmName = new System.Windows.Forms.ColumnHeader();
            this.clmPath = new System.Windows.Forms.ColumnHeader();
            this.mnuFile = new System.Windows.Forms.MainMenu();
            this.mnuOpen = new System.Windows.Forms.MenuItem();
            this.menuItem1 = new System.Windows.Forms.MenuItem();
            this.SuspendLayout();
            // 
            // lvFiles
            // 
            this.lvFiles.Columns.Add(this.clmName);
            this.lvFiles.Columns.Add(this.clmPath);
            this.lvFiles.FullRowSelect = true;
            this.lvFiles.HeaderStyle = System.Windows.Forms.ColumnHeaderStyle.None;
            this.lvFiles.Location = new System.Drawing.Point(16, 40);
            this.lvFiles.Name = "lvFiles";
            this.lvFiles.Size = new System.Drawing.Size(176, 200);
            this.lvFiles.TabIndex = 0;
            this.lvFiles.View = System.Windows.Forms.View.SmallIcon;
            this.lvFiles.ItemActivate += new System.EventHandler(this.lvFiles_ItemActivate);
            // 
            // clmName
            // 
            this.clmName.Text = "Name";
            this.clmName.Width = 160;
            // 
            // clmPath
            // 
            this.clmPath.Text = "Path";
            this.clmPath.Width = 1;
            // 
            // mnuFile
            // 
            this.mnuFile.MenuItems.Add(this.mnuOpen);
            this.mnuFile.MenuItems.Add(this.menuItem1);
            // 
            // mnuOpen
            // 
            this.mnuOpen.Text = "Select";
            this.mnuOpen.Click += new System.EventHandler(this.mnuOpen_Click);
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "Cancel";
            this.menuItem1.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // FileListDialog
            // 
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Inherit;
            this.ClientSize = new System.Drawing.Size(218, 315);
            this.ControlBox = false;
            this.Controls.Add(this.lvFiles);
            this.MaximizeBox = false;
            this.Menu = this.mnuFile;
            this.MinimizeBox = false;
            this.Name = "FileListDialog";
            this.Text = "Choose a file";
            this.Resize += new System.EventHandler(this.FileListDialog_Resize);
            this.ResumeLayout(false);

		}
		#endregion

		#region Public Properties

		/// <summary>
		/// The name of the selected file.
		/// </summary>
		public string FileName
		{
			get
			{
				return m_filename;
			}
		}

		/// <summary>
		/// 
		/// </summary>
		public string Filter
		{
			get
			{
				return m_filterstring;
			}
			set
			{
				m_filterstring = value;
				
				ArrayList filterbuilder = new ArrayList();
				
				//split the string and add items to arraylist
				foreach(string filtersection in m_filterstring.Split('|'))
				{
					//add filter to arraylist
					filterbuilder.Add(filtersection);
				}

				m_filter = (string[])filterbuilder.ToArray(typeof(string));

				//update the file list
				RefreshList();
			}
		}

		/// <summary>
		/// 
		/// </summary>
		public int FilterIndex
		{
			get
			{
				return m_filterindex;
			}
			set
			{
				if(value <= (m_filter.Length / 2) & value > 0)
				{
					m_filterindex = value;

					//update the listing
					RefreshList();
				}
				else
				{
					throw new ArgumentOutOfRangeException("FilterIndex greater than length of Filter collection");
				}
			}
		}

		/// <summary>
		/// The folder in which files will be listed.
		/// </summary>
		public string InitialDirectory
		{
			get
			{
				return m_path;
			}
			set
			{
				if(System.IO.Directory.Exists(value))
				{
					//set the path
					m_path = value;

					//reset the list
					RefreshList();
				}
				else
				{
					//throw an exception
					throw new ArgumentException("The specified path does not exist");
				}
				
			}
		}
		#endregion

		#region Refresh List
		/// <summary>
		/// Refreshes the list of files for the selected folder.
		/// </summary>
		internal void RefreshList()
		{
			Cursor.Current = Cursors.WaitCursor;

			//clear the list
			lvFiles.Items.Clear();

			//suspend events during updating
			lvFiles.BeginUpdate();

			//select the filter pointed to by the filterindex
			string selectedfilter = m_filter[(m_filterindex * 2) - 1];

			//support multiple filetype filters
			foreach(string thisfilter in selectedfilter.Split(';'))
			{
				
				//get all files of specified type in specified folder
				foreach(string filename in System.IO.Directory.GetFiles(m_path, thisfilter))
				{
					//get info on file
					FileInfo fi = new FileInfo(filename);

					//don't add hidden files to the list
					if((fi.Attributes & FileAttributes.Hidden) != FileAttributes.Hidden)
					{
                        int last_index = -1;
                        ListViewItem lviNew;
						//create new item with filename minus extension
                        if ((last_index=fi.Name.LastIndexOf(".")) >0)
                            lviNew = new ListViewItem(new string[] { fi.Name.Substring(0, last_index), fi.FullName });
                        else
                            lviNew = new ListViewItem(new string[] { fi.Name, fi.FullName });

						//add to list
						lvFiles.Items.Add(lviNew);
					}
				}
			}

			//disable open menu item when there are no files
			if(lvFiles.Items.Count==0)
			{
				mnuOpen.Enabled = false;
			}
			else
			{
				mnuOpen.Enabled = true;
			}

			//restore events to list
			lvFiles.EndUpdate();

			//set focus to list
			lvFiles.Focus();

			Cursor.Current = Cursors.Default;
		}
		#endregion

		#region Rename Click
		/// <summary>
		/// Handles when the user clicks the Rename button
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void mnuRename_Click(object sender, System.EventArgs e)
		{
			//only act if there is currently a selected file
			if(lvFiles.SelectedIndices.Count==1)
			{
				//get current item name
				string currentname = lvFiles.Items[lvFiles.SelectedIndices[0]].Text;
				
				//prompt user for new name
                string newname = "";//Microsoft.VisualBasic.Interaction.InputBox("Name:", "Rename file", currentname, 0, 0);
			
				//on ok
				if(newname!="")
				{
					//rename the file (by moving it)
					System.IO.File.Move(m_path + currentname, m_path + newname);
				}
			}
		}
		#endregion

		#region Form Resize
		/// <summary>
		/// Allows the form to dynamically resize.
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void FileListDialog_Resize(object sender, System.EventArgs e)
		{
			//fill screen with list
			lvFiles.Bounds = new Rectangle(-1, -1, Screen.PrimaryScreen.WorkingArea.Width + 2, Screen.PrimaryScreen.WorkingArea.Height + 2);
		}
		#endregion

		#region Open Click
		/// <summary>
		/// Handles user clicking the Open button
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void mnuOpen_Click(object sender, System.EventArgs e)
		{
			if(lvFiles.SelectedIndices.Count==1)
			{
				m_filename = lvFiles.Items[lvFiles.SelectedIndices[0]].SubItems[1].Text;
				DialogResult = DialogResult.OK;
                
			}
		}
		#endregion

		#region List Item
		/// <summary>
		/// Captures selection in the file list
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void lvFiles_ItemActivate(object sender, System.EventArgs e)
		{
			//only act if there is currently an item selected
			if(lvFiles.SelectedIndices.Count==1)
			{
				m_filename = lvFiles.Items[lvFiles.SelectedIndices[0]].SubItems[1].Text;
				DialogResult = DialogResult.OK;
			}
		}
		#endregion

		#region Change Click
		/// <summary>
		/// Handles when user chooses to change the current folder
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void mnuChange_Click(object sender, System.EventArgs e)
		{
			//create new folderbrowserdialog
			m_fbd.SelectedPath = this.InitialDirectory;

			//if user selects a new folder
			if(m_fbd.ShowDialog() == DialogResult.OK)
			{
				//reset the folder to the newly chosen one
				InitialDirectory = m_fbd.SelectedPath;
				//refresh the file list
				RefreshList();
			}
		}
		#endregion

		#region Cancel Click
		/// <summary>
		/// Handles user clicking Cancel - returns with no selection
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void mnuCancel_Click(object sender, System.EventArgs e)
		{
			//return with no selection
			this.DialogResult = DialogResult.Cancel;
		}
		#endregion

        private void menuItem1_Click(object sender, EventArgs e)
        {
            this.Close();
        }
	}
}
