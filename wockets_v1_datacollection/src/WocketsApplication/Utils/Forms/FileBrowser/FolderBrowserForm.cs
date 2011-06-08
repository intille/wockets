//
// FolderBrowserForm
// Underlying implementation of the FolderBrowserDialog
// (c) 2004 Peter Foot, OpenNETCF
//
using System;
using System.Drawing;
using System.IO;
using System.Windows.Forms;
using WocketsApplication;

namespace WocketsApplication.Utils.Forms.FileBrowser
{
	/// <summary>
	/// Presents a dialog allowing the user to browse the file system on the device.
	/// </summary>
	internal class FolderBrowserForm : Form
	{
		private System.Windows.Forms.MainMenu mainMenu1;
		private System.Windows.Forms.ImageList ilIcons;
		private System.Windows.Forms.TreeView tvFolders;
		private System.Windows.Forms.MenuItem mnuDone;
		private System.Windows.Forms.MenuItem mnuCancel;
		private System.Windows.Forms.MenuItem mnuMenu;
		private System.Windows.Forms.MenuItem mnuNew;
		private string m_selectedpath;


        private void InitializeInterface()
        {
            this.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
            this.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
            if ((this.Width > Constants.MAX_FORM_WIDTH) || (this.Height > Constants.MAX_FORM_HEIGHT))
            {
                this.Width = this.Width / 4;
                this.Height = this.Height / 2;
            }
            this.tvFolders.DoubleClick += new EventHandler(tvFolders_DoubleClick);            
            this.AutoScroll = true;            
        }
		private void InitializeComponent()
		{
			this.tvFolders = new System.Windows.Forms.TreeView();
			this.ilIcons = new System.Windows.Forms.ImageList();
			this.mainMenu1 = new System.Windows.Forms.MainMenu();
			this.mnuDone = new System.Windows.Forms.MenuItem();
			this.mnuMenu = new System.Windows.Forms.MenuItem();
			this.mnuNew = new System.Windows.Forms.MenuItem();
			this.mnuCancel = new System.Windows.Forms.MenuItem();
			// 
			// tvFolders
			// 
			this.tvFolders.ImageList = this.ilIcons;
			this.tvFolders.Location = new System.Drawing.Point(8, 32);
			this.tvFolders.ShowRootLines = false;
			this.tvFolders.Size = new System.Drawing.Size(152, 112);
			this.tvFolders.AfterSelect += new System.Windows.Forms.TreeViewEventHandler(this.tvFolders_AfterSelect);

           
			// 
			// ilIcons
			// 
			this.ilIcons.ImageSize = new System.Drawing.Size(16, 16);
			// 
			// mainMenu1
			// 
			this.mainMenu1.MenuItems.Add(this.mnuDone);
			this.mainMenu1.MenuItems.Add(this.mnuMenu);
			// 
			// mnuDone
			// 
			this.mnuDone.Text = "Select";
			this.mnuDone.Click += new System.EventHandler(this.mnuDone_Click);
			// 
			// mnuMenu
			// 
			//this.mnuMenu.MenuItems.Add(this.mnuNew);
			//this.mnuMenu.MenuItems.Add(this.mnuCancel);
			this.mnuMenu.Text = "Cancel";
            this.mnuMenu.Click+= new System.EventHandler(this.mnuCancel_Click);
			// 
			// mnuNew
			// 
			//this.mnuNew.Enabled = false;
			//this.mnuNew.Text = "New Folder";
			//this.mnuNew.Click += new System.EventHandler(this.mnuNew_Click);
			// 
			// mnuCancel
			// 
			//this.mnuCancel.Text = "Cancel";
			//this.mnuCancel.Click += new System.EventHandler(this.mnuCancel_Click);
			// 
			// InnerFolderBrowserDialog
			// 
			this.ClientSize = new System.Drawing.Size(170, 175);
			this.ControlBox = false;
			this.Controls.Add(this.tvFolders);
			this.MaximizeBox = false;
			this.Menu = this.mainMenu1;
			this.MinimizeBox = false;
			this.Text = "Browse for Folder";
			this.Resize += new System.EventHandler(this.FolderBrowserDialog_Resize);


		}

        void tvFolders_DoubleClick(object sender, EventArgs e)
        {
            //user made a selection return OK
            this.DialogResult = DialogResult.OK;

            this.Close();
        }


        public FolderBrowserForm()
        {

            //
            // TODO: Add constructor logic here
            //
            InitializeComponent();
            InitializeInterface();

            //add folder images to imagelist
            ilIcons.Images.Add(new System.Drawing.Bitmap(FileBrowserImages.Folder));
#if (PocketPC)
            ilIcons.Images.Add(new System.Drawing.Bitmap(FileBrowserImages.Device));
#else
            ilIcons.Images.Add(new System.Drawing.Bitmap(FileBrowserImages.PC));
#endif
            ilIcons.Images.Add(new System.Drawing.Bitmap(FileBrowserImages.Card));

            //set default image index to 0
            tvFolders.ImageIndex = 0;
            tvFolders.SelectedImageIndex = 0;

            //use a backslash between path levels
            tvFolders.PathSeparator = "\\";

            //setup default tree
            Reset();
        }
		

		#region Public Properties

		/// <summary>
		/// Gets or sets the path selected by the user.
		/// </summary>
		public string SelectedPath
		{
			get
			{
				return m_selectedpath;
			}
			set
			{
				//check that value passed is a valid file system path
				if(Directory.Exists(value))
				{
					m_selectedpath = value;

					//split the path into each folder layer
					string[] layers = value.Split('\\');

					//mark the current node
					TreeNode tn = tvFolders.Nodes[0];

					//loop through the folder levels
					foreach(string folderlevel in layers)
					{
						//ignore blank (top-level node)
						if(folderlevel!="")
						{
							//add sub-folders
							AddFolders(tn);

							//find the required subfolder
							foreach(TreeNode thisnode in tn.Nodes)
							{
								//check node text
								if(thisnode.Text ==folderlevel)
								{
									//if it does set it and continue processing the next level
									tn = thisnode;
									break;
								}
							}
						}
					}

					//select the final node
					tvFolders.SelectedNode = tn;

				}
			}
		}

		/// <summary>
		/// Gets or sets a value indicating whether the New Folder item appears in the menu.
		/// </summary>
		public bool ShowNewFolderButton
		{
			get
			{
				return mnuNew.Enabled;
			}
			set
			{
				mnuNew.Enabled = value;
			}
		}
		#endregion

		#region Helper Functions

		/// <summary>
		/// Adds the root node for the device to the TreeView
		/// </summary>
		private void AddRoot()
		{
			//stop updates during filling
			tvFolders.BeginUpdate();

			//add an empty node (use device image)
			TreeNode root = tvFolders.Nodes.Add("");
			root.ImageIndex = 1;
			root.SelectedImageIndex = 1;

			tvFolders.EndUpdate();
		}

		/// <summary>
		/// Adds subfolders to a specified node in the tree
		/// </summary>
		/// <param name="tn">Node to add sub-folders to</param>
		private void AddFolders(TreeNode tn)
		{
			//stop updates during filling
			tvFolders.BeginUpdate();

			//path to query for subfolders
			string path;

			if(tn.FullPath=="")
			{
				//for blank path (root) substitute '\'
				path = "\\";
			}
			else
			{
				//use the nodes full path
				path = tn.FullPath;
			}

			//clear existing subnodes if present
			tn.Nodes.Clear();

			//get all folders beneath the selected node
			foreach(string directory in System.IO.Directory.GetDirectories(path))
			{
				TreeNode newnode = new TreeNode();
				//format human friendly name
				newnode.Text = directory.Substring(directory.LastIndexOf("\\")+1, directory.Length - directory.LastIndexOf("\\")-1);
				
				//change icon if folder is a storage card
				DirectoryInfo di = new DirectoryInfo(directory);
				if((di.Attributes & FileAttributes.Temporary) == FileAttributes.Temporary)
				{
					newnode.ImageIndex = 2;
					newnode.SelectedImageIndex = 2;
				}

				//add to root of tree
				tn.Nodes.Add(newnode);
			}

			//restore events etc
			tvFolders.EndUpdate();
		}

		/// <summary>
		/// Resets properties to their default values.
		/// </summary>
		public void Reset()
		{
			//restores dialog to initial settings and repopulates folders
			this.m_selectedpath = "";
			tvFolders.Nodes.Clear();

			//add the root (device) node to the tree
			AddRoot();

			//add root level subfolders
			AddFolders(tvFolders.Nodes[0]);

			//expand the top level folders
			tvFolders.Nodes[0].Expand();
		}
		#endregion

		#region Event Handlers

		/// <summary>
		/// Handles dynamic sizing of the dialog contents to the available screen space
		/// </summary>
		/// <param name="sender"></param>
		/// <param name="e"></param>
		private void FolderBrowserDialog_Resize(object sender, System.EventArgs e)
		{
			//set the control to fill the available screen space
			tvFolders.Bounds = new Rectangle(-1, -1, Screen.PrimaryScreen.WorkingArea.Width + 2, Screen.PrimaryScreen.WorkingArea.Height + 2);
		}

		/// <summary>
		/// Handles selection of a tree node
		/// </summary>
		/// <param name="sender">Sender of the event (in this case always tvFolders)</param>
		/// <param name="e">Describes the event.</param>
		private void tvFolders_AfterSelect(object sender, System.Windows.Forms.TreeViewEventArgs e)
		{
			
				//set the currently selected folder
				if(tvFolders.SelectedNode.FullPath=="")
				{
					//the root node is returned from the tree as "" but for the filsystem we need this to be "\"
					m_selectedpath = "\\";
				}
				else
				{
					//for all other folders the fullpath directly matches the filesystem path
					m_selectedpath = tvFolders.SelectedNode.FullPath;
				}

				//if there are no child nodes we will check for any and add them
				if(tvFolders.SelectedNode.Nodes.Count==0)
				{
					AddFolders(tvFolders.SelectedNode);		
				}
		}

		private void mnuDone_Click(object sender, System.EventArgs e)
		{
			//user made a selection return OK
			this.DialogResult = DialogResult.OK;
            this.Close();
		}

		private void mnuCancel_Click(object sender, System.EventArgs e)
		{
			//user aborted selection
            this.Close();
		}

		private void mnuNew_Click(object sender, System.EventArgs e)
		{
			//get a name
			string foldername = Microsoft.VisualBasic.Interaction.InputBox("Enter new folder name", "Create Folder", "New Folder", 0, 0);

			//if user cancelled take no further action
			if(foldername != "")
			{
				//try to create a folder
				try
				{
					//call IO function to create the specified directory
					string newpath = tvFolders.SelectedNode.FullPath + "\\" + foldername;
					Directory.CreateDirectory(newpath);

					//refresh tree
					TreeNode newnode = tvFolders.SelectedNode.Nodes.Add(foldername);
					//select new folder
					tvFolders.SelectedNode = newnode;
					
				}
				catch
				{
					//warn the user
					MessageBox.Show("Error creating folder", "Create Folder", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button1);
					return;
				}
			}
		}
		#endregion

		
	}
}
