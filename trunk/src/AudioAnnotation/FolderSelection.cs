using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;



namespace TestApplication_Annotation
{
    public partial class FolderSelection : Form
    {
        private static string driveLetters = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        private DirectoryInfo folder;
        //private System.Windows.Forms.ImageList imageList1;
        private string sCurPath = "";
        private TextWriter tw;
        private TextReader tr;
        //private FileStream spath;


        public FolderSelection(string spath)
        {
            InitializeComponent();
            fillTree(spath);
           
        }


        /// <summary> method fillTree
        /// <para>This method is used to initially fill the treeView control with a list
        /// of available drives from which you can search for the desired folder.</para>
        /// </summary>
        private void fillTree(string spath)
        {
            DirectoryInfo directory;


            //string pathAPI = Application.StartupPath;

            //FileInfo file_session = new FileInfo("AudioDirPath.txt");

             
              // if (file_session.Exists == false)
            // {
             //    tw = new StreamWriter("DataInputPath.txt");
                 //tw.Write(folder.FullName);
             //    tw.Close();

             //}
             

                 if (spath.CompareTo("") == 0)
                 {
                     //tr = new StreamReader("DataInputPath.txt");
                     //sCurPath = tr.ReadLine();
                     //tr.Close();

                     sCurPath = Application.StartupPath;
                 }
                 else
                 {
                     sCurPath = spath;
                 }
             

          

            // clear out the old values
            treeView1.Nodes.Clear();

            //  If no path has been specified before, 
            //  loop through the drive letters and find the available drives.            
            if(sCurPath== null)
            { sCurPath = "";  }

            if ( sCurPath.CompareTo("") == 0 )
            {
                foreach (char c in driveLetters)
                {
                    sCurPath = c + ":\\";
                    try
                    {
                        // get the directory informaiton for this path.
                        directory = new DirectoryInfo(sCurPath);

                        // if the retrieved directory information points to a valid
                        // directory or drive in this case, add it to the root of the 
                        // treeView.
                        if (directory.Exists == true)
                        {
                            TreeNode newNode = new TreeNode(directory.FullName);
                            treeView1.Nodes.Add(newNode);	// add the new node to the root level.
                            getSubDirs(newNode);			// scan for any sub folders on this drive.
                        }                    
                    }
                    catch (Exception doh)
                    {
                        Console.WriteLine(doh.Message);
                    }
                }
            }
            else
            {
                try
                {
                    // get the directory informaiton for previous path.
                    directory = new DirectoryInfo(sCurPath);

                    if (directory.Exists == true)
                    {   
                        LoadFoldersInTreeView(treeView1, directory);
                       
                    }
                }
                catch (Exception doh)
                {
                    Console.WriteLine(doh.Message);
                }
            
            }
        }


        //==================================================
        // Load folders in a tree view
        //==================================================

        void LoadFoldersInTreeView(TreeView treeName, DirectoryInfo directory)
        {
            string spath1 = directory.FullName;
            int endstr = spath1.LastIndexOf("\\");
            string spath2 = "";
            int prev =0;
            int next = 0;
            int i = -1;

            TreeNodeCollection prevNodes = null;
            DirectoryInfo dpath;
           
            treeName.BeginUpdate();

            
            while (next < spath1.Length)
            {
                prev = next;
               
                if (prev < endstr)
                {
                    next = spath1.IndexOf("\\", prev + 1);
                    
                    if ((next + 1) < spath1.Length)
                    { 
                        spath2 = spath1.Remove(next + 1); 
                    }
                    else
                    {
                        spath2 = spath1;
                        next = spath1.Length;
                    }
                }
                else
                {
                    spath2 = spath1;
                    next = spath1.Length;
                }


                dpath = new DirectoryInfo(spath2);

                if (i < 0)
                {              
                    treeName.Nodes.Add(dpath.Name);
                    prevNodes = treeName.Nodes;
                }
                else
                {
                    prevNodes[0].Nodes.Add(dpath.Name);
                    prevNodes = prevNodes[0].Nodes;
                }
                i++;

                           
                treeName.ExpandAll();

            }

            treeName.EndUpdate();

        }
 
       

        /// <summary> method getSubDirs
        /// <para>this function will scan the specified parent for any subfolders 
        /// if they exist.  To minimize the memory usage, we only scan a single 
        /// folder level down from the existing, and only if it is needed.</para>
        /// <param name="parent">the parent folder in which to search for sub-folders.</param>
        /// </summary>
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


        /// <summary> method fixPath
        /// <para>For some reason, the treeView will only work with paths constructed like the following example.
        /// "c:\\Program Files\Microsoft\...".  What this method does is strip the leading "\\" next to the drive
        /// letter.</para>
        /// <param name="node">the folder that needs it's path fixed for display.</param>
        /// <returns>The correctly formatted full path to the selected folder.</returns>
        /// </summary>
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

        private void treeView1_BeforeSelect(object sender, TreeViewCancelEventArgs e)
        {
            getSubDirs(e.Node);					// get the sub-folders for the selected node.
            textBox1.Text = fixPath(e.Node);	// update the user selection text box.
            folder = new DirectoryInfo(e.Node.FullPath);	// get it's Directory info.

        }

        private void treeView1_BeforeExpand(object sender, TreeViewCancelEventArgs e)
        {
            getSubDirs(e.Node);					// get the sub-folders for the selected node.
            textBox1.Text = fixPath(e.Node);	// update the user selection text box.
            folder = new DirectoryInfo(e.Node.FullPath);	// get it's Directory info.
	
        }

        private void button_select_Click(object sender, EventArgs e)
        {
            tw = new StreamWriter("DataInputPath.txt");
            tw.Write(folder.FullName);
            tw.Close();

            this.DialogResult = DialogResult.OK;
            this.Close();
        }

        private void button_cancel_Click(object sender, EventArgs e)
        {
            folder = null;
            this.Close();
        }


        /// <summary> method name
        /// <para>A method to retrieve the short name for the selected folder.</para>
        /// <returns>The folder name for the selected folder.</returns>
        /// </summary>
        public string name
        {
            get { return ((folder != null && folder.Exists)) ? folder.Name : null; }
        }


        /// <summary> method fullPath
        /// <para>Retrieve the full path for the selected folder.</para>
        /// 
        /// <returns>The correctly formatted full path to the selected folder.</returns>
        /// <seealso cref="FolderSelect.fixPath"/>
        /// </summary>
        public string fullPath
        {
            get { return ((folder != null && folder.Exists && treeView1.SelectedNode != null)) ? fixPath(treeView1.SelectedNode) : null; }
        }

        /// <summary> method info
        /// <para>Retrieve the full DirectoryInfo object associated with the selected folder.  Note
        /// that this will not have the corrected full path string.</para>
        /// <returns>The full DirectoryInfo object associated with the selected folder.</returns>
        /// <see cref="System.IO.DirectoryInfo"/>
        /// </summary>
        public DirectoryInfo info
        {
            get { return ((folder != null && folder.Exists)) ? folder : null; }
        }

        

        private void treeView1_NodeMouseDoubleClick(object sender, TreeNodeMouseClickEventArgs e)
        {
            string node_path = e.Node.FullPath;
            fillTree(node_path);
        }

     





    }
}