using System;

using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using FileUploadLib;
using System.Threading;

namespace FileUploadTestApp
{
    public partial class Form1 : Form
    {
        private const String fileUploadSeverURL = "http://citytesting.scripts.mit.edu/upload/upload.php";

        private const String logFilePath = "\\Wockets\\FUlog.txt";
      
        

        public Form1()
        {
            InitializeComponent();

            /*
            if (!File.Exists(logFilePath))
            {
                File.Create(logFilePath);
            }
            */

            FileStream logFile = new FileStream(logFilePath, FileMode.Create, FileAccess.ReadWrite, FileShare.Read);
            StreamWriter logWriter = new StreamWriter(logFile);

            // Use "\\" for local file path.
            // Use "/" for remote file path.

            FileUploadManager.enableLogger(logWriter);
            //FileUploadManager.uploadFile(fileUploadSeverURL, @"/uploaddata.csv", "cityproject", "1", "raw_data", "", "This is wockets project file 1");
            //FileUploadManager.uploadFile(fileUploadSeverURL, @"/WocketsAccelBytes.2010-6-14-10-0-0-0.3.PLFormat", "cityproject", "1", "raw_data", "Subfolder\\subsubfolder", "This is another project file 2");
            
            String[] excludedDirectories = {"\\wockets_data\\data\\raw\\PLFormat"};

            // upload the WHOLE DIRECTORY structure recursively BUT THE PLFORMAT directory
            // documentation in the city project wiki
            // Parameters: (folder to upload, predefined project name "wockets", subject id, 
            //             type of data "raw_data", subfolder after the uploaded folder, 
            //             excluded directories: list of paths that will not be uploaded,
            //             note that will be written in the database)
            FileUploadManager.uploadAllFilesInDirectory(fileUploadSeverURL, "\\Wockets\\wockets", "wockets", "1", "raw_data", "wockets", excludedDirectories, "Uploaded in batch");
            FileUploadManager.uploadAllFilesInDirectory(fileUploadSeverURL, "\\Wockets\\wockets\\data\\raw\\PLFormat\\2010-06-14", "wockets", "1", "raw_data", "wockets\\data\\raw\\PLFormat\\2010-06-14", null, "Uploaded in batch");
        }

        private void timer1_Tick(object sender, EventArgs e)
        {
            FileStream logFile = new FileStream(logFilePath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);        
            String buffer = "";
            // create reader & open file
            TextReader tr = new StreamReader(logFile);
            
            String line = "";
            while ((line = tr.ReadLine()) != null)
            {
                buffer += line + "\r\n";;
            }
            tr.Close();

            textBox1.Text = buffer;
            textBox1.SelectionStart = textBox1.Text.Length;
            textBox1.ScrollToCaret();
        }
    }
}