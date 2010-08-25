using System;

using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using System.Threading;

//using Microsoft.WindowsCE.Forms;
using System.Runtime.InteropServices;

using Wockets.Utils.HttpUploader;



namespace FileUploadTestApp
{

    #region Internal message window (commented)
    
    /*
    public class internalMessageWindow : MessageWindow
    {
        private const int TERMINATE_MESSAGE = 0xA123;
        private const int MIN_WND_MESSAGE = 0xC00D;

        Form1 referedForm;
        

        public internalMessageWindow(Form1 referedForm)
        {
            this.referedForm = referedForm;
            this.Text = "WocketsMessageWindow";
        }


        protected override void WndProc(ref Message m)
        {
          
            //filter the Terminate Message
            if (m.Msg == TERMINATE_MESSAGE)
            {
                //display that we recieved the message, of course we could do
                //something else more important here.
                referedForm.textBox1.Text = referedForm.textBox1.Text + "\r\n" +
                                            "Terminate Message Received.";
                 referedForm.Refresh();
            }

            //be sure to pass along all messages to the base also
            base.WndProc(ref m);
        }

    }
    */
    #endregion




    public partial class Form1 : Form
    {
        private const String fileUploadSeverURL = "http://wockets.scripts.mit.edu/FileUpload.php";
        private String root_directory = "\\wockets_test";
        private const String logFilePath = "\\Wockets\\FUlog.txt";

        private FileUploader uploadManager;

        private int resendCounter = 0;
        private int resendThreshold = 480; // 40 minutes
        //private int resendThreshold = 5; // 25 seconds

       

        #region Internal Message window (commented)
        //private internalMessageWindow messageWindow;
        //public IntPtr wndPtr;
        #endregion 


        public Form1()
        {
            InitializeComponent();

            #region Internal Message window (commented)
            //this.messageWindow = new internalMessageWindow(this);
            //this.Text = "WocketsAppWindow";


            // Debug info commented
            //wndPtr = this.messageWindow.Hwnd;
            //textBox1.Text = string.Format("This process ID: {0} ", Process.GetCurrentProcess().Id) + "\r\n" +
            //                Process.GetCurrentProcess().MainWindowHandle.ToInt64().ToString() + "\r\n" +
            //                " , wndPtr= " + wndPtr.ToString() + "\r\n" ;
            #endregion


          
            //--- Create Log file ---
            // Note:
            // Use "\\" for local file path.
            // Use "/" for remote file path.
            FileStream logFile = new FileStream(logFilePath, FileMode.Create, FileAccess.ReadWrite, FileShare.Read);
            StreamWriter logWriter = new StreamWriter(logFile);


            //--- Enable Logger -----
            FileUploader.enableLogger(logWriter);
            

            //--- Indicate the root folder to scan for changes ----
            FileUploader.scanLogFilesAndDelete(root_directory, null);


            //upload the DIRECTORY structure recursively (Notes & Examples)
            #region Examples
            // Parameters: (folder to upload, predefined project name "wockets", subject id, 
            //             type of data "raw_data", subfolder after the uploaded folder, 
            //             excluded directories: list of paths that will not be uploaded,
            //             note that will be written in the database)
            //Examples:
            //FileUploadManager.uploadAllFilesInDirectory(fileUploadSeverURL, "rootDirectory", "applicationName", "subjecId", "DataType", "subdirectoryPath", excludedDirectories, "Uploaded in batch");
            //FileUploadManager.uploadAllFilesInDirectory(fileUploadSeverURL, "\\Wockets\\wockets\\data\\raw\\PLFormat\\2010-06-14", "wockets", "1", "raw_data", "wockets\\data\\raw\\PLFormat\\2010-06-14", null, "Uploaded in batch");
            #endregion 

            // upload the WHOLE DIRECTORY structure recursively 
            FileUploader.uploadAllFilesInDirectory(fileUploadSeverURL, root_directory, "FileUploadTestApp", "1", "raw_data", "", null, "Uploaded in batch");
            

        }


        private void Form1_Load(object sender, EventArgs e)
        {
            uploadManager = new FileUploader(fileUploadSeverURL);
        }




        //private void timer1_Tick(object sender, EventArgs e)
        //{
        //    WriteToScreen();

        //    //ReSendData();

        //}





        private void WriteToScreen()
        {

            //---- Read the logfile  ----
            FileStream logFile = new FileStream(logFilePath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
            String buffer = "";

            // create reader & open file
            TextReader tr = new StreamReader(logFile);
            String line = "";

            //load the contents to the logfile to buffer
            while ((line = tr.ReadLine()) != null)
            {
                buffer += line + "\r\n"; ;
            }

            buffer += "-----\r\n"; ;

            tr.Close();

            this.textBox1.Text = buffer;


        }

        private void ReSendData()
        {

            //----- Wait until the counter reaches the threshold to send files again ----
            if (resendCounter >= resendThreshold)
            {
                //---  Perform a delete and resend operation ---
                FileUploader.scanLogFilesAndDelete(root_directory, null);

                // upload the WHOLE DIRECTORY structure recursively 
                FileUploader.uploadAllFilesInDirectory(fileUploadSeverURL, root_directory, "wockets", "3", "raw_data", "", null, "Uploaded in batch");

                resendCounter = 0;
            }
            else
            {
                resendCounter++;
            }


        }


        //Close Form
        private void menuItem2_Click(object sender, EventArgs e)
        {
            this.Close();

        }



    }
}