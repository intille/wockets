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

using Microsoft.WindowsCE.Forms;
using System.Runtime.InteropServices;
//using System.Diagnostics;




namespace FileUploadTestApp
{

    #region Events
    
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

    #endregion






    public partial class Form1 : Form
    {
        //private const String fileUploadSeverURL = "http://citytesting.scripts.mit.edu/upload/upload.php";
        private const String logFilePath = "\\Wockets\\FUlog.txt";
        
        private internalMessageWindow messageWindow;
        public IntPtr wndPtr;


        public Form1()
        {
            InitializeComponent();

            this.messageWindow = new internalMessageWindow(this);
            this.Text = "WocketsAppWindow";


            #region Commented
            //wndPtr = this.messageWindow.Hwnd;
            //textBox1.Text = string.Format("This process ID: {0} ", Process.GetCurrentProcess().Id) + "\r\n" +
            //                Process.GetCurrentProcess().MainWindowHandle.ToInt64().ToString() + "\r\n" +
            //                " , wndPtr= " + wndPtr.ToString() + "\r\n" ;
            #endregion


            #region commented

            /*
            if (!File.Exists(logFilePath))
            {
                File.Create(logFilePath);
            }
            */

            //FileStream logFile = new FileStream(logFilePath, FileMode.Create, FileAccess.ReadWrite, FileShare.Read);
            //StreamWriter logWriter = new StreamWriter(logFile);

            //// Use "\\" for local file path.
            //// Use "/" for remote file path.

            //FileUploadManager.enableLogger(logWriter);
            ////FileUploadManager.uploadFile(fileUploadSeverURL, @"/uploaddata.csv", "cityproject", "1", "raw_data", "", "This is wockets project file 1");
            ////FileUploadManager.uploadFile(fileUploadSeverURL, @"/WocketsAccelBytes.2010-6-14-10-0-0-0.3.PLFormat", "cityproject", "1", "raw_data", "Subfolder\\subsubfolder", "This is another project file 2");
            
            //String[] excludedDirectories = {"\\wockets_data\\data\\raw\\PLFormat"};

            //// upload the WHOLE DIRECTORY structure recursively BUT THE PLFORMAT directory
            //// documentation in the city project wiki
            //// Parameters: (folder to upload, predefined project name "wockets", subject id, 
            ////             type of data "raw_data", subfolder after the uploaded folder, 
            ////             excluded directories: list of paths that will not be uploaded,
            ////             note that will be written in the database)
            //FileUploadManager.uploadAllFilesInDirectory(fileUploadSeverURL, "\\Wockets\\wockets", "wockets", "1", "raw_data", "wockets", excludedDirectories, "Uploaded in batch");
            //FileUploadManager.uploadAllFilesInDirectory(fileUploadSeverURL, "\\Wockets\\wockets\\data\\raw\\PLFormat\\2010-06-14", "wockets", "1", "raw_data", "wockets\\data\\raw\\PLFormat\\2010-06-14", null, "Uploaded in batch");
            #endregion commented
        }

        private void timer1_Tick(object sender, EventArgs e)
        {
            #region fileuploader
            //FileStream logFile = new FileStream(logFilePath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);        
            //String buffer = "";
           
            //// create reader & open file
            //TextReader tr = new StreamReader(logFile);
            
            //String line = "";
            //while ((line = tr.ReadLine()) != null)
            //{
            //    buffer += line + "\r\n";;
            //}
            //tr.Close();

            //textBox1.Text = buffer;
            //textBox1.SelectionStart = textBox1.Text.Length;
            //textBox1.ScrollToCaret();
            #endregion

        }
    }
}