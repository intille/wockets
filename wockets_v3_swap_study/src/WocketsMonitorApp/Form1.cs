using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Utils.feedback;
using System.Diagnostics;
using System.IO;
using System.Runtime.InteropServices;
using Wockets.Utils.IPC;
using Wockets.Utils.IPC.Queues;
using System.Threading;
namespace WocketsMonitorApp
{
    public partial class Form1 : Form
    {

        Sound disconnectedAlert = null;            
        string path="";
        public static string KERNEL_PATH = @"\Program Files\wockets\";
        public static string KERNEL_EXECUTABLE = "DataCollectionApp.exe";
        int raw1 = 0;
        int raw2 = 0;
        int sum1 = 0;
        int sum2 = 0;
        int partial1 = 0;
        int partial2 = 0;
        double receivedPackets1 = 0;
        double receivedPackets2 = 0;
        double expectedPackets1 = 0;
        double expectedPackets2 = 0;
        double loss1 = 0;
        double loss2 = 0;
        P2PMessageQueue mQue = null;
        int ExpectedPackets1 = 0;
        int ExpectedPackets2 = 0;
        bool playAlert = false;
        public Form1()
        {
            InitializeComponent();
            path= System.IO.Path.GetDirectoryName(
               System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase) + "\\NeededFiles\\";
            disconnectedAlert=new Sound(path+ "sounds\\Disconnected.wav");
      
            mQue = new P2PMessageQueue(true, "WocketStatistics");
            mQue.DataOnQueueChanged += new EventHandler(mQue_DataOnQueueChanged);
        }


        private bool disposed = false;

        delegate void UpdateFormCallback();
        public void UpdateForm()
        {

            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired)
                {
                    UpdateFormCallback d = new UpdateFormCallback(UpdateForm);
                    this.Invoke(d, new object[] { });
                }
                else
                {
                    this.label5.Text = "Fully Received: "+raw1+" packets";
                    this.label6.Text = "Partially Received: "+partial1+" packets";
                    this.label7.Text = "Summary: "+sum1+" packets";
                    this.label2.Text = "Loss Rate: " + loss1.ToString("0.0") + " %";


                    this.label4.Text = "Fully Received: " + raw2 + " packets";
                    this.label8.Text = "Partially Received: " + partial2 + " packets";
                    this.label9.Text = "Summary: " + sum2 + " packets";
                    this.label10.Text = "Loss Rate: " + loss2.ToString("0.0") +" %";
                }
            }
        }

        void mQue_DataOnQueueChanged(object sender, EventArgs e)
        {
           Message msg;

			msg = new Message();
			//msg = new CustomMessage();// Either this or the previous line. This demoes CustomMessages

			// mTimeout is set by the end user via the GUI 
			// to DON’T BLOCK (0), BLOCK (-1), or a real timeout value
			ReadWriteResult rwr = mQue.Receive(msg, 1000);
            if (rwr == ReadWriteResult.OK)
            {
                bool isAlrt;
                string payload;
                isAlrt = msg.IsAlert;

                byte[] bytes = msg.MessageBytes;
                payload = System.Text.Encoding.ASCII.GetString(bytes, 0, bytes.GetLength(0));

                string[] tokens = payload.Split(new char[1] { ',' });
                int myraw1 = 0;
                int myraw2 = 0;
                myraw1 = Convert.ToInt32(tokens[6]);
                ExpectedPackets1 = Convert.ToInt32(tokens[7]);
                if (tokens.Length > 11)
                {
                    myraw2 = Convert.ToInt32(tokens[11]);
                    ExpectedPackets2 = Convert.ToInt32(tokens[12]);
                }

                if ((ExpectedPackets1!=0) && (myraw1 == ExpectedPackets1))
                    raw1++;
                else if (myraw1 > 0)
                    partial1++;
                else
                    sum1++;

                receivedPackets1 += myraw1;
                expectedPackets1 += ExpectedPackets1;
                loss1=(1.0-((double)receivedPackets1/expectedPackets1))*100.0;

                if (tokens.Length > 11)
                {
                    if ((ExpectedPackets2!=0) && (myraw2 == ExpectedPackets2))
                        raw2++;
                    else if (myraw2 > 0)
                        partial2++;
                    else
                        sum2++;

                    receivedPackets2 += myraw2;
                    expectedPackets2 += ExpectedPackets2;
                    loss2 = (1.0 - ((double)receivedPackets2 / expectedPackets2)) * 100.0;
                }
                UpdateForm();
            }
        }
        
        private void button1_Click(object sender, EventArgs e)
        {          
            System.Diagnostics.Process po = new System.Diagnostics.Process();
            ProcessStartInfo startInfo = new ProcessStartInfo();
            //startInfo.
            startInfo.WorkingDirectory = KERNEL_PATH;
            startInfo.FileName = KERNEL_PATH + "\\" + KERNEL_EXECUTABLE;
            startInfo.UseShellExecute = false;         
            po.StartInfo = startInfo;           
            po.Start();
            this.button1.Enabled = false;

        } 

        private void menuItem1_Click(object sender, EventArgs e)
        {
            if (Microsoft.VisualBasic.Interaction.MsgBox("Are you sure you want to exit?", Microsoft.VisualBasic.MsgBoxStyle.YesNo, "Shutdown") == Microsoft.VisualBasic.MsgBoxResult.Yes)
            {
                mQue.Close();
                NamedEvents namedEvent = new NamedEvents();
                namedEvent.Send("TerminateWockets");
                Application.Exit();
                System.Diagnostics.Process.GetCurrentProcess().Kill();
            }
        }
        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
        const int SW_MINIMIZED = 6;
        private void menuItem2_Click(object sender, EventArgs e)
        {
            ShowWindow(this.Handle, SW_MINIMIZED);
        }
    }
}