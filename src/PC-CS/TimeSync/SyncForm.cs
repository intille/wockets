using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace TimeSync_PC
{
    public partial class SyncForm : Form
    {
        private static string TimeServer;

        public SyncForm()
        {
            InitializeComponent();

            SynchronizerName();
        }

        private static void SynchronizerName()
        {
          
            // Modify the server name as desired, 
            // this server is closer to Stanford
            TimeServer = "nist1.datum.com";

            //Name, IP, location
            //time-a.nist.gov 	            //129.6.15.28 	    NIST, Gaithersburg, Maryland
            //time-b.nist.gov 	            //129.6.15.29 	    NIST, Gaithersburg, Maryland
            //time-a.timefreq.bldrdoc.gov 	//132.163.4.101 	NIST, Boulder, Colorado
            //time-b.timefreq.bldrdoc.gov 	//132.163.4.102 	NIST, Boulder, Colorado
            //time-c.timefreq.bldrdoc.gov 	//132.163.4.103 	NIST, Boulder, Colorado
            //utcnist.colorado.edu 	        //128.138.140.44 	University of Colorado, Boulder
            //time.nist.gov 	            //192.43.244.18 	NCAR, Boulder, Colorado
            //time-nw.nist.gov 	            //131.107.1.10 	    Microsoft, Redmond, Washington
            //nist1.datum.com 	            //66.243.43.21     Datum, San Jose, California
            //nist1.dc.certifiedtime.com 	//216.200.93.8 	    Abovnet, Virginia
            //nist1.nyc.certifiedtime.com 	//208.184.49.9 	    Abovnet, New York City
            //nist1-ny.ustiming.org         //64.90.182.55      New York City
            //nist1.sjc.certifiedtime.com 	//208.185.146.41 	Abovnet, San Jose, California

        }


        #region commented implementation 1
        
        public int Synchronize()
        {


            SNTPClient client;

            try
            {
                client = new SNTPClient(TimeServer);
                client.Connect(true);
            }
            catch (Exception e)
            {

                textBox1.Text = "Error:  " + "The time server has not responded.\r\n" +
                                             "The operation timed out.\r\n" + "\r\n" +
                                             e.Message;
                return -1;
            }


            textBox1.Text = client.ToString();

            return 0;

        }
      

        #endregion

        #region implementation 2
        /*
        public int Synchronize()
        {

            int isconnected = -1;
            SNTPClient client;

            try
            {
                client = new SNTPClient(TimeServer);


                isconnected = client.Connect(6000, true);

                if (isconnected == 0)
                {
                    // The server can be called maximum every 5 seconds
                    System.Threading.Thread.Sleep(5000);
                    isconnected = client.Connect(6000, true);
                }

                textBox1.Text = client.ToString();


            }
            catch (Exception e)
            {

                textBox1.Text = textBox1.Text + "\r\n"
                                + "Error:  " + "The time server has not responded.\r\n"
                                + "The operation timed out.\r\n" + "\r\n"
                                + e.Message;
                return -1;
            }



            return isconnected;

        }
         
         */ 
        #endregion



        private void button1_Click(object sender, EventArgs e)
        {
            button1.Enabled = false;



            textBox1.Text = "Connecting to: " + TimeServer + "\r\n";
            Application.DoEvents();

            Synchronize();

            button1.Enabled = true;

        }

        private void SyncForm_FormClosing(object sender, FormClosingEventArgs e)
        {
            Application.Exit();
        }

        private void button2_Click(object sender, EventArgs e)
        {
            this.Close();
        }










    }
}