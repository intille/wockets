using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;
using Wockets.Utils;
using System.Threading;

namespace TestApplication
{
    public partial class Form1 : Form
    {
        Thread tt;

        private void timer()
        {

            TextWriter tw = new StreamWriter("test.csv");
            double delta = 0;
            double[] times = new double[1000];
            WocketsTimer.InitializeTime();
            for (int i = 0; (i < 1000); i++)
            {
                times[i] = WocketsTimer.GetUnixTime();
                Thread.Sleep(10);

            }

            for (int i = 1; (i < 1000); i++)
            {
                delta = times[i] - times[i-1];
                tw.WriteLine(times[i].ToString("0.00") + "," + delta.ToString("0.00"));

            }
            tw.Close();
            Application.Exit();

        }
        public Form1()
        {
            InitializeComponent();
            Thread.Sleep(10000);
            tt = new Thread(new ThreadStart(timer));
           tt.Priority = ThreadPriority.Highest;
            tt.Start();
            
        }
    }
}