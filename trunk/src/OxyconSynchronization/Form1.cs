using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.IO;
using System.Windows.Forms;

namespace OxyconSynchronization
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
            Form2 f = new Form2();
            f.Show();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            DateTime now = DateTime.Now;
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
            TimeSpan diff = now.Subtract(origin);
            string timestamp = diff.TotalMilliseconds + "," + now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            string filename = Environment.GetFolderPath(Environment.SpecialFolder.Desktop) + "\\OxyconSyncronizationTime.txt";
            TextWriter tw = new StreamWriter(filename);
            tw.WriteLine(timestamp);
            tw.Close();
            this.button1.Enabled = false;
        }
    }
}