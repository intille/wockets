using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace OxyconSynchronization
{
    public partial class Form2 : Form
    {
        public Form2()
        {
            InitializeComponent();
        }

        private void button1_Click(object sender, EventArgs e)
        {
            DateTime now = DateTime.Now;
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
            TimeSpan diff = now.Subtract(origin);
            string timestamp = diff.TotalMilliseconds + "," + now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            TextWriter tw = new StreamWriter(Environment.GetFolderPath(Environment.SpecialFolder.Desktop) + "\\RTISynchronizationTime.txt");
            tw.WriteLine(timestamp);
            tw.Close();
            this.button1.Enabled = false;
        }
    }
}