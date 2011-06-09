using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Diagnostics;

namespace WocketsProgrammer
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
            this.comboBox1.SelectedIndex = 3;
        }

        private void button1_Click(object sender, EventArgs e)
        {
            Process batch = new Process();

            batch.StartInfo.FileName = "programmer\\ProgramWocket.bat";
            batch.StartInfo.Arguments = "Firmware-" + ((string)this.comboBox1.Items[this.comboBox1.SelectedIndex]).Replace(" ", "-") + ".hex " +"programmer\\";
            batch.Start();
        }
    }
}
