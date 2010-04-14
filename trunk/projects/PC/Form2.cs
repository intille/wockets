using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace DataMerger
{
    public partial class Form2 : Form
    {
        public double _SensewearSeconds = 0;
        public double _ZephyrSeconds = 0;
        public double _ActigraphSeconds = 0;
        public double _RTISeconds = 0;
        public double _ColumbiaSeconds = 0;
        private string directory = "";
        private string FILENAME = "TimeOffsetCorrections.txt";

        public Form2(string directory)
        {
            InitializeComponent();
            this.directory = directory;

           
           LoadData();
        }

        private void Form2_Load(object sender, EventArgs e)
        {

        }

        private void textBox1_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ActigraphSeconds = Convert.ToDouble(this.textBox1.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds = 0;
            }
        }

        private void textBox2_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._SensewearSeconds = Convert.ToDouble(this.textBox2.Text.Trim());
                Save();
            }
            catch
            {
                this._SensewearSeconds = 0;
            }
        }

        private void textBox3_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ZephyrSeconds = Convert.ToDouble(this.textBox3.Text.Trim());
                Save();
            }
            catch
            {
                this._ZephyrSeconds = 0;
            }
        }

        private void textBox4_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ColumbiaSeconds = Convert.ToDouble(this.textBox4.Text.Trim());
                Save();
            }
            catch
            {
                this._ColumbiaSeconds = 0;
            }
        }

        private void textBox5_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._RTISeconds = Convert.ToDouble(this.textBox5.Text.Trim());
                Save();
            }
            catch
            {
                this._RTISeconds = 0;
            }
        }

        private void LoadData()
        {
            if (File.Exists(directory + FILENAME))
            {
                TextReader tr = new StreamReader(directory + FILENAME);
                string line = tr.ReadLine();
                this._ActigraphSeconds = Convert.ToDouble(line.Substring(10));
                line = tr.ReadLine();
                this._SensewearSeconds = Convert.ToDouble(line.Substring(10));
                line = tr.ReadLine();
                this._ZephyrSeconds = Convert.ToDouble(line.Substring(7));
                line = tr.ReadLine();
                this._ColumbiaSeconds = Convert.ToDouble(line.Substring(9));
                line = tr.ReadLine();
                this._RTISeconds = Convert.ToDouble(line.Substring(4));
                tr.Close();
            }
            this.textBox1.Text = this._ActigraphSeconds.ToString();
            this.textBox2.Text = this._SensewearSeconds.ToString();
            this.textBox3.Text = this._ZephyrSeconds.ToString();
            this.textBox4.Text = this._ColumbiaSeconds.ToString();
            this.textBox5.Text = this._RTISeconds.ToString();

        }
        private void Save()
        {
            TextWriter tw = new StreamWriter(directory + "TimeOffsetCorrections.txt");
            tw.WriteLine("Actigraph:" + this._ActigraphSeconds);
            tw.WriteLine("Sensewear:" + this._SensewearSeconds);
            tw.WriteLine("Zephyr:" + this._ZephyrSeconds);
            tw.WriteLine("Columbia:" + this._ColumbiaSeconds);
            tw.WriteLine("RTI:" + this._RTISeconds);
            tw.Close();
        }
    }
}