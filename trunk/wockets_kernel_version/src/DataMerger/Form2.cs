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
        public int _TotalActigraphs = 6;

        public double _SensewearSeconds = 0;
        public double _ZephyrSeconds = 0;
        //public double _ActigraphSeconds = 0;
        public double _RTISeconds = 0;
        public double _ColumbiaSeconds = 0;
        public double _OxyconSeconds = 0;
        public double[] _ActigraphSeconds = new double[] { 0, 0, 0, 0, 0, 0 };


        public double _MitesSeconds = 0;
        public double _GpsSeconds = 0;
        public double _AnnotationsSeconds = 0;


        private string directory = "";
        private string FILENAME = "TimeOffsetCorrections.txt";




        public Form2(string directory)
        {
            InitializeComponent();
            this.directory = directory + "\\othersensors\\"; ;


            LoadData();
        }




        //private void textBox_actigraph1_TextChanged(object sender, EventArgs e)
        //{
        //    try
        //    {
        //        //TextBox[] _textBox_Actigraphs = { this.textBox_actigraph1, this.textBox_actigraph2, this.textBox_actigraph3, this.textBox_actigraph4, this.textBox_actigraph5, this.textBox_actigraph6 };
        //        //for (int i = 0; i < _TotalActigraphs; i++)
        //        //{
        //        //    this._ActigraphSeconds[i] = Convert.ToDouble(_textBox_Actigraphs[i].Text.Trim());
        //        //}
        //        this._ActigraphSeconds[0] = Convert.ToDouble(this.textBox_actigraph1.Text.Trim());
        //        Save();
        //    }
        //    catch
        //    {
        //        this._ActigraphSeconds[0] = 0;
        //    }
        //}

        private void textBox_actigraph1_TextChanged_1(object sender, EventArgs e)
        {
            try
            {
                //TextBox[] _textBox_Actigraphs = { this.textBox_actigraph1, this.textBox_actigraph2, this.textBox_actigraph3, this.textBox_actigraph4, this.textBox_actigraph5, this.textBox_actigraph6 };
                //for (int i = 0; i < _TotalActigraphs; i++)
                //{
                //    this._ActigraphSeconds[i] = Convert.ToDouble(_textBox_Actigraphs[i].Text.Trim());
                //}
                this._ActigraphSeconds[0] = Convert.ToDouble(this.textBox_actigraph1.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds[0] = 0;
            }
        }

        private void textBox_actigraph2_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ActigraphSeconds[1] = Convert.ToDouble(this.textBox_actigraph2.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds[1] = 0;
            }

        }

        private void textBox_actigraph3_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ActigraphSeconds[2] = Convert.ToDouble(this.textBox_actigraph3.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds[2] = 0;
            }
        }

        private void textBox_actigraph4_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ActigraphSeconds[3] = Convert.ToDouble(this.textBox_actigraph4.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds[3] = 0;
            }
        }

        private void textBox_actigraph5_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ActigraphSeconds[4] = Convert.ToDouble(this.textBox_actigraph5.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds[4] = 0;
            }
        }
        private void textBox_actigraph6_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ActigraphSeconds[5] = Convert.ToDouble(this.textBox_actigraph6.Text.Trim());
                Save();
            }
            catch
            {
                this._ActigraphSeconds[5] = 0;
            }
        }

        private void textBox_sensewear_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._SensewearSeconds = Convert.ToDouble(this.textBox_sensewear.Text.Trim());
                Save();
            }
            catch
            {
                this._SensewearSeconds = 0;
            }
        }

        private void textBox_zephyr_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ZephyrSeconds = Convert.ToDouble(this.textBox_zephyr.Text.Trim());
                Save();
            }
            catch
            {
                this._ZephyrSeconds = 0;
            }
        }

        private void textBox_columbia_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._ColumbiaSeconds = Convert.ToDouble(this.textBox_columbia.Text.Trim());
                Save();
            }
            catch
            {
                this._ColumbiaSeconds = 0;
            }
        }

        private void textBox_rti_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._RTISeconds = Convert.ToDouble(this.textBox_rti.Text.Trim());
                Save();
            }
            catch
            {
                this._RTISeconds = 0;
            }
        }


        private void textBox_oxycon_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._OxyconSeconds = Convert.ToDouble(this.textBox_oxycon.Text.Trim());
                Save();
            }
            catch
            {
                this._OxyconSeconds = 0;
            }
        }


        private void textBox_annotations_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._AnnotationsSeconds = Convert.ToDouble(this.textBox_annotations.Text.Trim());
                Save();
            }
            catch
            {
                this._AnnotationsSeconds = 0;
            }
        }

        private void textBox_mites_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._MitesSeconds = Convert.ToDouble(this.textBox_mites.Text.Trim());
                Save();
            }
            catch
            {
                this._MitesSeconds = 0;
            }
        }

        private void textBox_gps_TextChanged(object sender, EventArgs e)
        {
            try
            {
                this._GpsSeconds = Convert.ToDouble(this.textBox_gps.Text.Trim());
                Save();
            }
            catch
            {
                this._GpsSeconds = 0;
            }
        }




        private void LoadData()
        {
            TextBox[] _textBox_Actigraphs = { this.textBox_actigraph1, this.textBox_actigraph2, this.textBox_actigraph3, this.textBox_actigraph4, this.textBox_actigraph5, this.textBox_actigraph6 };

            if (File.Exists(directory + FILENAME))
            {
                TextReader tr = new StreamReader(directory + FILENAME);
                string line = "";



                try
                {
                    for (int i = 0; i < _TotalActigraphs; i++)
                    {
                        line = tr.ReadLine();
                        this._ActigraphSeconds[i] = Convert.ToDouble(line.Substring(10));
                    }
                    //line = tr.ReadLine();
                    //this._ActigraphSeconds = Convert.ToDouble(line.Substring(10));
                }
                catch
                {
                    this._ActigraphSeconds = new double[] { 0, 0, 0, 0, 0, 0 };
                }


                try
                {
                    line = tr.ReadLine();
                    this._SensewearSeconds = Convert.ToDouble(line.Substring(10));
                }
                catch
                {
                    this._SensewearSeconds = 0;
                }



                try
                {
                    line = tr.ReadLine();
                    this._ZephyrSeconds = Convert.ToDouble(line.Substring(7));
                }
                catch
                {
                    this._ZephyrSeconds = 0;
                }



                try
                {
                    line = tr.ReadLine();
                    this._ColumbiaSeconds = Convert.ToDouble(line.Substring(9));
                }
                catch
                {
                    this._ColumbiaSeconds = 0;
                }


                try
                {
                    line = tr.ReadLine();
                    this._RTISeconds = Convert.ToDouble(line.Substring(4));
                }
                catch
                {
                    this._RTISeconds = 0;
                }


                try
                {
                    line = tr.ReadLine();
                    this._OxyconSeconds = Convert.ToDouble(line.Substring(7));
                }
                catch
                {
                    this._OxyconSeconds = 0;
                }



                try
                {
                    line = tr.ReadLine();
                    this._AnnotationsSeconds = Convert.ToDouble(line.Substring(12));
                }
                catch
                {
                    this._AnnotationsSeconds = 0;
                }



                try
                {
                    line = tr.ReadLine();
                    this._MitesSeconds = Convert.ToDouble(line.Substring(6));
                }
                catch
                {
                    this._MitesSeconds = 0;
                }



                try
                {
                    line = tr.ReadLine();
                    this._GpsSeconds = Convert.ToDouble(line.Substring(4));
                }
                catch
                {
                    this._GpsSeconds = 0;
                }




                tr.Close();
            }


            for (int i = 0; i < _TotalActigraphs; i++)
            {
                _textBox_Actigraphs[i].Text = this._ActigraphSeconds[i].ToString();
            }
            //this.textBox_actigraph1.Text = this._ActigraphSeconds.ToString();
            this.textBox_sensewear.Text = this._SensewearSeconds.ToString();
            this.textBox_zephyr.Text = this._ZephyrSeconds.ToString();
            this.textBox_columbia.Text = this._ColumbiaSeconds.ToString();
            this.textBox_rti.Text = this._RTISeconds.ToString();
            this.textBox_oxycon.Text = this._OxyconSeconds.ToString();


            this.textBox_annotations.Text = this._AnnotationsSeconds.ToString();
            this.textBox_mites.Text = this._MitesSeconds.ToString();
            this.textBox_gps.Text = this._GpsSeconds.ToString();

        }




        private void Save()
        {
            TextWriter tw = new StreamWriter(directory + "TimeOffsetCorrections.txt");
            for (int i = 0; i < _TotalActigraphs; i++)
            {
                tw.WriteLine("Actigraph" + (i + 1) + ":" + this._ActigraphSeconds[i]);
            }
            //tw.WriteLine("Actigraph:" + this._ActigraphSeconds);
            tw.WriteLine("Sensewear:" + this._SensewearSeconds);
            tw.WriteLine("Zephyr:" + this._ZephyrSeconds);
            tw.WriteLine("Columbia:" + this._ColumbiaSeconds);
            tw.WriteLine("RTI:" + this._RTISeconds);
            tw.WriteLine("Oxycon:" + this._OxyconSeconds);


            tw.WriteLine("Annotations:" + this._AnnotationsSeconds);
            tw.WriteLine("Mites:" + this._MitesSeconds);
            tw.WriteLine("Gps:" + this._GpsSeconds);

            tw.Close();


        }










    }
}