using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace AudioAnnotation
{
    public partial class PopUp_Result_Window : Form
    {
        
        public PopUp_Result_Window()
        {
            InitializeComponent();
            
            //this.DialogResult = DialogResult.None;

        }


        public void button_continue_Click(object sender, EventArgs e)
        {

            this.Visible = false;
            this.DataGridView_Summary.Rows.Clear();
        }

        public bool fill_grid_summary(string summary_results)
        {
            try
            {
                //textBox_results.Text = summary_results; 
                int nrow = -1;
                this.DataGridView_Summary.Rows.Clear();

                //DataGridViewCellStyle cellstyle_bold = new DataGridVie;
                Font Font1 = new Font(FontFamily.GenericSansSerif, 9.0F, FontStyle.Bold);
                Font Font2 = new Font(FontFamily.GenericSansSerif, 8.5F, FontStyle.Bold);

                string[] str = summary_results.Split(';');

                foreach (string line in str)
                {
                    string[] value = line.Split(',');
                    nrow++;
                    DataGridView_Summary.Rows.Add();

                    if (value.Length >= 1)
                    { DataGridView_Summary.Rows[nrow].Cells[0].Value = value[0]; }


                    if (value.Length >= 2)
                    {
                        DataGridView_Summary.Rows[nrow].Cells[1].Value = value[1];
                    }

                    if (value.Length >= 3)
                    {
                        if (value[2].CompareTo("#") == 0)
                        {
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.Font = Font1;
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.BackColor = Color.DarkSeaGreen;
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.ForeColor = Color.White;


                        }
                        else if (value[2].CompareTo("##") == 0)
                        {
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.Font = Font2;
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.ForeColor = Color.Green;
                        }
                        else if (value[2].CompareTo("###") == 0)
                        {
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.Font = Font2;
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.ForeColor = Color.Tomato;
                        }
                        else if (value[2].CompareTo("#-") == 0)
                        {
                            DataGridView_Summary.Rows[nrow].DefaultCellStyle.Font = Font1;
                        }
                        else if (value[2].CompareTo("*") == 0)
                        { DataGridView_Summary.Rows[nrow].DefaultCellStyle.BackColor = Color.Gainsboro; }
                    }
                }

                return true;
            }//try
            catch
            {
                return false;
            }

        }

       
    }
}