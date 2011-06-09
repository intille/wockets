using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

using Wockets.Data.Types;

namespace KernelApp.GUI
{
    class PhonePanel:Panel
    {
        private int BTE = -1;
        
        private int panel_width;
        private int panel_height;
        private Color panel_bgcolor = Color.Gainsboro;
        public  TransmissionMode MODE = TransmissionMode.Continuous;


        //picture box
        private PictureBox image_id;

        //labels
        private Label label_ebt = new Label();
        private Label label_ebt_value = new Label();


        public PhonePanel(int width, int height, Bitmap picture, TransmissionMode mode)
        {
            MODE = mode;
            
            //Wall parameters
            panel_width = width;
            panel_height = height;

            this.Size = new Size(panel_width, panel_height);
            this.Location = new Point(0, 0);
            this.Visible = true;
            this.BackColor = panel_bgcolor;
            

            //--- Labels ---
            Color label_text_color = Color.DeepSkyBlue;
            Color label_value_color = Color.DimGray;

            Font panel_labels_font = new Font("Tahoma", 9, FontStyle.Regular);
            Font panel_labels_font_bold = new Font("Tahoma", 9, FontStyle.Bold);
            int panel_labels_width = 100;
            int panel_labels_height = 30;
            int upper_gap = 1;
            int ipos_x = 20; //50, 250
            int ipos_value_x = 70; //350
            int ipos_label_x = 250;
            int ipos_y = upper_gap;

            //Phone Expected Battery Life Label
            label_ebt.Text = "";
            label_ebt.Font = panel_labels_font_bold;
            label_ebt.TextAlign = ContentAlignment.TopLeft;
            label_ebt.ForeColor = label_text_color;
            label_ebt.Width = panel_labels_width * 2;
            label_ebt.Height = panel_labels_height;
            label_ebt.Location = new Point(ipos_label_x, ipos_y);
            this.Controls.Add(label_ebt);

            label_ebt_value.Text = "";
            label_ebt_value.Font = panel_labels_font_bold;
            label_ebt_value.TextAlign = ContentAlignment.TopLeft;
            label_ebt_value.ForeColor = label_text_color;
            label_ebt_value.Width = panel_labels_width + 50;
            label_ebt_value.Height = panel_labels_height;
            label_ebt_value.Location = new Point(ipos_value_x, ipos_y);
            this.Controls.Add(label_ebt_value);


            //image
            image_id = new PictureBox();
            image_id.Location = new Point(ipos_x, upper_gap); //20
            image_id.Size = new Size(picture.Width, picture.Height);
            image_id.Image = (Image)new Bitmap((Image)picture);
            image_id.Visible = true;
            this.Controls.Add(image_id);


        }


        //BTE
        public int GetBTE()
        {
            return BTE;
        }

        public void SetBTE(int value, TransmissionMode tm)
        {
            BTE = value;
            MODE = tm;
        }

        public void UpdateBTE()
        {
            #region comment
            //if (BTE > 0)
            //{
            //    DateTime ebt_dt = DateTime.Now;
            //    label_ebt_value.Text = String.Format("{0:hh:mm} h", ebt_dt);
            //}
            //else
            //    label_ebt_value.Text = "";
            #endregion 


            if (BTE > 0)
            {
                label_ebt_value.Text = "";
                int bt_life_secs = 0;

                if (MODE == TransmissionMode.Continuous)
                {
                    bt_life_secs = (int)(BTE * 5); //percent * 5min
                    //TimeSpan ebt_dt = TimeSpan.FromMinutes((double)BTE);
                    TimeSpan ebt_dt = TimeSpan.FromMinutes(bt_life_secs);
                    label_ebt_value.Text = String.Format("{0:hh:mm} h", ebt_dt);
                }
                else if (MODE == TransmissionMode.Bursty60)
                {
                    //double bt_life_secs = 0.0;
                    bt_life_secs = (int)(BTE * 15); //percent * 15min
                    TimeSpan ebt_dt = TimeSpan.FromMinutes(bt_life_secs);
                    label_ebt_value.Text = String.Format("{0:hh:mm} h", ebt_dt);
               }     
            }
            else
            {
                label_ebt_value.Text = "";
            }

        }

        public void ClearBTE()
        {
            label_ebt_value.Text = "";
        }

       

       

        //MODE
        public TransmissionMode GetMode()
        {
            return MODE;
        }

        public void SetMode(TransmissionMode value)
        {
            MODE = value;
        }


        public void UpdateStatusLabel( string value)
        {
            
            label_ebt.Text = value;
        }

        public void ClearStatusLabel()
        {
            label_ebt.Text = "";
        }





    }
}
