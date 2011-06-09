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
    
    class WocketsWall:Panel
    {

        #region Variable Declaration

        //Wall Parameters
        private int ID;
        private String MAC;
        //private String MODE = "";

        private int BTP = -1;
        private int BTE = 0;
        private int PC = 0;
        private int SR = 0;

        private Sensitivity SEN = Sensitivity._4G;
        private TransmissionMode TM = TransmissionMode.Continuous;
        private int AC = 0;


        //View
        private int panel_width;
        private int panel_height;
        private Color panel_bgcolor = Color.White;

        //Labels
        private Label label_mac = new Label();
        private Label label_mac_value = new Label();

        private Label label_sr = new Label();
        private Label label_sr_value = new Label();

        private Label label_loss = new Label();
        private Label label_loss_value = new Label();
       
        private Label label_pbt = new Label();
        private Label label_pbt_value = new Label();
       
        private Label label_ebt = new Label();
        private Label label_ebt_value = new Label();

     
        //picture box
        private PictureBox image_id;

        #endregion 


        #region Initialization
        
        public WocketsWall(int id, String mac, int width, int height,Bitmap picture ,TransmissionMode mode)
        {
            //Wockets Parameteres
            ID = id;
            MAC = mac;
            //MODE = mode;
            

            //Wall parameters
            panel_width = width;
            panel_height = height;

            this.Size = new Size(panel_width, panel_height);
            this.Location = new Point(0,0);
            this.Visible = true;
            this.BackColor = panel_bgcolor;
           
            
            //--- Labels ---
            Color label_text_color = Color.DimGray;
            Color label_value_color = Color.DimGray;

            Font panel_labels_font = new Font("Tahoma", 10, FontStyle.Regular);
            int panel_labels_width = 100;
            int panel_labels_height = 30;
            int upper_gap = 10;
            int ipos_value_x = 350;
            int ipos_x = 250;



            int ipos_y = upper_gap;
            //mac address
            label_mac.Text = "ID:";
            label_mac.Font = panel_labels_font;
            label_mac.TextAlign = ContentAlignment.TopLeft;
            label_mac.ForeColor = label_text_color;
            label_mac.Width = panel_labels_width;
            label_mac.Height = panel_labels_height;
            label_mac.Location = new Point(ipos_x, ipos_y);
            this.Controls.Add(label_mac);

            label_mac_value.Text = mac;
            label_mac_value.Font = panel_labels_font;
            label_mac_value.TextAlign = ContentAlignment.TopLeft;
            label_mac_value.ForeColor = label_value_color;
            label_mac_value.Width = panel_labels_width;
            label_mac_value.Height = panel_labels_height;
            label_mac_value.Location = new Point(ipos_value_x, ipos_y);
            this.Controls.Add(label_mac_value);

            ipos_y = ipos_y + panel_labels_height;
            //Sampling Rate Label
            label_sr.Text = "SR:";
            label_sr.Font = panel_labels_font;
            label_sr.TextAlign = ContentAlignment.TopLeft;
            label_sr.ForeColor = label_text_color;
            label_sr.Width = panel_labels_width;
            label_sr.Height = panel_labels_height;
            label_sr.Location = new Point(ipos_x, ipos_y);
            this.Controls.Add(label_sr);

            label_sr_value.Text = "";
            label_sr_value.Font = panel_labels_font;
            label_sr_value.TextAlign = ContentAlignment.TopLeft;
            label_sr_value.ForeColor = label_value_color;
            label_sr_value.Width = panel_labels_width;
            label_sr_value.Height = panel_labels_height;
            label_sr_value.Location = new Point(ipos_value_x, ipos_y);
            this.Controls.Add(label_sr_value);

            ipos_y = ipos_y + panel_labels_height;
            //Package loss label
            label_loss.Text = "PC:";
            label_loss.Font = panel_labels_font;
            label_loss.TextAlign = ContentAlignment.TopLeft;
            label_loss.ForeColor = label_text_color;
            label_loss.Width = panel_labels_width;
            label_loss.Height = panel_labels_height;
            label_loss.Location = new Point(ipos_x, ipos_y);
            this.Controls.Add(label_loss);


            label_loss_value.Text = "";
            label_loss_value.Font = panel_labels_font;
            label_loss_value.TextAlign = ContentAlignment.TopLeft;
            label_loss_value.ForeColor = label_value_color;
            label_loss_value.Width = panel_labels_width;
            label_loss_value.Height = panel_labels_height;
            label_loss_value.Location = new Point(ipos_value_x, ipos_y);
            this.Controls.Add(label_loss_value);


            //Battery Percent
            ipos_y = ipos_y + panel_labels_height;

            label_pbt.Text = "BT:";
            label_pbt.Font = panel_labels_font;
            label_pbt.TextAlign = ContentAlignment.TopLeft;
            label_pbt.ForeColor = label_text_color;
            label_pbt.Width = panel_labels_width;
            label_pbt.Height = panel_labels_height;
            label_pbt.Location = new Point(ipos_x, ipos_y);
            this.Controls.Add(label_pbt);

            label_pbt_value.Text = "";
            label_pbt_value.Font = panel_labels_font;
            label_pbt_value.TextAlign = ContentAlignment.TopLeft;
            label_pbt_value.ForeColor = label_value_color;
            label_pbt_value.Width = panel_labels_width;
            label_pbt_value.Height = panel_labels_height;
            label_pbt_value.Location = new Point(ipos_value_x, ipos_y);
            this.Controls.Add(label_pbt_value);

            //Expected Battery Time Label
            ipos_y = ipos_y + panel_labels_height;

            label_ebt.Text = "SEN:";
            label_ebt.Font = panel_labels_font;
            label_ebt.TextAlign = ContentAlignment.TopLeft;
            label_ebt.ForeColor = label_text_color;
            label_ebt.Width = panel_labels_width;
            label_ebt.Height = panel_labels_height;
            label_ebt.Location = new Point(ipos_x, ipos_y);
            this.Controls.Add(label_ebt);

            label_ebt_value.Text = "";
            label_ebt_value.Font = panel_labels_font;
            label_ebt_value.TextAlign = ContentAlignment.TopLeft;
            label_ebt_value.ForeColor = label_value_color;
            label_ebt_value.Width = panel_labels_width + 30;
            label_ebt_value.Height = panel_labels_height;
            label_ebt_value.Location = new Point(ipos_value_x, ipos_y);
            this.Controls.Add(label_ebt_value);


            //image
            ipos_y = ipos_y + panel_labels_height;
            image_id = new PictureBox();
            image_id.Location = new Point(20, upper_gap);
            image_id.Size = new Size(150, 150);
            image_id.Image = (Image)new Bitmap((Image) picture);
            image_id.Visible = true;
            this.Controls.Add(image_id);

        }

        #endregion 


        #region Get/Set Wocket Wall Parameters
        //ID
        public int GetID()
        {
            return ID;
        }

        public void SetID(int value)
        {
            if (value > 0)
                ID = value;
            else
                ID = -1;
           
        }

        //MAC
        public String GetMac()
        {
          return MAC;
        }

        public void SetMac(string value)
        {
            MAC = value;
            if (value.Length > 7)
                label_mac_value.Text = value.Substring(7);
            else
                label_mac_value.Text = "";

        }

        //MODE
        public TransmissionMode GetMode()
        {
            return TM;
        }

        public void SetMode(TransmissionMode value)
        {
            TM = value;
        }

        //AC
        public int GetAC()
        {
            return AC;
        }

        public void SetAC(int value)
        {
            AC = value;
        }


        //BTP
        public int GetBTP()
        {
            return BTP;
        }

        public void SetBTP(int value)
        {
            BTP = value;
        }

        public void UpdateBTP()
        {
            if (BTP > 0)
            {
                if (BTP > 640)
                { label_pbt_value.Text = "High";
                  label_pbt_value.ForeColor = Color.Green;
                }
                else if(BTP > 570)
                {
                    label_pbt_value.Text = "Medium";
                    label_pbt_value.ForeColor = Color.Gold;
                }
                else
                {
                    label_pbt_value.Text = "Low";
                    label_pbt_value.ForeColor = Color.Red;
                }

            }
            else
                label_pbt_value.Text = "";
        }

        public void ClearBTP()
        {
            label_pbt_value.Text = "";
        }

        //BTE
        public int GetBTE()
        {
            return BTE;
        }

        public void SetBTE(int value)
        {
             BTE = value; 
           
        }

        public void UpdateBTE()
        {
            if (BTP > 0)
            {
                DateTime ebt_dt = DateTime.Now;
                label_ebt_value.Text = String.Format("{0:hh:mm} h",ebt_dt); 
            }
            else
                label_ebt_value.Text = "";
        }

        public void ClearBTE()
        {
            label_ebt_value.Text = "";
        }


        //SEN
        public Sensitivity GetSEN()
        {
            return SEN;
        }

        public void SetSEN(Sensitivity mysen)
        {
            SEN = mysen;
        }

        public void UpdateSEN()
        {

            label_ebt_value.Text = SEN.ToString();
      
        }

        public void ClearSEN()
        {
            label_ebt_value.Text = "";
        }


        //PC
        public int GetPC()
        {
            return PC;
        }

        public void SetPC(int value)
        {
            PC = value;
         }

        public void UpdatePC()
        {
           // if (PC > 0)
           // {  //label_loss_value.Text = String.Format("{0:0000}", PC); 
                label_loss_value.Text = PC.ToString(); 
           // }
           // else
           //     label_loss_value.Text = "";
        }

        public void ClearPC()
        {
            label_loss_value.Text = "";
        }

        //SR
        public int GetSR()
        {
            return SR;
        }

        public void SetSR(int value)
        {
            if (value > 0)
                SR = value;
            else
                SR = 0;

        }

        public void UpdateSR()
        {
            if (SR > 0)
                label_sr_value.Text = SR.ToString();
            else
                label_sr_value.Text = "";
        }

        public void ClearSR()
        {
            label_sr_value.Text = "";
        }



        #endregion 



    }
}
