using System;
using System.ComponentModel;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text;
using System.Windows.Forms;
namespace CollectData
{
    public partial class ProgressBar : Panel
    {
        Panel panel2;
        double unit = 0;
        Label label1;
        public ProgressBar()
        {
            InitializeComponent();
            this.panel2 = new System.Windows.Forms.Panel();            
            this.panel2.Location = new System.Drawing.Point(2, 2);
            this.label1 = new Label();
            this.label1.Font = new System.Drawing.Font("Tahoma", 10F, System.Drawing.FontStyle.Regular);
            this.label1.Name = "label7";
            this.label1.Visible = false;
            this.panel2.Controls.Add(this.label1);
          
            this.Controls.Add(this.panel2);                       
        }

        protected override void OnResize(EventArgs e)
        {
            this.unit = (this.Width - 4) / 100.0;
        }
        public int _Value
        {
            get
            {
                return (int)(this.panel2.Width / unit);
            }
            set
            {
                this.panel2.Width = (int)(value * this.unit);
                this.panel2.Height = this.Height - 4;
                this.label1.Size = new System.Drawing.Size(90, this.Height - 4);
                if (this.panel2.Width > 90)
                {
                    this.label1.Location = new System.Drawing.Point((this.panel2.Width / 2) - 45, 0);
                    this.label1.Text = value + "%";
                    this.label1.Visible = true;
                }
                else
                    this.label1.Visible = false;
            }
        }

        public System.Drawing.Color _ForeColor
        {
            get
            {
                return this.panel2.BackColor;
            }

            set
            {
                this.panel2.BackColor = value;
            }
        }


        public System.Drawing.Color _BackColor
        {
            get
            {
                return this.BackColor;
            }

            set
            {
                this.BackColor = value;
            }
        }
    }
}
