namespace KernelTest
{
    partial class Form2
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;
        private System.Windows.Forms.MainMenu mainMenu1;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.menuItem1 = new System.Windows.Forms.MenuItem();
            this.menuItem3 = new System.Windows.Forms.MenuItem();
            this.menuItem4 = new System.Windows.Forms.MenuItem();
            this.menuItem5 = new System.Windows.Forms.MenuItem();
            this.menuItem6 = new System.Windows.Forms.MenuItem();
            this.menuItem14 = new System.Windows.Forms.MenuItem();
            this.menuItem15 = new System.Windows.Forms.MenuItem();
            this.menuItem16 = new System.Windows.Forms.MenuItem();
            this.menuItem17 = new System.Windows.Forms.MenuItem();
            this.menuItem18 = new System.Windows.Forms.MenuItem();
            this.menuItem19 = new System.Windows.Forms.MenuItem();
            this.menuItem7 = new System.Windows.Forms.MenuItem();
            this.menuItem8 = new System.Windows.Forms.MenuItem();
            this.menuItem20 = new System.Windows.Forms.MenuItem();
            this.menuItem9 = new System.Windows.Forms.MenuItem();
            this.menuItem10 = new System.Windows.Forms.MenuItem();
            this.menuItem11 = new System.Windows.Forms.MenuItem();
            this.menuItem12 = new System.Windows.Forms.MenuItem();
            this.menuItem13 = new System.Windows.Forms.MenuItem();
            this.menuItem21 = new System.Windows.Forms.MenuItem();
            this.menuItem24 = new System.Windows.Forms.MenuItem();
            this.menuItem22 = new System.Windows.Forms.MenuItem();
            this.menuItem23 = new System.Windows.Forms.MenuItem();
            this.menuItem25 = new System.Windows.Forms.MenuItem();
            this.menuItem26 = new System.Windows.Forms.MenuItem();
            this.menuItem27 = new System.Windows.Forms.MenuItem();
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.panel1 = new System.Windows.Forms.Panel();
            this.label1 = new System.Windows.Forms.Label();
            this.timer1 = new System.Windows.Forms.Timer();
            this.label2 = new System.Windows.Forms.Label();
            this.label3 = new System.Windows.Forms.Label();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            this.mainMenu1.MenuItems.Add(this.menuItem2);
            // 
            // menuItem1
            // 
            this.menuItem1.MenuItems.Add(this.menuItem3);
            this.menuItem1.MenuItems.Add(this.menuItem4);
            this.menuItem1.MenuItems.Add(this.menuItem5);
            this.menuItem1.MenuItems.Add(this.menuItem6);
            this.menuItem1.MenuItems.Add(this.menuItem7);
            this.menuItem1.MenuItems.Add(this.menuItem8);
            this.menuItem1.MenuItems.Add(this.menuItem21);
            this.menuItem1.Text = "Commands";
            // 
            // menuItem3
            // 
            this.menuItem3.Text = "Battery Level";
            this.menuItem3.Click += new System.EventHandler(this.menuItem3_Click);
            // 
            // menuItem4
            // 
            this.menuItem4.Text = "Battery Percent";
            this.menuItem4.Click += new System.EventHandler(this.menuItem4_Click);
            // 
            // menuItem5
            // 
            this.menuItem5.Text = "Get PDU Count";
            this.menuItem5.Click += new System.EventHandler(this.menuItem5_Click);
            // 
            // menuItem6
            // 
            this.menuItem6.MenuItems.Add(this.menuItem14);
            this.menuItem6.MenuItems.Add(this.menuItem15);
            this.menuItem6.MenuItems.Add(this.menuItem16);
            this.menuItem6.MenuItems.Add(this.menuItem17);
            this.menuItem6.MenuItems.Add(this.menuItem18);
            this.menuItem6.MenuItems.Add(this.menuItem19);
            this.menuItem6.Text = "Sensitivity";
            this.menuItem6.Click += new System.EventHandler(this.menuItem6_Click);
            // 
            // menuItem14
            // 
            this.menuItem14.Text = "Update";
            this.menuItem14.Click += new System.EventHandler(this.menuItem14_Click);
            // 
            // menuItem15
            // 
            this.menuItem15.Text = "1.5 G";
            this.menuItem15.Click += new System.EventHandler(this.menuItem15_Click);
            // 
            // menuItem16
            // 
            this.menuItem16.Text = "2 G";
            this.menuItem16.Click += new System.EventHandler(this.menuItem16_Click);
            // 
            // menuItem17
            // 
            this.menuItem17.Text = "4 G";
            this.menuItem17.Click += new System.EventHandler(this.menuItem17_Click);
            // 
            // menuItem18
            // 
            this.menuItem18.Text = "8 G";
            this.menuItem18.Click += new System.EventHandler(this.menuItem18_Click);
            // 
            // menuItem19
            // 
            this.menuItem19.Text = "12 G";
            // 
            // menuItem7
            // 
            this.menuItem7.Text = "Get Calibration";
            this.menuItem7.Click += new System.EventHandler(this.menuItem7_Click);
            // 
            // menuItem8
            // 
            this.menuItem8.MenuItems.Add(this.menuItem20);
            this.menuItem8.MenuItems.Add(this.menuItem9);
            this.menuItem8.MenuItems.Add(this.menuItem10);
            this.menuItem8.MenuItems.Add(this.menuItem11);
            this.menuItem8.MenuItems.Add(this.menuItem12);
            this.menuItem8.MenuItems.Add(this.menuItem13);
            this.menuItem8.Text = "Sampling Rate";
            // 
            // menuItem20
            // 
            this.menuItem20.Text = "Update";
            this.menuItem20.Click += new System.EventHandler(this.menuItem20_Click);
            // 
            // menuItem9
            // 
            this.menuItem9.Text = "20";
            this.menuItem9.Click += new System.EventHandler(this.menuItem9_Click);
            // 
            // menuItem10
            // 
            this.menuItem10.Text = "30";
            this.menuItem10.Click += new System.EventHandler(this.menuItem10_Click);
            // 
            // menuItem11
            // 
            this.menuItem11.Text = "40";
            this.menuItem11.Click += new System.EventHandler(this.menuItem11_Click);
            // 
            // menuItem12
            // 
            this.menuItem12.Text = "80";
            this.menuItem12.Click += new System.EventHandler(this.menuItem12_Click);
            // 
            // menuItem13
            // 
            this.menuItem13.Text = "90";
            this.menuItem13.Click += new System.EventHandler(this.menuItem13_Click);
            // 
            // menuItem21
            // 
            this.menuItem21.MenuItems.Add(this.menuItem24);
            this.menuItem21.MenuItems.Add(this.menuItem22);
            this.menuItem21.MenuItems.Add(this.menuItem23);
            this.menuItem21.MenuItems.Add(this.menuItem25);
            this.menuItem21.MenuItems.Add(this.menuItem26);
            this.menuItem21.MenuItems.Add(this.menuItem27);
            this.menuItem21.Text = "Mode";
            // 
            // menuItem24
            // 
            this.menuItem24.Text = "Update";
            this.menuItem24.Click += new System.EventHandler(this.menuItem24_Click);
            // 
            // menuItem22
            // 
            this.menuItem22.Text = "Continuous";
            this.menuItem22.Click += new System.EventHandler(this.menuItem22_Click);
            // 
            // menuItem23
            // 
            this.menuItem23.Text = "Efficient 30";
            this.menuItem23.Click += new System.EventHandler(this.menuItem23_Click);
            // 
            // menuItem25
            // 
            this.menuItem25.Text = "Efficient 60";
            this.menuItem25.Click += new System.EventHandler(this.menuItem25_Click);
            // 
            // menuItem26
            // 
            this.menuItem26.Text = "Efficient 90";
            // 
            // menuItem27
            // 
            this.menuItem27.Text = "Efficient 120";
            // 
            // menuItem2
            // 
            this.menuItem2.Text = "Disconnect";
            this.menuItem2.Click += new System.EventHandler(this.menuItem2_Click);
            // 
            // panel1
            // 
            this.panel1.Location = new System.Drawing.Point(3, 37);
            this.panel1.Name = "panel1";
            this.panel1.Size = new System.Drawing.Size(234, 192);
            this.panel1.Paint += new System.Windows.Forms.PaintEventHandler(this.panel1_Paint);
            // 
            // label1
            // 
            this.label1.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.label1.Location = new System.Drawing.Point(3, 9);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(197, 32);
            this.label1.Text = "Wocket";
            // 
            // timer1
            // 
            this.timer1.Tick += new System.EventHandler(this.timer1_Tick);
            // 
            // label2
            // 
            this.label2.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.label2.Location = new System.Drawing.Point(14, 237);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(223, 29);
            this.label2.Text = "Sent:";
            // 
            // label3
            // 
            this.label3.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.label3.Location = new System.Drawing.Point(14, 270);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(223, 46);
            this.label3.Text = "Received:";
            // 
            // Form2
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 320);
            this.Controls.Add(this.label3);
            this.Controls.Add(this.label2);
            this.Controls.Add(this.label1);
            this.Controls.Add(this.panel1);
            this.Menu = this.mainMenu1;
            this.Name = "Form2";
            this.Text = "Wocket";
            this.ResumeLayout(false);

        }

  

        #endregion

        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.MenuItem menuItem3;
        private System.Windows.Forms.MenuItem menuItem2;
        private System.Windows.Forms.Panel panel1;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Timer timer1;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.MenuItem menuItem4;
        private System.Windows.Forms.MenuItem menuItem5;
        private System.Windows.Forms.MenuItem menuItem6;
        private System.Windows.Forms.MenuItem menuItem7;
        private System.Windows.Forms.MenuItem menuItem8;
        private System.Windows.Forms.MenuItem menuItem9;
        private System.Windows.Forms.MenuItem menuItem10;
        private System.Windows.Forms.MenuItem menuItem11;
        private System.Windows.Forms.MenuItem menuItem12;
        private System.Windows.Forms.MenuItem menuItem13;
        private System.Windows.Forms.MenuItem menuItem14;
        private System.Windows.Forms.MenuItem menuItem15;
        private System.Windows.Forms.MenuItem menuItem16;
        private System.Windows.Forms.MenuItem menuItem17;
        private System.Windows.Forms.MenuItem menuItem18;
        private System.Windows.Forms.MenuItem menuItem19;
        private System.Windows.Forms.MenuItem menuItem20;
        private System.Windows.Forms.MenuItem menuItem21;
        private System.Windows.Forms.MenuItem menuItem24;
        private System.Windows.Forms.MenuItem menuItem22;
        private System.Windows.Forms.MenuItem menuItem23;
        private System.Windows.Forms.MenuItem menuItem25;
        private System.Windows.Forms.MenuItem menuItem26;
        private System.Windows.Forms.MenuItem menuItem27;
    }
}