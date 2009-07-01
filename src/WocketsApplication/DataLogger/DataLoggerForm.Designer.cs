using System;
using System.Windows.Forms;
using System.Collections;
using System.Drawing;
using Wockets.Receivers;
using Wockets.Data.Annotation;
using Wockets.Utils;
using WocketsApplication.Utils;
using Wockets.Data.Classifiers.Utils;
using Wockets.Data.Summary;

#if (PocketPC)
using OpenNETCF.GDIPlus;
using Charts.twodimensional;
#endif

using System.Threading;

namespace WocketsApplication.DataLogger
{
    partial class DataLoggerForm
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;
        private System.Windows.Forms.MainMenu mainMenu1;

        private System.Windows.Forms.MainMenu mainMenuPanel1;
        private System.Windows.Forms.MenuItem menuItemQuitPanel1;
        private System.Windows.Forms.MenuItem menuItemPlottingPanel1;
        private System.Windows.Forms.MenuItem menuItemOnPlottingPanel1;
        private System.Windows.Forms.MenuItem menuItemOffPlottingPane1l;


#if (PocketPC)
        private Chart pieChart;
        IntPtr token;
        BitmapPlus bmp;
        GdiplusStartupInput input = new GdiplusStartupInput();
        GdiplusStartupOutput output;
#endif
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

#if (PocketPC)
        ActivityListSummary aList;
#endif
        //Intialize different interface components
        Image disconnectedWocketImage;
        Image connectedWocketImage;
        private void InitializeInterface()
        {


            #region Common PC and Pocket PC Widgets

            this.mainMenuPanel1 = new MainMenu();
            this.menuItemQuitPanel1 = new MenuItem();
            this.menuItemPlottingPanel1 = new MenuItem();
            this.menuItemOffPlottingPane1l = new MenuItem();
            this.menuItemOnPlottingPanel1 = new MenuItem();

            this.mainMenuPanel1.MenuItems.Add(this.menuItemQuitPanel1);
            this.menuItemQuitPanel1.Click += new EventHandler(menuItemQuitPanel1_Click);
            this.mainMenuPanel1.MenuItems.Add(this.menuItemPlottingPanel1);
            this.menuItemPlottingPanel1.MenuItems.Add(this.menuItemOffPlottingPane1l);
            this.menuItemOffPlottingPane1l.Click += new EventHandler(menuItemOffPlottingPane1l_Click);
            this.menuItemPlottingPanel1.MenuItems.Add(this.menuItemOnPlottingPanel1);
            this.menuItemOnPlottingPanel1.Click += new EventHandler(menuItemOnPlottingPanel1_Click);
            this.menuItemOnPlottingPanel1.Checked = true;

            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.menuItem1 = new System.Windows.Forms.MenuItem();
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.menuItem3 = new System.Windows.Forms.MenuItem();
            this.menuItem8 = new System.Windows.Forms.MenuItem();
            this.menuItem10 = new System.Windows.Forms.MenuItem();
            this.menuItem11 = new System.Windows.Forms.MenuItem();
            this.menuItem12 = new System.Windows.Forms.MenuItem();
            this.menuItem13 = new System.Windows.Forms.MenuItem();
            this.menuItem14 = new System.Windows.Forms.MenuItem();
            this.menuItem15 = new System.Windows.Forms.MenuItem();
            this.menuItem16 = new System.Windows.Forms.MenuItem();
            this.menuItem17 = new System.Windows.Forms.MenuItem();
            this.menuItem18 = new System.Windows.Forms.MenuItem();
            this.menuItem19 = new System.Windows.Forms.MenuItem();
            this.menuItem20 = new System.Windows.Forms.MenuItem();
            //this.label5 = new System.Windows.Forms.Label();
            this.label4 = new System.Windows.Forms.Label();
            this.pictureBox1 = new System.Windows.Forms.PictureBox();
            this.label3 = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.label1 = new System.Windows.Forms.Label();
            this.resetButton = new System.Windows.Forms.Button();
            this.startStopButton = new System.Windows.Forms.Button();
            this.oxyconButton = new System.Windows.Forms.Button();
            this.label6 = new System.Windows.Forms.Label();
            //this.label16 = new System.Windows.Forms.Label();
            this.label8 = new System.Windows.Forms.Label();
            this.label7 = new System.Windows.Forms.Label();
            this.label9 = new System.Windows.Forms.Label();
            this.readDataTimer = new System.Windows.Forms.Timer();
            this.panel1 = new Panel();
            this.panel2 = new Panel();
            this.panel3 = new Panel();
            this.panel4 = new Panel();
            this.panel5 = new Panel();

            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            this.mainMenu1.MenuItems.Add(this.menuItem2);
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "Menu";
            this.menuItem1.MenuItems.Add(this.menuItem12);
            this.menuItem1.MenuItems.Add(this.menuItem13);
            // 
            // menuItem2
            // 
            this.menuItem2.MenuItems.Add(this.menuItem3);
            this.menuItem2.MenuItems.Add(this.menuItem10);
            this.menuItem2.MenuItems.Add(this.menuItem11);
            this.menuItem2.MenuItems.Add(this.menuItem8);
            this.menuItem2.Text = "Options";
            // 
            // menuItem3
            // 
            this.menuItem3.Text = "Power Saver";
            this.menuItem3.Click += new System.EventHandler(this.powersaver_Click);
            this.menuItem3.Enabled = true;
            // 
            // menuItem8
            // 
            this.menuItem8.Click += new System.EventHandler(this.training_Click);
            this.menuItem8.Text = "Training";
            this.menuItem8.Enabled = true;
            // 
            // menuItem10
            // 
            this.menuItem10.Click += new System.EventHandler(this.plotting_Click);
            this.menuItem10.Text = "Plotting";
            this.menuItem10.Checked = true;
            this.menuItem10.Enabled = true;
            // 
            // menuItem11
            // 
            this.menuItem11.Click += new System.EventHandler(this.saving_Click);
            this.menuItem11.Text = "Saving Data";
            this.menuItem11.Enabled = true;
            this.menuItem11.Checked = true;
            // 
            // menuItem12
            // 
            this.menuItem12.Text = "Quit";
            this.menuItem12.Enabled = true;
            this.menuItem12.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // menuItem13
            // 
            this.menuItem13.Text = "Minimize";
            this.menuItem13.Enabled = true;
            this.menuItem13.Click += new System.EventHandler(this.menuItem13_Click);
            // 
            // menuItem14
            // 
            this.menuItem14.Text = "Turn off";
            this.menuItem14.Enabled = false;
            // 
            // menuItem15
            // 
            this.menuItem15.Text = "Turn on";
            this.menuItem15.Enabled = false;
            // 
            // menuItem16
            // 
            this.menuItem16.MenuItems.Add(this.menuItem17);
            this.menuItem16.MenuItems.Add(this.menuItem18);
            this.menuItem16.MenuItems.Add(this.menuItem19);
            this.menuItem16.MenuItems.Add(this.menuItem20);
            this.menuItem16.Text = "Steps";
            this.menuItem16.Enabled = false;
            // 
            // menuItem17
            // 
            this.menuItem17.Text = "Beep On";
            this.menuItem17.Enabled = false;
            // 
            // menuItem18
            // 
            this.menuItem18.Text = "Beep Off";
            this.menuItem18.Enabled = false;
            // 
            // menuItem19
            // 
            this.menuItem19.Text = "Compute On";
            this.menuItem19.Enabled = false;
            // 
            // menuItem20
            // 
            this.menuItem20.Text = "Compute Off";
            this.menuItem20.Enabled = false;


            //prepare common PC and Pocket PC widgets

            // 
            // label5
            // 
            //this.label5.Location = new System.Drawing.Point(106, 1);
            //this.label5.Name = "label5";
            //this.label5.Size = new System.Drawing.Size(81, 14);
            //this.label5.Text = "stopped";
            // 
            // label4
            // 
            this.label4.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label4.ForeColor = System.Drawing.Color.Red;
            this.label4.Location = new System.Drawing.Point(187, 2);
            this.label4.Name = "label4";
            this.label4.Size = new System.Drawing.Size(65, 13);
            this.label4.Text = "HR";
            // 
            // pictureBox1
            // 
            //this.pictureBox1.Image = ((System.Drawing.Image)(resources.GetObject("pictureBox1.Image")));
            this.pictureBox1.Location = new System.Drawing.Point(209, -1);
            this.pictureBox1.Name = "pictureBox1";
            this.pictureBox1.Size = new System.Drawing.Size(26, 20);
            // 
            // label3
            // 
            this.label3.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label3.Location = new System.Drawing.Point(53, 2);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(50, 13);
            this.label3.Text = "0:00:00";
            // 
            // label2
            // 
            this.label2.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label2.Location = new System.Drawing.Point(45, 2);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(13, 13);
            this.label2.Text = "/";
            // 
            // label1
            // 
            this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label1.ForeColor = System.Drawing.Color.Green;
            this.label1.Location = new System.Drawing.Point(2, 2);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(50, 13);
            this.label1.Text = "0:00:00";
            // 
            // resetButton
            // 
            this.resetButton.BackColor = System.Drawing.Color.Yellow;
            this.resetButton.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Regular);
            this.resetButton.Location = new System.Drawing.Point(127, 182);
            this.resetButton.Name = "resetButton";
            this.resetButton.Size = new System.Drawing.Size(78, 57);
            this.resetButton.TabIndex = 12;
            this.resetButton.Text = "Reset";
            this.resetButton.Click += new System.EventHandler(this.resetButton_Click);
            // 
            // startStopButton
            // 
            this.startStopButton.BackColor = System.Drawing.Color.Green;
            this.startStopButton.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Regular);
            this.startStopButton.Location = new System.Drawing.Point(32, 182);
            this.startStopButton.Name = "startStopButton";
            this.startStopButton.Size = new System.Drawing.Size(78, 57);
            this.startStopButton.TabIndex = 11;
            this.startStopButton.Text = "Start";
            this.startStopButton.Click += new System.EventHandler(this.startStopButton_Click);

            // 
            // Oxycon Button
            // 
            this.oxyconButton.BackColor = System.Drawing.Color.Green;
            this.oxyconButton.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Regular);
            this.oxyconButton.Location = new System.Drawing.Point(2, 2);
            this.oxyconButton.Name = "oxyconButton";
            this.oxyconButton.Size = new System.Drawing.Size(100, 100);
            this.oxyconButton.TabIndex = 11;
            this.oxyconButton.Text = "Sync Oxycon";
            this.oxyconButton.Click += new System.EventHandler(this.oxycon_Click);


            // 
            // label8
            // 
            this.label8.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.label8.Location = new System.Drawing.Point(103, 9);
            this.label8.Name = "label8";
            this.label8.Size = new System.Drawing.Size(130, 20);
            this.label8.Text = "E (Sampling Rate)";
            // 
            // label7
            // 
            this.label7.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.label7.Location = new System.Drawing.Point(7, 8);
            this.label7.Name = "label7";
            this.label7.Size = new System.Drawing.Size(100, 20);
            this.label7.Text = "Sensor ID";


            //Prepare common PC and Pocket PC panels 
            this.panel1.Location = new System.Drawing.Point(0, 0);
            this.panel1.Paint += new System.Windows.Forms.PaintEventHandler(this.Panel1_Paint);
            this.panel2.Location = new System.Drawing.Point(0, 0);
            this.panel3.Location = new System.Drawing.Point(0, 0);
            this.panel4.Location = new System.Drawing.Point(0, 0);
            this.panel5.Location = new System.Drawing.Point(0, 0);



            



            // 
            // readDataTimer
            // 
            this.readDataTimer.Enabled = true;
            this.readDataTimer.Interval = 30;
            this.readDataTimer.Tick += new System.EventHandler(this.readDataTimer_Tick);
            // 
            // MITesDataCollectionForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.KeyPreview = true;
            this.Name = "WocketsSoftware";
            this.Text = "Collect Data...";


            #endregion Common PC and Pocket PC Widgets

            #region PC and PocketPC specific Widgets
#if (PocketPC)
            this.tabControl1 = new System.Windows.Forms.TabControl();
            this.tabPage1 = new System.Windows.Forms.TabPage();
            this.tabPage2 = new System.Windows.Forms.TabPage();
            this.tabPage3 = new System.Windows.Forms.TabPage();
            this.tabPage4 = new System.Windows.Forms.TabPage();
            this.tabPage5 = new System.Windows.Forms.TabPage();
            this.tabControl1.SuspendLayout();
            this.tabPage2.SuspendLayout();
            this.tabPage3.SuspendLayout();
            this.tabPage4.SuspendLayout();
            this.tabPage5.SuspendLayout();


            // tabControl1
            // 
            this.tabControl1.Controls.Add(this.tabPage1);
            this.tabControl1.Controls.Add(this.tabPage2);
            this.tabControl1.Controls.Add(this.tabPage4);
            this.tabControl1.Controls.Add(this.tabPage3);
            this.tabControl1.Controls.Add(this.tabPage5);
            this.tabControl1.Location = new System.Drawing.Point(0, 0);
            this.tabControl1.Name = "tabControl1";
            this.tabControl1.SelectedIndex = 0;
            this.tabControl1.Size = new System.Drawing.Size(240, 265);
            this.tabControl1.TabIndex = 0;
            // 
            // tabPage1
            // 
            this.tabPage1.Location = this.panel1.Location = new System.Drawing.Point(0, 0);
            this.tabPage1.Name = "tabPage1";
            this.tabPage1.Size = new System.Drawing.Size(240, 242);
            this.tabPage1.Text = "Visualize";

            // 
            // tabPage2
            // 
            this.panel2.Controls.Add(this.label5);

            this.panel2.Controls.Add(this.pictureBox1);
            this.panel2.Controls.Add(this.label3);
            this.panel2.Controls.Add(this.label2);
            this.panel2.Controls.Add(this.label1);
            this.panel2.Controls.Add(this.resetButton);
            this.panel2.Controls.Add(this.startStopButton);
            this.tabPage2.Location = new System.Drawing.Point(0, 0);
            this.tabPage2.Name = "tabPage2";
            this.tabPage2.Size = new System.Drawing.Size(232, 239);
            this.tabPage2.Text = "Annotate";
            // 
            // tabPage3
            // 
            //this.tabPage3.Controls.Add(this.label6);
            //this.tabPage3.Controls.Add(this.label16);

            GpStatusPlus stat = NativeMethods.GdiplusStartup(out token, input, out output);
            pieChart = new Charts.twodimensional.PieChart();
            pieChart.IsStretch = true;
            this.aList = new ActivityListSummary();
            int chartIndex=0;
            ActivitySummary asummary=null;
            ActivityList chartCategory = this.annotatedSession.OverlappingActivityLists[0];
            for (chartIndex = 0; (chartIndex < chartCategory.Count); chartIndex++)
            {      
                asummary = new ActivitySummary();
                asummary.Name = chartCategory[chartIndex]._Name;
                asummary.StartTime = 0;
                asummary.EndTime = 0;
                asummary.Percent = 1;
                this.aList.Activities.Add(asummary);
            }

            asummary = new ActivitySummary();
            asummary.Name = "empty2";
            asummary.StartTime = 0;
            asummary.EndTime = 0;
            asummary.Percent = 100 - chartIndex;
            this.aList.Activities.Add(asummary);

   
            pieChart.Data = aList.toPercentHashtable();
            pieChart.SetActivity("No Activity");
            pieChart.SetTime(0, 0, 0);
            pieChart.SetCalories(0, 0);
            this.tabPage3.Controls.Add(pieChart);
            //pieChartClearButton = new Button();
            //pieChartClearButton.Text = "Clear";
            //pieChartClearButton.Name = "pieChartButton";
            //pieChartClearButton.Size = new System.Drawing.Size(72, 20);
            //pieChartClearButton.Location = new Point(0, 0);
            //pieChartClearButton.Click += new System.EventHandler(this.pieChartClearButton_Click);
            //this.tabPage3.Controls.Add(pieChartClearButton);


            this.tabPage3.Location = new System.Drawing.Point(0, 0);
            this.tabPage3.Name = "tabPage3";
            this.tabPage3.Size = new System.Drawing.Size(232, 239);
            this.tabPage3.Text = "Summary";
            // tabPage4
            // 
            //this.panel4.Controls.Add(this.label8);
            //this.panel4.Controls.Add(this.label7);
            //this.panel4.Controls.Add(this.label9);
            this.tabPage4.Location = new System.Drawing.Point(0, 0);
            this.tabPage4.Name = "tabPage4";
            this.tabPage4.Size = new System.Drawing.Size(232, 239);
            this.tabPage4.Text = "Activity";

            //tabPage5
            //

            this.tabPage5.Location = new System.Drawing.Point(0, 0);
            this.tabPage5.Name = "tabPage5";
            this.tabPage5.Size = new System.Drawing.Size(232, 239);
            this.tabPage5.Text = "Status";
            this.SampLabels = new Label[this.wocketsController._Sensors.Count];

            Label cur = new Label();
            cur = new Label();
            cur.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Regular);
            cur.Text = "Samp/sec, #Disconnects, Time Disconnect";
            cur.Location = new Point(5, 16);
            cur.Size = new Size(500, 50);
            this.panel5.Controls.Add(cur);
            for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
            {
                cur = new Label();
                cur.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
                cur.Text = "Sensor "+this.wocketsController._Sensors[i]._ID+": ?, ?, ?";
                cur.Location = new Point(16, 66 + i * 30);
                cur.Size = new Size(500, 40);
                this.SampLabels[i] = cur;
                this.panel5.Controls.Add(cur);
                cur.BringToFront();
            }



            //Add Panels to the tab pages
            this.tabPage1.Controls.Add(this.panel1);
            this.tabPage2.Controls.Add(this.panel2);
            this.tabPage3.Controls.Add(this.panel3);
            this.tabPage4.Controls.Add(this.panel4);
            this.tabPage5.Controls.Add(this.panel5);

            this.Controls.Add(this.tabControl1);
            this.tabControl1.ResumeLayout(false);
            this.tabPage2.ResumeLayout(false);
            this.tabPage3.ResumeLayout(false);
            this.tabPage4.ResumeLayout(false);
            this.tabPage5.ResumeLayout(false);
            this.Menu = this.mainMenuPanel1;
#else

            this.form1 = new Form();
            this.form2 = new Form();
            this.form3 = new Form();
            this.form4 = new Form();
            this.form5 = new Form();
            this.form1.SuspendLayout();
            this.form2.SuspendLayout();
            this.form3.SuspendLayout();
            this.form4.SuspendLayout();
            this.form5.SuspendLayout();


            // 
            // form1
            // 
            this.form1.Location =new System.Drawing.Point(0, 0);
            this.form1.Name = "form1";
            this.form1.Size = new System.Drawing.Size(240, 242);
            this.form1.Text = "Visualize";

            // 
            // form2
            // 
            this.form2.Location = new System.Drawing.Point(0, 0);
            this.form2.Name = "form2";
            this.form2.Size = new System.Drawing.Size(240, 242);
            this.form2.Text = "Annotate";

            // 
            // form3
            // 
            this.form3.Location = new System.Drawing.Point(0, 0);
            this.form3.Name = "form3";
            this.form3.Size = new System.Drawing.Size(120, 120);
            this.form3.Text = "Oxycon";

            // 
            // form4
            // 
            this.form4.Location = new System.Drawing.Point(0, 0);
            this.form4.Name = "form4";
            this.form4.Size = new System.Drawing.Size(240, 242);
            this.form4.Text = "Quality";


            // 
            // form5
            // 
            this.form5.Location = new System.Drawing.Point(0, 0);
            this.form5.Name = "form5";
            this.form5.Size = new System.Drawing.Size(240, 242);
            this.form5.Text = "Calibrate";


            this.form1.Controls.Add(this.panel1);
            this.form2.Controls.Add(this.panel2);
            this.form3.Controls.Add(this.panel3);
            this.form4.Controls.Add(this.panel4);
            this.form5.Controls.Add(this.panel5);

            // 
            // tabPage2
            // 
            //this.form2.Controls.Add(this.label5);
            this.form2.Controls.Add(this.label4);
            this.form2.Controls.Add(this.pictureBox1);
            this.form2.Controls.Add(this.label3);
            this.form2.Controls.Add(this.label2);
            this.form2.Controls.Add(this.label1);
            this.form2.Controls.Add(this.resetButton);
            this.form2.Controls.Add(this.startStopButton);
            this.form3.Controls.Add(this.oxyconButton);
            //this.form3.Controls.Add(this.label6);
            this.form4.Controls.Add(this.label8);
            this.form4.Controls.Add(this.label7);
            this.form4.Controls.Add(this.label9);


            this.panel5.Controls.Add(this.label17);
            this.panel5.Controls.Add(this.pictureBox2);
            this.panel5.Controls.Add(this.button2);

            
          


            //Add Panels to the tab pages
            this.form1.Controls.Add(this.panel1);
            this.form2.Controls.Add(this.panel2);
            this.form3.Controls.Add(this.panel3);
            this.form4.Controls.Add(this.panel4);
            this.form5.Controls.Add(this.panel5);
            this.form1.Menu = this.mainMenu1;
            this.form2.Menu = this.mainMenuTab2;

#endif

            #endregion PC and PocketPC specific Widgets

            this.ResumeLayout(false);

            #region Calculation of Widgets locations and Sizes
            //Initialize screen dimensions           
            this.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width - Constants.WIDGET_SPACING;
            this.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height - Constants.WIDGET_SPACING;
            if ((this.Width > Constants.MAX_FORM_WIDTH) || (this.Height > Constants.MAX_FORM_HEIGHT))
            {
                this.Width = this.Width / 2;
                this.Height = this.Height / 2;
            }

#if (PocketPC)
            //Initialize Tab control dimensions
            this.tabControl1.Width = this.ClientSize.Width;
            this.tabControl1.Height = this.ClientSize.Height;
            this.tabPage1.Width = this.panel1.Width = this.tabPage2.Width = this.panel2.Width = this.tabPage3.Width = this.panel3.Width = this.tabPage4.Width = this.panel4.Width = this.tabPage5.Width = this.panel5.Width =this.tabControl1.ClientSize.Width;//-Constants.SCREEN_LEFT_MARGIN-Constants.SCREEN_RIGHT_MARGIN;
            this.tabPage1.Height = this.panel1.Height = this.tabPage2.Height = this.panel2.Height = this.tabPage3.Height = this.panel3.Height = this.tabPage4.Height = this.panel4.Height = this.tabPage5.Height = this.panel5.Height =this.tabControl1.ClientSize.Height;
#else
            this.form1.Width = this.form2.Width = this.form3.Width = this.form4.Width = this.form5.Width = this.ClientSize.Width;
            this.form1.Height = this.form2.Height = this.form3.Height = this.form4.Height = this.form5.Height = this.ClientSize.Height;
            this.panel1.Width = this.panel2.Width = this.panel4.Width = this.panel5.Width = this.form1.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
            this.panel2.Height = this.panel4.Height = this.panel5.Height = this.form1.ClientSize.Height;

            this.panel1.Height = (int) (System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height * 0.70);
            this.panel3.Width = (int)(System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height * 0.20); this.panel3.Height = (int)(System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height * 0.20);
#endif

            //Intialize Labels 40% of the screen
            this.sensorLabels = new Hashtable();
            this.sensorStatus = new Hashtable();
            this.sensorStat = new Hashtable();
            this.sensorBattery = new Hashtable();
            int num_rows = (int)((this.wocketsController._Sensors.Count + 2) / 2); //additional row for HR and total sampling rate
            int textBoxHeight = ((int)(0.35 * this.panel1.ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
            int textBoxWidth = ((this.panel1.ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 3);
            int currentTextY = (int)(this.panel1.ClientSize.Height * 0.60);
            int leftTextX = Constants.WIDGET_SPACING+32;
            int rightTextX = ((Constants.WIDGET_SPACING+32) * 2) + textBoxWidth;
            int currentTextX = Constants.WIDGET_SPACING+32;
            this.samplingLabel = new System.Windows.Forms.Label();
            samplingLabel.Width = textBoxWidth;
            samplingLabel.Height = textBoxHeight;


            //Button1 is a dummy button that is removed afterwards. After lots of
            //debugging the only way to create a graphics is by adding a button to the
            //actual form
            // Size olderSize = new Size(this.button1.Width, this.button1.Height);

            this.button1.Enabled = false;
            this.button1.Visible = false;
            this.button1.Width = textBoxWidth;
            this.button1.Height = textBoxHeight;
            Font textFont = this.button1.Font =
                GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.button1.Size, "textBoxAC11", this.button1.Font, (float)0.9, (float)0.9);

            connectedWocketImage = (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "connected.gif");
            disconnectedWocketImage = (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "disconnected.gif");
            //foreach (Sensor sensor in this.sensors.Sensors)
            for (int i=0;(i<this.wocketsController._Sensors.Count);i++)
            {
                System.Windows.Forms.Label t = new System.Windows.Forms.Label();
                PictureBox p = new PictureBox();
                p.Size = new Size(32, 32);
                p.Image = connectedWocketImage;
                p.Location = new System.Drawing.Point(currentTextX-32, currentTextY);
                PictureBox p2 = new PictureBox();
                p2.Size = new Size(32, 32);
                p2.Image = this.batteryImg[0];
                p2.Location = new System.Drawing.Point(currentTextX + 50, currentTextY+5);
                t.Text = "W" + this.wocketsController._Sensors[i]._ID;
                t.Name = "W" + this.wocketsController._Sensors[i]._ID;
                t.Size = new System.Drawing.Size(textBoxWidth, 32);
                t.Location = new System.Drawing.Point(currentTextX, currentTextY);
                t.Font = textFont;
                this.sensorLabels.Add("W" + this.wocketsController._Sensors[i]._ID, t);
                this.sensorStatus.Add("W" + this.wocketsController._Sensors[i]._ID, p);
                this.sensorStat.Add("W" + this.wocketsController._Sensors[i]._ID, this.connectedWocketImage);
                this.sensorBattery.Add("W" + this.wocketsController._Sensors[i]._ID, p2);
                //this.tabPage1.Controls.Add(t);
                this.panel1.Controls.Add(t);
                this.panel1.Controls.Add(p);
                this.panel1.Controls.Add(p2);
                p2.BringToFront();
                if (currentTextX == leftTextX)
                    currentTextX = rightTextX;
                else
                {
                    currentTextX = leftTextX;
                    currentTextY += (textBoxHeight + Constants.WIDGET_SPACING);
                }
            }


            samplingLabel.Text = "SampRate";
            samplingLabel.Name = samplingLabel.Text;
            samplingLabel.Size = new System.Drawing.Size(textBoxWidth, textBoxHeight);
            samplingLabel.Location = new System.Drawing.Point(currentTextX, currentTextY);
            samplingLabel.Font = textFont;
            this.sensorLabels.Add("SampRate", samplingLabel);
            //this.tabPage1.Controls.Add(samplingLabel);
            System.Windows.Forms.Label errorLabel = new System.Windows.Forms.Label();
            errorLabel.Size = new System.Drawing.Size(this.panel1.ClientSize.Width - 10, 30);
            errorLabel.Location = new System.Drawing.Point(5, 100);
            errorLabel.Visible = false;
            this.panel1.Controls.Add(errorLabel);
            this.sensorLabels.Add("ErrorLabel", errorLabel);



            //Initialize Buttons

            this.categoryButtons = new ArrayList();
            this.buttonIndex = new ArrayList();
            int button_width = this.panel2.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
            int button_height = (this.panel2.ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - (this.annotatedSession.OverlappingActivityLists.Count * Constants.WIDGET_SPACING)) / (this.annotatedSession.OverlappingActivityLists.Count + 1);
            int button_x = Constants.WIDGET_SPACING;
            int button_y = Constants.WIDGET_SPACING * 2;
            int delta_y = button_height + Constants.WIDGET_SPACING;
            int button_id = 0;



            //foreach (Category category in this.annotation.Categories)
            for (int i=0;(i<this.annotatedSession.OverlappingActivityLists.Count);i++)
            {
                
                ActivityList category=this.annotatedSession.OverlappingActivityLists[0];
                System.Windows.Forms.Button button = new System.Windows.Forms.Button();

                button.Location = new System.Drawing.Point(button_x, button_y + button_id * delta_y);
                button.Name = button_id.ToString();
                //button.Font = buttonFont;
                button.Size = new System.Drawing.Size(button_width, button_height);
                //button.TabIndex = button_id;
                button.Text = category[0]._Name;// ((AXML.Label)category.Labels[0]).Name;
                //button.UseVisualStyleBackColor = true;
                button.Click += new System.EventHandler(this.button_Click);
                this.categoryButtons.Add(button);
                this.panel2.Controls.Add(button);

                //check the longest label for this button
                //foreach (AXML.Label label in category.Labels)
                for (int j=0;(j<category.Count);j++)
                {
                    string newlabel = category[j]._Name;//label.Name;

                    if (newlabel.Length > longest_label.Length)
                        longest_label = newlabel;
                }
                this.buttonIndex.Add(0);
                button_id++;
            }

            if (longest_label.Length < 5)
                longest_label = "RESET";

            //Size oldSize=this.Size;
            //this.Size=new Size(button_width,button_height);         
            this.button1.Width = button_width;
            this.button1.Height = button_height;
            Font buttonFont = this.button1.Font =
                GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                    Constants.MAX_FONT, this.button1.Size, longest_label, this.button1.Font, (float)0.9, (float)0.9);
            foreach (System.Windows.Forms.Button button in categoryButtons)
                button.Font = buttonFont;
            //adjust round buttons start/stop -reset

            //this.startStopButton.Font = GUI.CalculateBestFitFont(this.CreateGraphics(), Constants.MIN_FONT, Constants.MAX_FONT,
            //this.ClientSize, "RESET", new Font(Constants.FONT_FAMILY, (float)32.0, FontStyle.Bold), (float)0.90, (float)0.90);
            //this.Size = oldSize;

            button_width = (this.panel2.Size.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 2;
            this.resetButton.Font = this.startStopButton.Font = buttonFont;
            this.startStopButton.Size = new System.Drawing.Size(button_width, button_height);
            this.resetButton.Size = new System.Drawing.Size(button_width, button_height);
            this.startStopButton.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, button_y + button_id * delta_y);
            this.resetButton.Location = new System.Drawing.Point(this.startStopButton.Location.X + this.startStopButton.Size.Width + Constants.WIDGET_SPACING, button_y + button_id * delta_y);



            //Menu Tab 2
            this.mainMenuTab2 = new System.Windows.Forms.MainMenu();
            this.menuItem1Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem2Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem3Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem4Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem5Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem6Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem7Tab2 = new System.Windows.Forms.MenuItem();
            this.menuItem8Tab2 = new System.Windows.Forms.MenuItem();


            this.menuItem1Tab2.Text = "Quit";
            this.menuItem1Tab2.Click += new System.EventHandler(this.menuItem1_Click);
            this.menuItem2Tab2.Text = "Options";

            this.mainMenuTab2.MenuItems.Add(this.menuItem1Tab2);
            this.mainMenuTab2.MenuItems.Add(this.menuItem2Tab2);
            this.menuItem3Tab2.Text = "Session";
            this.menuItem4Tab2.Text = "Training";

            this.menuItem2Tab2.MenuItems.Add(this.menuItem3Tab2);
            this.menuItem2Tab2.MenuItems.Add(this.menuItem4Tab2);


            this.menuItem5Tab2.Text = "Start";
            this.menuItem6Tab2.Text = "End";
            this.menuItem3Tab2.MenuItems.Add(this.menuItem5Tab2);
            this.menuItem3Tab2.MenuItems.Add(this.menuItem6Tab2);
            this.menuItem5Tab2.Click += new EventHandler(menuItem5Tab2_Click);
            this.menuItem6Tab2.Click += new EventHandler(menuItem6Tab2_Click);


            this.menuItem7Tab2.Text = "Auto";
            this.menuItem8Tab2.Text = "Manual";
            this.menuItem4Tab2.MenuItems.Add(this.menuItem7Tab2);
            this.menuItem4Tab2.MenuItems.Add(this.menuItem8Tab2);
            this.menuItem7Tab2.Click += new EventHandler(menuItem7Tab2_Click);
            this.menuItem8Tab2.Click += new EventHandler(menuItem8Tab2_Click);

#if (PocketPC)
            this.tabControl1.SelectedIndexChanged += new EventHandler(tabControl1_Changed);
#endif

            //if there is more than one category, manual training is the only option
            //if (this.annotation.Categories.Count > 1)
            if (this.annotatedSession.OverlappingActivityLists.Count>1)
            {
                this.menuItem7Tab2.Enabled = false;
                this.menuItem8Tab2.Enabled = false;
                this.menuItem8Tab2.Checked = true;
            }
            this.menuItem6Tab2.Enabled = false;
            this.menuItem8Tab2.Checked = true;
            this.startStopButton.Enabled = true;
            this.resetButton.Enabled = true;
            //this.label5.Text = Constants.MANUAL_MODE_SESSION;

#if (PocketPC)
            this.ClientSize = new Size(this.tabControl1.Width, this.tabControl1.Height);
#else
            this.form1.ClientSize = new Size(this.panel1.Width, this.panel1.Height);
            this.form2.ClientSize = new Size(this.panel2.Width, this.panel2.Height);
            this.form3.ClientSize = new Size(this.panel3.Width, this.panel3.Height);
            this.form4.ClientSize = new Size(this.panel4.Width, this.panel4.Height);
            this.form5.ClientSize = new Size(this.panel5.Width, this.panel5.Height);
#endif


            #endregion Calculation of Widgets locations and sizes


        }

        void menuItemOnPlottingPanel1_Click(object sender, EventArgs e)
        {
            this.menuItemOffPlottingPane1l.Checked = false;
            this.menuItemOnPlottingPanel1.Checked = true;
            this.isPlotting = true;
        }

        void menuItemOffPlottingPane1l_Click(object sender, EventArgs e)
        {
            this.menuItemOffPlottingPane1l.Checked = true;
            this.menuItemOnPlottingPanel1.Checked = false;
            this.isPlotting = false;
        }

        private bool isQuitting = false;
        void menuItemQuitPanel1_Click(object sender, EventArgs e)
        {
#if (PocketPC)
            //if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
#else
            if (MessageBox.Show("Are you sure you want to Quit MITes Software?", "Confirm", MessageBoxButtons.YesNo) == DialogResult.Yes)
#endif
           // {
               isQuitting = true;
              /* while(this.readDataTimer.Enabled)
                   Thread.Sleep(50);*/
                //this.readDataTimer.Enabled = false;
                //this.qualityTimer.Enabled = false;
            //}




        }



        private void InitializeQualityInterface()
        {
            this.labels = new System.Windows.Forms.Label[this.wocketsController._Sensors.Count];//[this.sensors.MaximumSensorID + 1];
            this.expectedLabels = new System.Windows.Forms.Label[this.wocketsController._Sensors.Count];//[this.sensors.MaximumSensorID + 1];
            this.samplesPerSecond = new System.Windows.Forms.Label[this.wocketsController._Sensors.Count];//[this.sensors.MaximumSensorID + 1];

            int counter = 0;
            label_width = (this.panel4.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 3;

            label_height = 0;

            //if (this.sensors.IsHR)
              //  label_height = (this.panel4.ClientSize.Height - Constants.SCREEN_TOP_MARGIN - Constants.SCREEN_BOTTOM_MARGIN - ((this.sensors.Sensors.Count) * Constants.WIDGET_SPACING)) / (this.sensors.Sensors.Count);
            //else
            label_height = (this.panel4.ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - ((this.wocketsController._Sensors.Count) * Constants.WIDGET_SPACING)) / (this.wocketsController._Sensors.Count + 1);


            this.button1.Width = label_width;
            this.button1.Height = label_height;
            this.button1.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Bold);
            textFont = this.button1.Font =
                GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.button1.Size, "E(Samp. Rate) ", this.button1.Font, (float)0.9, (float)0.9);


            this.label7.Size = this.label8.Size = this.label9.Size = new Size(label_width, label_height);
            this.label7.Font = this.label8.Font = this.label9.Font = textFont;
            this.label7.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
            this.label8.Location = new System.Drawing.Point(Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
            this.label8.Text = "E(Samp. Rate)";

            this.label9.Location = new System.Drawing.Point(Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
            this.label9.Text = "Samples/Second";

            counter++;
            //foreach (Sensor sensor in this.sensors.Sensors)
            for (int i=0;(i<this.wocketsController._Sensors.Count);i++)
            {

                //setup the labels for the expected sampling rates
                int sensor_id = Convert.ToInt32(this.wocketsController._Sensors[i]._ID);

                System.Windows.Forms.Label label = new System.Windows.Forms.Label();
                //label.AutoSize = true;
                label.Size = new Size(label_width, label_height);
                label.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
                label.Name = this.wocketsController._Sensors[i]._ID.ToString();
                label.Text = "Sensor " + this.wocketsController._Sensors[i]._ID;
                label.Font = textFont;
                this.labels[sensor_id] = label;
                //this.panel5.Controls.Add(label);

                System.Windows.Forms.Label label2 = new System.Windows.Forms.Label();
                //label2.AutoSize = true;
                label2.Size = new Size(label_width, label_height);
                label2.Location = new System.Drawing.Point(Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
                label2.Name = "E(SR) " + this.wocketsController._Sensors[i]._ID;
                label2.Text = "unknown"; //rate.ToString("00.00") + "%";
                label2.Font = textFont;
                //this.panel5.Controls.Add(label2);
                this.expectedLabels[sensor_id] = label2;

                System.Windows.Forms.Label label3 = new System.Windows.Forms.Label();
                //label2.AutoSize = true;
                label3.Size = new Size(label_width, label_height);
                label3.Location = new System.Drawing.Point(Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (counter * (label_height + Constants.WIDGET_SPACING)));
                label2.Name = "Samples " + this.wocketsController._Sensors[i]._ID;
                label3.Text = "unknown"; //rate.ToString("00.00") + "%";
                label3.Font = textFont;
                //this.panel5.Controls.Add(label3);
                this.samplesPerSecond[sensor_id] = label3;

                counter++;
            }
            //#if (PocketPC)
            //            foreach (Sensor sensor in this.sensors.BuiltinSensors)
            //            {

            //                    System.Windows.Forms.Label label = new System.Windows.Forms.Label();
            //                    //label.AutoSize = true;
            //                    label.Size = new Size(label_width, label_height);
            //                    label.Location = new System.Drawing.Point(Constants.SCREEN_LEFT_MARGIN, Constants.SCREEN_TOP_MARGIN + (counter * (label_height + Constants.WIDGET_SPACING)));
            //                    label.Name = sensor.Type;
            //                    label.Text = sensor.Type;
            //                    label.Font = textFont;
            //                    this.builtInlabels[sensor.Type] = label;
            //                    this.panel4.Controls.Add(label);

            //                    System.Windows.Forms.Label label2 = new System.Windows.Forms.Label();
            //                    //label2.AutoSize = true;
            //                    label2.Size = new Size(label_width, label_height);
            //                    label2.Location = new System.Drawing.Point(Constants.SCREEN_LEFT_MARGIN + label_width + Constants.WIDGET_SPACING, Constants.SCREEN_TOP_MARGIN + (counter * (label_height + Constants.WIDGET_SPACING)));
            //                    label2.Name = "E(SR) " +sensor.Type;
            //                    label2.Text = "unknown"; //rate.ToString("00.00") + "%";
            //                    label2.Font = textFont;
            //                    this.panel4.Controls.Add(label2);
            //                    this.builtInExpectedLabels[sensor.Type] = label2;

            //                    System.Windows.Forms.Label label3 = new System.Windows.Forms.Label();
            //                    //label2.AutoSize = true;
            //                    label3.Size = new Size(label_width, label_height);
            //                    label3.Location = new System.Drawing.Point(Constants.SCREEN_LEFT_MARGIN + label_width + Constants.WIDGET_SPACING + label_width + Constants.WIDGET_SPACING, Constants.SCREEN_TOP_MARGIN + (counter * (label_height + Constants.WIDGET_SPACING)));
            //                    label2.Name = "Samples " + sensor.Type;
            //                    label3.Text = "unknown"; //rate.ToString("00.00") + "%";
            //                    label3.Font = textFont;
            //                    this.panel4.Controls.Add(label3);
            //                    this.builtInSamplesPerSecond[sensor.Type] = label3;
            //                counter++;
            //            }

            //#endif
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.readDataTimer = new System.Windows.Forms.Timer();
            this.qualityTimer = new System.Windows.Forms.Timer();
            this.HRTimer = new System.Windows.Forms.Timer();
            this.button1 = new System.Windows.Forms.Button();
            this.SuspendLayout();


            // 
            // button1
            // 
            this.button1.Location = new System.Drawing.Point(17, 80);
            this.button1.Name = "button1";
            this.button1.Size = new System.Drawing.Size(72, 20);
            this.button1.TabIndex = 0;
            this.button1.Text = "button1";
            // 
            // MITesDataCollectionForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.Controls.Add(this.button1);
            this.KeyPreview = true;
            this.Menu = this.mainMenuPanel1;
            this.Name = "MITesDataCollectionForm";
            this.Text = "Collect Data...";
            this.ResumeLayout(false);

        }


        #endregion


        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.MenuItem menuItem2;
        private System.Windows.Forms.MenuItem menuItem3;
        private System.Windows.Forms.MenuItem menuItem8;
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
        private System.Windows.Forms.Timer readDataTimer;
        private System.Windows.Forms.PictureBox pictureBox1;
        private System.Windows.Forms.PictureBox pictureBox2;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Button resetButton;
        private System.Windows.Forms.Button startStopButton;
        private System.Windows.Forms.Button oxyconButton;
        private System.Windows.Forms.Label label4;
        private System.Windows.Forms.Label label5;
        private System.Windows.Forms.Label label6;
        private System.Windows.Forms.Label label8;
        private System.Windows.Forms.Label label7;
        private System.Windows.Forms.Label label9;
        private System.Windows.Forms.Label label16;
        private System.Windows.Forms.Label label17;
        private System.Windows.Forms.Panel panel1, panel2, panel3, panel4, panel5;
        private System.Windows.Forms.Timer qualityTimer;
        private System.Windows.Forms.Timer HRTimer;
        private System.Windows.Forms.Label trainingLabel;
        private System.Windows.Forms.Button button1;
        private System.Windows.Forms.Button button2;
        private System.Windows.Forms.Button pieChartClearButton;
        private System.Windows.Forms.MainMenu mainMenuTab2;
        private System.Windows.Forms.MenuItem menuItem1Tab2;
        private System.Windows.Forms.MenuItem menuItem2Tab2;
        private System.Windows.Forms.MenuItem menuItem3Tab2;
        private System.Windows.Forms.MenuItem menuItem4Tab2;
        private System.Windows.Forms.MenuItem menuItem5Tab2;
        private System.Windows.Forms.MenuItem menuItem6Tab2;
        private System.Windows.Forms.MenuItem menuItem7Tab2;
        private System.Windows.Forms.MenuItem menuItem8Tab2;

        #region PC and PocketPC Specific Widgets
#if (PocketPC)
        private System.Windows.Forms.TabControl tabControl1;
        private System.Windows.Forms.TabPage tabPage1;
        private System.Windows.Forms.TabPage tabPage2;
        private System.Windows.Forms.TabPage tabPage3;
        private System.Windows.Forms.TabPage tabPage4;
        private System.Windows.Forms.TabPage tabPage5;

#else
        private System.Windows.Forms.Form form1;
        private System.Windows.Forms.Form form2;
        private System.Windows.Forms.Form form3;
        private System.Windows.Forms.Form form4;
        private System.Windows.Forms.Form form5;
     

#endif
        #endregion PocketPC Widgets

    }
}