using System;
using System.Windows.Forms;
using System.Collections;
using System.Drawing;
using System.IO;
using Wockets.Data.Annotation;
using Wockets.Utils;
using WocketsApplication.Utils;


namespace WocketsApplication.Calibrator
{
    partial class CalibratorForm
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

#if (PocketPC)
        //   ActivityList aList;
#endif
        //Intialize different interface components
        private void InitializeInterface()
        {


            #region Common PC and Pocket PC Widgets
            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.menuItem1 = new System.Windows.Forms.MenuItem();
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.menuItem3 = new System.Windows.Forms.MenuItem();
            this.menuItem4 = new System.Windows.Forms.MenuItem();
            this.menuItem5 = new System.Windows.Forms.MenuItem();
            this.menuItem6 = new System.Windows.Forms.MenuItem();
            this.menuItem7 = new System.Windows.Forms.MenuItem();
            this.menuItem8 = new System.Windows.Forms.MenuItem();
            this.menuItem9 = new System.Windows.Forms.MenuItem();
            this.menuItem21 = new System.Windows.Forms.MenuItem();
            this.menuItem22 = new System.Windows.Forms.MenuItem();
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
            this.label3 = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.label1 = new System.Windows.Forms.Label();
            this.label6 = new System.Windows.Forms.Label();
            this.label8 = new System.Windows.Forms.Label();
            this.label7 = new System.Windows.Forms.Label();
            this.label9 = new System.Windows.Forms.Label();
            this.readDataTimer = new System.Windows.Forms.Timer();
            this.panel1 = new Panel();
            this.panel2 = new Panel();
            this.pictureBox1 = new PictureBox();
            this.pictureLabel = new Label();


            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            this.mainMenu1.MenuItems.Add(this.menuItem2);
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "Quit";
            this.menuItem1.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // menuItem2
            // 
            this.menuItem2.MenuItems.Add(this.menuItem3);
            this.menuItem2.MenuItems.Add(this.menuItem4);
            this.menuItem2.MenuItems.Add(this.menuItem5);
            this.menuItem2.MenuItems.Add(this.menuItem9);
            this.menuItem2.MenuItems.Add(this.menuItem10);
            this.menuItem2.MenuItems.Add(this.menuItem13);
            this.menuItem2.MenuItems.Add(this.menuItem16);
            this.menuItem2.Text = "Options";
            // 
            // menuItem3
            // 






            // 
            // menuItem10
            // 
            this.menuItem10.MenuItems.Add(this.menuItem11);
            this.menuItem10.MenuItems.Add(this.menuItem12);
            this.menuItem10.Text = "Plotting";
            // 
            // menuItem11
            // 
            this.menuItem11.Text = "Show";
            this.menuItem11.Click += new System.EventHandler(this.menuItem11_Click);
            // 
            // menuItem12
            // 
            this.menuItem12.Text = "Full Screen";
            this.menuItem12.Enabled = false;
            // 
            // menuItem13
            // 
            this.menuItem13.MenuItems.Add(this.menuItem14);
            this.menuItem13.MenuItems.Add(this.menuItem15);
            this.menuItem13.Text = "Sound";
            this.menuItem13.Enabled = false;
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
            this.panel2.Location = new System.Drawing.Point(0, 0);
            this.panel1.Paint += new System.Windows.Forms.PaintEventHandler(this.Panel1_Paint);







            // 
            // readDataTimer
            // 
            this.readDataTimer.Enabled = false;
            this.readDataTimer.Interval = 10;
            this.readDataTimer.Tick += new System.EventHandler(this.readDataTimer_Tick);
            // 
            // Wockets Calibration Form
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.KeyPreview = true;
            this.Name = "Wockets Calibration";
            this.Text = "Calibrate...";


            #endregion Common PC and Pocket PC Widgets

            #region PC and PocketPC specific Widgets
#if (PocketPC)
            this.tabControl1 = new System.Windows.Forms.TabControl();
            this.tabPage1 = new System.Windows.Forms.TabPage();
            this.tabControl1.SuspendLayout();


            // tabControl1
            // 
            this.tabControl1.Controls.Add(this.tabPage1);
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

            //Add Panels to the tab pages
            this.tabPage1.Controls.Add(this.panel1);
            this.tabPage1.Controls.Add(this.panel2);
            this.panel2.Visible = false;

            this.Controls.Add(this.tabControl1);
            this.tabControl1.ResumeLayout(false);
            this.Menu = this.mainMenu1;
#else


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
            this.tabPage1.Width = this.panel1.Width = this.panel2.Width = this.tabControl1.ClientSize.Width;
            this.tabPage1.Height = this.panel1.Height = this.panel2.Height = this.tabControl1.ClientSize.Height;
#else
            this.form1.Width = this.form2.Width = this.form3.Width = this.form4.Width = this.form5.Width = this.ClientSize.Width;
            this.form1.Height = this.form2.Height = this.form3.Height = this.form4.Height = this.form5.Height = this.ClientSize.Height;
            this.panel1.Width = this.panel2.Width = this.panel4.Width = this.panel5.Width = this.form1.ClientSize.Width - Constants.SCREEN_LEFT_MARGIN - Constants.SCREEN_RIGHT_MARGIN;
            this.panel2.Height = this.panel4.Height = this.panel5.Height = this.form1.ClientSize.Height;

            this.panel1.Height = (int) (System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height * 0.70);
            this.panel3.Width = (int)(System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height * 0.20); this.panel3.Height = (int)(System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height * 0.20);
#endif

            //Intialize Labels 40% of the screen
            this.sensorLabels = new Hashtable();
            int num_rows = (int)((this.wocketsController._Sensors.Count + 3) / 2); //additional row for HR and total sampling rate
            int textBoxHeight = ((int)(0.35 * this.panel1.ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
            int textBoxWidth = ((this.panel1.ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 2);
            int currentTextY = (int)(this.panel1.Height * 0.60);
            int leftTextX = Constants.WIDGET_SPACING;
            int rightTextX = (Constants.WIDGET_SPACING * 2) + textBoxWidth;
            int currentTextX = Constants.WIDGET_SPACING;
            System.Windows.Forms.Label calibrationLabel = new System.Windows.Forms.Label();
            calibrationLabel.Width = textBoxWidth*2;
            calibrationLabel.Height = textBoxHeight;


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
                   Constants.MAX_FONT, this.button1.Size, "textAC011", this.button1.Font, (float)0.9, (float)0.9);

            //foreach (Sensor sensor in this.sensors.Sensors)
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                System.Windows.Forms.Label t = new System.Windows.Forms.Label();
                t.Text = "Wocket" + this.wocketsController._Sensors[i]._ID;
                t.Name = t.Text;
                t.Size = new System.Drawing.Size(textBoxWidth, textBoxHeight);
                t.Location = new System.Drawing.Point(currentTextX, currentTextY);
                t.Font = textFont;
                this.sensorLabels.Add(t.Text, t);
                //this.tabPage1.Controls.Add(t);
                this.panel1.Controls.Add(t);
                if (currentTextX == leftTextX)
                    currentTextX = rightTextX;
                else
                {
                    currentTextX = leftTextX;
                    currentTextY += (textBoxHeight + Constants.WIDGET_SPACING);
                }

            }


            calibrationLabel.Text = "X=?    Y=?    Z=?";
            calibrationLabel.Name = calibrationLabel.Text;
            calibrationLabel.Size = new System.Drawing.Size(textBoxWidth*2, textBoxHeight/3);
            calibrationLabel.Location = new System.Drawing.Point(leftTextX, currentTextY+textBoxHeight+5);
            calibrationLabel.Font = textFont;
            this.sensorLabels.Add("calibration", calibrationLabel);
            //this.tabPage1.Controls.Add(samplingLabel);
            this.panel1.Controls.Add(calibrationLabel);
            System.Windows.Forms.Label errorLabel = new System.Windows.Forms.Label();
            errorLabel.Size = new System.Drawing.Size(this.panel1.ClientSize.Width - 10, 30);
            errorLabel.Location = new System.Drawing.Point(5, 100);
            errorLabel.Visible = false;
            this.panel1.Controls.Add(errorLabel);
            this.sensorLabels.Add("ErrorLabel", errorLabel);


            this.button1.Width = textBoxWidth;
            this.button1.Height = textBoxHeight/2;
            textFont = this.button1.Font =
                GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.button1.Size, "Calibrate", this.button1.Font, (float)0.9, (float)0.9);

            this.button2.Enabled = true;
            this.button2.Visible = true;
            this.button2.Font = textFont;
            this.button2.Width = textBoxWidth;
            this.button2.Height = textBoxHeight / 2;
            this.button2.Location = new Point((this.panel1.Width - this.button2.Width) / 2, calibrationLabel.Location.Y + calibrationLabel.Height +5);
            this.panel1.Controls.Add(this.button2);


            this.pictureBox1.Name="PictureBox1";
            this.pictureBox1.Size = new Size(this.panel2.Width, this.panel2.Height- (2*textBoxHeight));
            this.pictureBox1.SizeMode = PictureBoxSizeMode.CenterImage;
            this.pictureBox1.Location= new System.Drawing.Point(5, 5);

            this.pictureLabel.Name = "PictureLabel";
            this.pictureLabel.Size = new System.Drawing.Size(this.panel2.Width, textBoxHeight);
            this.pictureLabel.Location = new System.Drawing.Point(5, this.pictureBox1.Size.Height+5);
            this.pictureLabel.Font = textFont;


            this.button3.Enabled = true;
            this.button3.Visible = true;
            this.button3.Font = textFont;
            this.button3.Width = textBoxWidth;
            this.button3.Height = textBoxHeight / 2;
            this.button3.Location = new Point(this.panel2.Width/2, this.pictureLabel.Size.Height + this.pictureLabel.Location.Y + 2);
     


            this.panel2.Controls.Add(this.pictureLabel);
            this.panel2.Controls.Add(this.pictureBox1);
            this.panel2.Controls.Add(this.button3);




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


        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.readDataTimer = new System.Windows.Forms.Timer();
            this.button1 = new System.Windows.Forms.Button();
            this.button2 = new System.Windows.Forms.Button();
            this.button3 = new System.Windows.Forms.Button();
            this.SuspendLayout();
            // 
            // readDataTimer
            // 
            this.readDataTimer.Interval = 10;
            this.readDataTimer.Tick += new System.EventHandler(this.readDataTimer_Tick);

            // 
            // button1
            // 
            this.button1.Location = new System.Drawing.Point(17, 80);
            this.button1.Name = "button1";
            this.button1.Size = new System.Drawing.Size(72, 20);
            this.button1.TabIndex = 0;
            this.button1.Text = "Calibrate";

            // 
            // button2
            // 
            this.button2.Location = new System.Drawing.Point(17, 80);
            this.button2.Name = "button2";
            this.button2.Size = new System.Drawing.Size(72, 20);
            this.button2.TabIndex = 1;
            this.button2.Text = "Calibrate";
            this.button2.Click += new EventHandler(button2_Click);

            // 
            // button3
            // 
            this.button3.Location = new System.Drawing.Point(17, 80);
            this.button3.Name = "button3";
            this.button3.Size = new System.Drawing.Size(72, 20);
            this.button3.TabIndex = 1;
            this.button3.Text = "Next";
            this.button3.Click += new EventHandler(button3_Click);

            // 
            // CalibratorForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.Controls.Add(this.button1);           
            this.KeyPreview = true;
            this.Menu = this.mainMenu1;
            this.Name = "Wockets Calibration";
            this.Text = "Collect Data...";
            this.ResumeLayout(false);

        }

      
        void button3_Click(object sender, EventArgs e)
        {
            this.panel1.Visible = true;
            this.panel2.Visible = false;
            for (int i = 0; (i < 3); i++)
                this.calibrations[this.calibrationDirection][i] = 0.0;
            this.calibrationCounter = 0;


            this.isCalibrating = true;
        }
      
        
        void button2_Click(object sender, EventArgs e)
        {
            if (this.calibrationDirection == 7)
            {

                //Store calibration data
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._X1G = this.calibrations[0][0];
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._XN1G = this.calibrations[2][0];

                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._Y1G = this.calibrations[3][1];
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._YN1G = this.calibrations[1][1];

                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._Z1G = this.calibrations[4][2];
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._ZN1G = this.calibrations[5][2];


                
                //calculate STD
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._XSTD = 0;
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._YSTD = 0;
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._ZSTD = 0;
                for (int i = 0; (i < CALIBRATION_SAMPLES); i++)
                {
                    ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._XSTD += Math.Pow(this.samples[i][0] - this.calibrations[6][0], 2.0);
                    ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._YSTD += Math.Pow(this.samples[i][1] - this.calibrations[6][1], 2.0);
                    ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._ZSTD += Math.Pow(this.samples[i][2] - this.calibrations[6][2], 2.0);
                }

                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._XSTD = Math.Sqrt(((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._XSTD) / (CALIBRATION_SAMPLES-1);
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._YSTD = Math.Sqrt(((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._YSTD) / (CALIBRATION_SAMPLES-1);
                ((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._ZSTD = Math.Sqrt(((Wockets.Sensors.Accelerometers.Accelerometer)this.wocketsController._Sensors[0])._ZSTD) / (CALIBRATION_SAMPLES-1);

                TextWriter tw = new StreamWriter(Constants.SENSOR_CONFIGURATIONS_DIRECTORY+this.wocketsController._FileName);
                tw.WriteLine(this.wocketsController.ToXML());
                tw.Flush();
                tw.Close();
                menuItem1_Click(null, null);
            }
            else
            {
                this.button2.Visible = false;
                this.pictureBox1.Image = this.calibrationImages[calibrationDirection];

                if (calibrationDirection == 6)
                    this.pictureLabel.Text = "Place the wocket flat on a table";
                else
                    this.pictureLabel.Text = "Place the wocket as shown";

                this.panel2.Visible = true;
                this.panel1.Visible = false;
            }

        }


        #endregion


        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.MenuItem menuItem2;
        private System.Windows.Forms.MenuItem menuItem3;
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
        private System.Windows.Forms.Timer readDataTimer;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label label4;

        private System.Windows.Forms.Label label6;
        private System.Windows.Forms.Label label8;
        private System.Windows.Forms.Label label7;
        private System.Windows.Forms.Label label9;

        private System.Windows.Forms.MenuItem menuItem21;
        private System.Windows.Forms.MenuItem menuItem22;
        private System.Windows.Forms.Panel panel1,panel2,panel3,panel4;
        private System.Windows.Forms.PictureBox pictureBox1;
        private System.Windows.Forms.Label pictureLabel;

        private System.Windows.Forms.Button button1;
        private System.Windows.Forms.Button button2;
        private System.Windows.Forms.Button button3;


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