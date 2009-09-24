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
using OpenNETCF.GDIPlus;
using Charts.twodimensional;


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
        private System.Windows.Forms.MainMenu mainMenu2;
        private System.Windows.Forms.MainMenu mainMenuPanel1;
        private System.Windows.Forms.MenuItem menuItemQuitPanel1;
        private System.Windows.Forms.MenuItem menuItemPlottingPanel1;
        private System.Windows.Forms.MenuItem menuItemOnPlottingPanel1;
        private System.Windows.Forms.MenuItem menuItemOffPlottingPane1l;


#if (PocketPC)
        private Chart pieChart;
        IntPtr token;
        GdiplusStartupInput input = new GdiplusStartupInput();
        GdiplusStartupOutput output;
#endif
        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (!this.disposed)
            {
                if (disposing)
                {
                    this.isQuitting = true;
                    if (components != null)
                        components.Dispose();
                }
                base.Dispose(disposing);
                disposed = true;
            }
        }

#if (PocketPC)
        ActivityListSummary aList;
#endif
        //Intialize different interface components
        Image disconnectedWocketImage;
        Image connectedWocketImage;

        private const string VISUALIZE_PANEL = "Visualize";
        private const string ANNOTATE_PANEL = "Annotate";
        private const string ANNOTATE_LIST_PANEL = "List";
        private const string LOG_PANEL = "Log";
        private const string CLASSIFIER_LABEL_PANEL = "ClassifierLabel";
        private const string QUALITY_PANEL = "Quality";
        private const string BUTTON_ANNOTATION_PANEL = "Button";
        private const string GAME_PANEL = "Game";
        private const string EMPTY_PANEL = "Empty";
        private Hashtable views;
        private Hashtable panels;
        private ArrayList activityButtons = new ArrayList();

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
            this.mainMenu2 = new System.Windows.Forms.MainMenu();
            this.menuItem1 = new System.Windows.Forms.MenuItem();
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.menuItem3 = new System.Windows.Forms.MenuItem();
            this.menuItem4 = new System.Windows.Forms.MenuItem();
            this.menuItem5 = new System.Windows.Forms.MenuItem();
            this.menuItem6 = new System.Windows.Forms.MenuItem();
            this.menuItem7 = new System.Windows.Forms.MenuItem();
            this.menuItem8 = new System.Windows.Forms.MenuItem();
            this.menuItem9 = new System.Windows.Forms.MenuItem();
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
            this.menuItem21 = new System.Windows.Forms.MenuItem();
            this.menuItem22 = new System.Windows.Forms.MenuItem();
            this.menuItem23 = new System.Windows.Forms.MenuItem();
            this.menuItem24 = new System.Windows.Forms.MenuItem();
            this.menuItem25 = new System.Windows.Forms.MenuItem();
            

            this.label3 = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.label1 = new System.Windows.Forms.Label();

            this.label3b = new System.Windows.Forms.Label();
            this.label2b = new System.Windows.Forms.Label();
            this.label1b = new System.Windows.Forms.Label();


            this.label6 = new System.Windows.Forms.Label();
            this.label8 = new System.Windows.Forms.Label();
            this.label7 = new System.Windows.Forms.Label();
            this.label9 = new System.Windows.Forms.Label();
            this.readDataTimer = new System.Windows.Forms.Timer();


            this.panels = new Hashtable();
            this.views = new Hashtable();


            /* Visualize Panel */
            Panel panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name = VISUALIZE_PANEL;
            panel.Paint += new System.Windows.Forms.PaintEventHandler(this.Panel1_Paint);
            this.panels.Add(VISUALIZE_PANEL, panel);

            panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name = EMPTY_PANEL;
            this.panels.Add(EMPTY_PANEL, panel);

            panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name = ANNOTATE_LIST_PANEL;
            this.panels.Add(ANNOTATE_LIST_PANEL, panel);

            panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name = CLASSIFIER_LABEL_PANEL;
            this.panels.Add(LOG_PANEL, panel);

            panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name = QUALITY_PANEL;
            this.panels.Add(QUALITY_PANEL, panel);


            panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name =BUTTON_ANNOTATION_PANEL;
            this.panels.Add(BUTTON_ANNOTATION_PANEL, panel);

            panel = new Panel();
            panel.Visible = false;
            panel.Location = new System.Drawing.Point(0, 0);
            panel.Name =GAME_PANEL;
            this.panels.Add(GAME_PANEL, panel);


            this.CommandBox = new System.Windows.Forms.TextBox();
            this.annotatePanelArray = new Panel[] { ((Panel)this.panels[ANNOTATE_LIST_PANEL]), ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]) };
            this.defaultColor = Color.SkyBlue;
            this.panelColor = Color.White;
            this.clickColor = Color.DodgerBlue;
            this.SuspendLayout();
            //
            //Commands Panel
            //
            this.CommandBox.Multiline = true;
            this.CommandBox.Location = new System.Drawing.Point(((Panel)this.panels[LOG_PANEL]).Location.X + 10, ((Panel)this.panels[LOG_PANEL]).Location.Y + 10);
            this.CommandBox.Size = new System.Drawing.Size(this.ClientSize.Width - 260, this.ClientSize.Height - 350);
            this.CommandBox.Text = "Commands Dialogue:\r\n";
            ((Panel)this.panels[LOG_PANEL]).Controls.Add(this.CommandBox);

            // 
            // Options Menu
            //
            this.mainMenu1.MenuItems.Add(this.menuItem1);      
            this.menuItem1.Text = "Options";

            // Views
            this.menuItem1.MenuItems.Add(this.menuItem2);
            this.menuItem2.Text = "Views";
            this.menuItem2.Enabled = true;
            
           
            this.menuItem2.MenuItems.Add(this.menuItem3);
            this.menuItem2.MenuItems.Add(this.menuItem4);
            this.menuItem2.MenuItems.Add(this.menuItem7);
            this.menuItem2.MenuItems.Add(this.menuItem8);
            this.menuItem2.MenuItems.Add(this.menuItem9);    


      
            this.menuItem3.Text = VISUALIZE_PANEL;
            this.menuItem3.Enabled = true;
            this.menuItem3.Checked = true;
            this.menuItem3.Click += new System.EventHandler(this.view_menu_Click);
            this.views[VISUALIZE_PANEL] = this.menuItem3;

            this.menuItem4.Text = ANNOTATE_PANEL;
            this.menuItem4.Enabled = true;
            

            this.menuItem4.MenuItems.Add(this.menuItem5);
            this.menuItem5.Text = ANNOTATE_LIST_PANEL;
            this.menuItem5.Enabled = true;
            this.menuItem5.Click += new System.EventHandler(this.view_menu_Click);
            this.views[ANNOTATE_LIST_PANEL] = this.menuItem5;
            
            this.menuItem4.MenuItems.Add(this.menuItem6);
            this.menuItem6.Text = BUTTON_ANNOTATION_PANEL;
            this.menuItem6.Enabled = true;            
            this.menuItem6.Click += new System.EventHandler(this.view_menu_Click);
            this.views[BUTTON_ANNOTATION_PANEL] = this.menuItem6;

            this.menuItem7.Text = QUALITY_PANEL;
            this.menuItem7.Enabled = true;
            this.menuItem7.Click += new System.EventHandler(this.view_menu_Click);
            this.views[QUALITY_PANEL] = this.menuItem7;

            this.menuItem8.Text = LOG_PANEL;
            this.menuItem8.Enabled = true;
            this.menuItem8.Click += new System.EventHandler(this.view_menu_Click);
            this.views[LOG_PANEL] = this.menuItem8;

            this.menuItem9.Text = GAME_PANEL;
            this.menuItem9.Enabled = true;
            this.menuItem9.Click += new System.EventHandler(this.view_menu_Click);
            this.views[GAME_PANEL] = this.menuItem9;


            // Data Modes
            this.menuItem1.MenuItems.Add(this.menuItem10);
            this.menuItem10.Text = "Data";
            this.menuItem10.Enabled = true;

            this.menuItem10.MenuItems.Add(this.menuItem11);
            this.menuItem11.Text = "Save";
            this.menuItem11.Enabled = true;
            this.menuItem11.Click += new EventHandler(this.saving_Click);

            this.menuItem10.MenuItems.Add(this.menuItem12);
            this.menuItem12.Text = "Plot";
            this.menuItem12.Enabled = true;
            this.menuItem12.Click += new System.EventHandler(this.plotting_Click);            
            this.menuItem12.Checked = true;

            this.menuItem10.MenuItems.Add(this.menuItem23);
            this.menuItem23.Text = "Train";
            this.menuItem23.Enabled = true;
            this.menuItem23.Click += new EventHandler(this.training_Click);
            this.menuItem23.Checked = false;

            this.menuItem10.MenuItems.Add(this.menuItem24);
            this.menuItem24.Text = "Classify";
            this.menuItem24.Enabled = true;
            this.menuItem24.Click += new System.EventHandler(this.classifying_Click);
            this.menuItem24.Checked = false;

            this.menuItem10.MenuItems.Add(this.menuItem25);
            this.menuItem25.Text = "Play Escape";
            this.menuItem25.Enabled = true;
            this.menuItem25.Click += new System.EventHandler(this.gaming_Click);
            this.menuItem25.Checked = false;

            //Minimize
            this.menuItem1.MenuItems.Add(this.menuItem13);
            this.menuItem13.Text = "Minimize";
            this.menuItem13.Enabled = true;
            this.menuItem13.Click += new System.EventHandler(this.minimize_Click);

            //Quit
            this.menuItem1.MenuItems.Add(this.menuItem14);
            this.menuItem14.Text = "Quit";
            this.menuItem14.Enabled = true;
            this.menuItem14.Click += new System.EventHandler(this.quit_Click);



            // 
            // Commands Menu
            //
            this.mainMenu1.MenuItems.Add(this.menuItem15);
            this.menuItem15.Text = "Commands";
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                if (this.wocketsController._Sensors[i]._Class == Wockets.Sensors.SensorClasses.Wockets)
                {
                    MenuItem mItem= new MenuItem();
                    string address=((Wockets.Receivers.RFCOMMReceiver)((Wockets.Sensors.Accelerometers.Wocket)(this.wocketsController._Sensors[i]))._Receiver)._Address;
                    this.menuItem15.MenuItems.Add(mItem);
                    mItem.Text = "Wocket " + address.Substring(address.Length - 2, 2);
                    mItem.Enabled = true;

                    MenuItem getItem = new MenuItem();
                    mItem.MenuItems.Add(getItem);
                    getItem.Text = "Get";
                    getItem.Enabled = true;                    

                    MenuItem batteryItem = new MenuItem();
                    getItem.MenuItems.Add(batteryItem);
                    batteryItem.Text = "Battery Level";
                    batteryItem.Enabled = true;

                    MenuItem pcItem = new MenuItem();
                    getItem.MenuItems.Add(pcItem);
                    pcItem.Text = "Packet Count";
                    pcItem.Enabled = false;

                    MenuItem smItem = new MenuItem();
                    getItem.MenuItems.Add(smItem);
                    smItem.Text = "Sleep Mode";
                    smItem.Enabled = false;

                    MenuItem senItem = new MenuItem();
                    getItem.MenuItems.Add(senItem);
                    senItem.Text = "Sensitivity";
                    senItem.Enabled = false;

                    MenuItem calItem = new MenuItem();
                    getItem.MenuItems.Add(calItem);
                    calItem.Text = "Calibration";
                    calItem.Enabled = false;

                    MenuItem tpItem = new MenuItem();
                    getItem.MenuItems.Add(tpItem);
                    tpItem.Text = "Trans. Power";
                    tpItem.Enabled = false;

                    MenuItem srItem = new MenuItem();
                    getItem.MenuItems.Add(srItem);
                    srItem.Text = "Samp. Rate";
                    srItem.Enabled = false;

                    MenuItem discItem = new MenuItem();
                    getItem.MenuItems.Add(discItem);
                    discItem.Text = "Discoverable";
                    discItem.Enabled = false;

                    MenuItem tmItem = new MenuItem();
                    getItem.MenuItems.Add(tmItem);
                    tmItem.Text = "Trans. Mode";
                    tmItem.Enabled = false;

                    MenuItem atItem = new MenuItem();
                    getItem.MenuItems.Add(atItem);
                    atItem.Text = "Alive Timer";
                    atItem.Enabled = false;

                    MenuItem pdtItem = new MenuItem();
                    getItem.MenuItems.Add(pdtItem);
                    pdtItem.Text = "Pwr Dwn Timer";
                    pdtItem.Enabled = false;

                    MenuItem ctItem = new MenuItem();
                    getItem.MenuItems.Add(ctItem);
                    ctItem.Text = "Conf. Timer";
                    ctItem.Enabled = false;

                    MenuItem brItem = new MenuItem();
                    getItem.MenuItems.Add(brItem);
                    brItem.Text = "Baud Rate";
                    brItem.Enabled = false;


                    //Set MENU
                    MenuItem setItem = new MenuItem();
                    mItem.MenuItems.Add(setItem);                  
                    setItem.Text = "Set";
                    setItem.Enabled = true;

                    smItem = new MenuItem();
                    setItem.MenuItems.Add(smItem);
                    smItem.Text = "Sleep Mode";
                    smItem.Enabled = false;

                    MenuItem sledItem = new MenuItem();
                    setItem.MenuItems.Add(sledItem);
                    sledItem.Text = "LED Time";
                    sledItem.Enabled = false;

                    senItem = new MenuItem();
                    setItem.MenuItems.Add(senItem);
                    senItem.Text = "Sensitivity";
                    senItem.Enabled = false;

                    calItem = new MenuItem();
                    setItem.MenuItems.Add(calItem);
                    calItem.Text = "Calibration";
                    calItem.Enabled = false;

                    tpItem = new MenuItem();
                    setItem.MenuItems.Add(tpItem);
                    tpItem.Text = "Trans. Power";
                    tpItem.Enabled = false;

                    srItem = new MenuItem();
                    setItem.MenuItems.Add(srItem);
                    srItem.Text = "Samp. Rate";
                    srItem.Enabled = false;

                    discItem = new MenuItem();
                    setItem.MenuItems.Add(discItem);
                    discItem.Text = "Discoverable";
                    discItem.Enabled = false;

                    tmItem = new MenuItem();
                    setItem.MenuItems.Add(tmItem);
                    tmItem.Text = "Trans. Mode";
                    tmItem.Enabled = false;

                    atItem = new MenuItem();
                    setItem.MenuItems.Add(atItem);
                    atItem.Text = "Alive Timer";
                    atItem.Enabled = false;

                    pdtItem = new MenuItem();
                    setItem.MenuItems.Add(pdtItem);
                    pdtItem.Text = "Pwr Dwn Timer";
                    pdtItem.Enabled = false;

                    ctItem = new MenuItem();
                    setItem.MenuItems.Add(ctItem);
                    ctItem.Text = "Conf. Timer";
                    ctItem.Enabled = false;

                    brItem = new MenuItem();
                    setItem.MenuItems.Add(brItem);
                    brItem.Text = "Baud Rate";
                    brItem.Enabled = false;


                }
            }

            //Annotation Menu
            this.menuItem16.Text = "Start";
            this.menuItem16.Click += new EventHandler(this.startStopButton_Click);            
            





            //prepare common PC and Pocket PC widgets

            // 
            // label3
            // 
            this.label3.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label3.Location = new System.Drawing.Point(53, 2);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(50, 13);
            this.label3.Text = "0:00:00";

            this.label3b.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label3b.Location = new System.Drawing.Point(53, 2);
            this.label3b.Name = "label3b";
            this.label3b.Size = new System.Drawing.Size(50, 13);
            this.label3b.Text = "0:00:00";  

            // 
            // label2
            // 
            this.label2.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label2.Location = new System.Drawing.Point(45, 2);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(13, 13);
            this.label2.Text = "/";

            this.label2b.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label2b.Location = new System.Drawing.Point(45, 2);
            this.label2b.Name = "label2b";
            this.label2b.Size = new System.Drawing.Size(13, 13);
            this.label2b.Text = "/";

            // 
            // label1
            // 
            this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label1.ForeColor = System.Drawing.Color.Green;
            this.label1.Location = new System.Drawing.Point(2, 2);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(50, 13);
            this.label1.Text = "0:00:00";

            this.label1b.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold);
            this.label1b.ForeColor = System.Drawing.Color.Green;
            this.label1b.Location = new System.Drawing.Point(2, 2);
            this.label1b.Name = "label1b";
            this.label1b.Size = new System.Drawing.Size(50, 13);
            this.label1b.Text = "0:00:00";

            ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).BackColor = panelColor;
            ((Panel)this.panels[VISUALIZE_PANEL]).Visible = true;


           

            // 
            // readDataTimer
            // 
            this.readDataTimer.Enabled = true;
            this.readDataTimer.Interval = 30;
            this.readDataTimer.Tick += new System.EventHandler(this.readDataTimer_Tick);
            // 
            // WocketsForm
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


            ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Controls.Add(this.label3b);
            ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Controls.Add(this.label2b);
            ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Controls.Add(this.label1b);


            ((Panel)this.panels[ANNOTATE_LIST_PANEL]).Controls.Add(this.label3);
            ((Panel)this.panels[ANNOTATE_LIST_PANEL]).Controls.Add(this.label2);
            ((Panel)this.panels[ANNOTATE_LIST_PANEL]).Controls.Add(this.label1);


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

   

            //((Panel)this.panels[CLASSIFIER_LABEL_PANEL]).Controls.Add(this.label8);
            //((Panel)this.panels[CLASSIFIER_LABEL_PANEL]).Controls.Add(this.label7);
            //((Panel)this.panels[CLASSIFIER_LABEL_PANEL]).Controls.Add(this.label9);

            this.SampLabels = new Label[this.wocketsController._Sensors.Count];

            Label cur = new Label();
            cur.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Regular);
            cur.Text = "Samp/sec, #Disconnects, Time Disconnect";
            cur.Location = new Point(5, 16);
            cur.Size = new Size(500, 50);
            ((Panel)this.panels[QUALITY_PANEL]).Controls.Add(cur);
            for (int i = 0; i < this.wocketsController._Sensors.Count; i++)
            {
                cur = new Label();
                cur.Font = new System.Drawing.Font("Tahoma", 10F, System.Drawing.FontStyle.Regular);
                cur.Text = "Sensor "+this.wocketsController._Sensors[i]._ID+": ?, ?, ?";
                cur.Location = new Point(16, 66 + i * 30);
                cur.Size = new Size(500, 40);
                this.SampLabels[i] = cur;
                ((Panel)this.panels[QUALITY_PANEL]).Controls.Add(cur);
                cur.BringToFront();
            }



            foreach(Panel p in this.panels.Values)
                this.Controls.Add(p);

            this.Menu = this.mainMenuPanel1;


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


            foreach(Panel p in this.panels.Values)
            {
                p.Width = this.ClientSize.Width;
                p.Height = this.ClientSize.Height; 
            }


            //Intialize Labels 40% of the screen
            this.sensorLabels = new Hashtable();
            this.sensorStatus = new Hashtable();
            this.sensorBattery = new Hashtable();
            int num_rows = (int)((this.wocketsController._Sensors.Count + 2) / 2); //additional row for HR and total sampling rate
            int textBoxHeight = ((int)(0.35 * ((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Height) - ((this.wocketsController._Sensors.Count - 1) * Constants.WIDGET_SPACING)) / num_rows;
            int textBoxWidth = (( ((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Width - (3 * Constants.WIDGET_SPACING)) / 3);
            int currentTextY = (int)( ((Panel)this.panels[VISUALIZE_PANEL]).ClientSize.Height * 0.60);
            int leftTextX = Constants.WIDGET_SPACING+32;
            int rightTextX = ((Constants.WIDGET_SPACING+32) * 2) + textBoxWidth;
            int currentTextX = Constants.WIDGET_SPACING+32;

            Font textFont;
            if (isPocketPC)
            {
                this.button1.Enabled = false;
                this.button1.Visible = false;
                this.button1.Width = textBoxWidth;
                this.button1.Height = textBoxHeight;
                textFont = this.button1.Font =
                    GUIHelper.CalculateBestFitFont(this.button1.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.button1.Size, "textBoxAC11", this.button1.Font, (float)0.9, (float)0.9);
            }
            else
            {
                this.label111.Enabled = false;
                this.label111.Visible = false;
                this.label111.Width = textBoxWidth;
                this.label111.Height = textBoxHeight;
                System.Windows.Forms.Form form = new System.Windows.Forms.Form();
                form.Size = label111.Size;
                textFont = this.label111.Font =
                    GUIHelper.CalculateBestFitFont(form.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.label111.Size, "textBoxAC11", this.label111.Font, (float)0.9, (float)0.9);
            }
            connectedWocketImage = (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "connected.gif");
            disconnectedWocketImage = (Image)new Bitmap(Constants.NETWORK_STATUS_DIRECTORY + "disconnected.gif");

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
                p2.Location = new System.Drawing.Point(currentTextX + 80, currentTextY+5);
                if (this.wocketsController._Sensors[i]._Receiver._Type == ReceiverTypes.HTCDiamond)
                    t.Text = "Intrnl";
                else
                {
                    string address = ((Wockets.Receivers.RFCOMMReceiver)((Wockets.Sensors.Accelerometers.Wocket)(this.wocketsController._Sensors[i]))._Receiver)._Address;
                    t.Text = "W" + address.Substring(address.Length - 2, 2);
                }
                t.Name = "W" + this.wocketsController._Sensors[i]._ID;
                t.Size = new System.Drawing.Size(textBoxWidth, 32);
                t.Location = new System.Drawing.Point(currentTextX, currentTextY);
                t.Font = textFont;
                this.sensorLabels.Add("W" + this.wocketsController._Sensors[i]._ID, t);
                this.sensorStatus.Add("W" + this.wocketsController._Sensors[i]._ID, p);
                this.sensorBattery.Add("W" + this.wocketsController._Sensors[i]._ID, p2);

                ((Panel)this.panels[VISUALIZE_PANEL]).Controls.Add(t);
                ((Panel)this.panels[VISUALIZE_PANEL]).Controls.Add(p);
                ((Panel)this.panels[VISUALIZE_PANEL]).Controls.Add(p2);
                p2.BringToFront();
                if (currentTextX == leftTextX)
                    currentTextX = rightTextX;
                else
                {
                    currentTextX = leftTextX;
                    currentTextY += (textBoxHeight + Constants.WIDGET_SPACING);
                }
            }


            #region graphical Annotation

            ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).AutoScroll = true;
           
            int max_buttons_per_row = 4;
            int act_button_width = 0;
            int act_button_height = 0;
            int numberOfButtons = 0;
            float fontSize = 7F;
            int act_button_x = 0;
            int act_button_y = 0;
            int marginHeight = 20;

            int screenWidth = ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Width;
            int screenHeight = ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Height;
            int scrollbarWidth = 28;

          
            for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists.Count); i++)
            {
                Activity[] acts = this.annotatedSession.OverlappingActivityLists[i].ToArray();
                if (isPocketPC)
                {
                    System.Windows.Forms.Button[] buttons = new System.Windows.Forms.Button[acts.Length];

                    for (int j = 0; j < buttons.Length; j++)
                    {
                        buttons[j] = new System.Windows.Forms.Button();
                        MakeButtonMultiline(buttons[j]);
                        buttons[j].Name = i+"_" +j;
                        buttons[j].Text = truncateText(acts[j]._Name);
                        buttons[j].Click += new EventHandler(this.activityButton_Click);
                        //      buttons[j].Font = new System.Drawing.Font("Microsoft Sans Serif", fontSize, System.Drawing.FontStyle.Regular);
                        buttons[j].BackColor = Color.SkyBlue;
                        numberOfButtons += 1;
                    }
                    activityButtons.Add(buttons);
                }
                else
                {
                    System.Windows.Forms.Label[] labels = new System.Windows.Forms.Label[acts.Length];
                    for (int j = 0; j < labels.Length; j++)
                    {
                        labels[j] = new System.Windows.Forms.Label();
                        MakeLabelMultiline(labels[j]);
                        labels[j].Name = this.annotatedSession.OverlappingActivityLists[i]._Name + "_" + acts[j]._Name;
                        labels[j].Text = truncateText(acts[j]._Name);
                        labels[j].Click += new EventHandler(this.activityButton_Click);
                        //      labels[j].Font = new System.Drawing.Font("Microsoft Sans Serif", fontSize, System.Drawing.FontStyle.Regular);
                        labels[j].BackColor = Color.SkyBlue;
                        numberOfButtons += 1;
                    }
                    activityButtons.Add(labels);
                }

            }

            if (numberOfButtons > 12)
            {
                screenWidth -= scrollbarWidth;
                act_button_width = act_button_height = screenWidth / max_buttons_per_row;
            }
            else if ((numberOfButtons <= 12) && (numberOfButtons > 8))
            {
                act_button_width = screenWidth / max_buttons_per_row;
                act_button_height = act_button_width+(act_button_width / 3);
            }
            else if ((numberOfButtons <= 8) && (numberOfButtons > 3))
            {
                int dBlockSize = (screenWidth-2) / max_buttons_per_row;
                max_buttons_per_row = 2;
                act_button_width = dBlockSize * 2;
                int s = (int)Math.Ceiling(numberOfButtons / 2.0);
                act_button_height =  ((dBlockSize * 4) + 22) / s;
                fontSize = 12F;
            }
            else
            {
                int dBlockSize = screenWidth / max_buttons_per_row;
                max_buttons_per_row = 1;
                act_button_width = screenWidth-2;
                act_button_height = (dBlockSize*4) / numberOfButtons;
                fontSize = 14F;
            }

            if (isPocketPC)
            {
                for (int i = 0; i < activityButtons.Count; i++)
                {
                    System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                    int buttonsOnRow = 0;
                    for (int j = 0; j < activityList.Length; j++)
                    {

                        activityList[j].Visible = true;
                        activityList[j].Width = act_button_width;
                        activityList[j].Height = act_button_height;
                        activityList[j].Location = new System.Drawing.Point(act_button_x, act_button_y);
                        activityList[j].Font = new System.Drawing.Font("Microsoft Sans Serif", fontSize, System.Drawing.FontStyle.Regular);
                        ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Controls.Add(activityList[j]);
                        buttonsOnRow += 1;

                        if (buttonsOnRow == activityList.Length) //completed a category
                        {
                            act_button_x = 0;
                            act_button_y += act_button_height + marginHeight;
                            buttonsOnRow = 0;
                        }
                        else if (buttonsOnRow == max_buttons_per_row) //completed a row within a category
                        {
                            act_button_x = 0;
                            act_button_y += act_button_height;
                            buttonsOnRow = 0;
                        }
                        else //added a button within a row
                            act_button_x += act_button_width;
                    }

                }
            }
            else
            {
                for (int i = 0; i < activityButtons.Count; i++)
                {
                    System.Windows.Forms.Label[] activityList = (System.Windows.Forms.Label[])activityButtons[i];
                    int buttonsOnRow = 0;
                    for (int j = 0; j < activityList.Length; j++)
                    {

                        activityList[j].Visible = true;
                        activityList[j].Width = act_button_width;
                        activityList[j].Height = act_button_height;
                        activityList[j].Location = new System.Drawing.Point(act_button_x, act_button_y);
                        activityList[j].Font = new System.Drawing.Font("Microsoft Sans Serif", fontSize, System.Drawing.FontStyle.Regular);
                        ((Panel)this.panels[BUTTON_ANNOTATION_PANEL]).Controls.Add(activityList[j]);
                        buttonsOnRow += 1;

                        if (buttonsOnRow == activityList.Length) //completed a category
                        {
                            act_button_x = 0;
                            act_button_y += act_button_height + marginHeight;
                            buttonsOnRow = 0;
                        }
                        else if (buttonsOnRow == max_buttons_per_row) //completed a row within a category
                        {
                            act_button_x = 0;
                            act_button_y += act_button_height;
                            buttonsOnRow = 0;
                        }
                        else //added a button within a row
                            act_button_x += act_button_width;
                    }
                }
            }



            #endregion graphical Annotation


            //Initialize Buttons

            this.categoryDrops = new ArrayList();
            this.buttonIndex = new ArrayList();
            int button_width = ((Panel)this.panels[ANNOTATE_LIST_PANEL]).ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
            int button_height = (((Panel)this.panels[ANNOTATE_LIST_PANEL]).ClientSize.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - (this.annotatedSession.OverlappingActivityLists.Count * Constants.WIDGET_SPACING)) / (this.annotatedSession.OverlappingActivityLists.Count + 1);
            int button_x = Constants.WIDGET_SPACING;
            int button_y = Constants.WIDGET_SPACING * 2;
            int delta_y = button_height + Constants.WIDGET_SPACING;
            int button_id = 0;


            if (isPocketPC)
            {
                for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists.Count); i++)
                {

                    ActivityList category = this.annotatedSession.OverlappingActivityLists[0];
                    System.Windows.Forms.Button button = new System.Windows.Forms.Button();
                    System.Windows.Forms.ComboBox combo = new System.Windows.Forms.ComboBox();
                    button.Location = new System.Drawing.Point(button_x, button_y + button_id * delta_y);
                    combo.Location = new System.Drawing.Point(button_x, button_y + 37 + button_id * delta_y);
                    button.Name = button_id.ToString();
                    combo.Name = button_id.ToString();
                    button.Size = new System.Drawing.Size(button_width, button_height);
                    combo.Size = new System.Drawing.Size(button_width, button_height);
                    button.Text = category[0]._Name;
                    foreach (Activity cat in category)
                        combo.Items.Add(cat._Name);
                    combo.SelectedItem = combo.Items[0];
                    this.categoryDrops.Add(combo);
                    ((Panel)this.panels[ANNOTATE_LIST_PANEL]).Controls.Add(combo);

                    //check the longest label for this button
                    for (int j = 0; (j < category.Count); j++)
                    {
                        string newlabel = category[j]._Name;//label.Name;

                        if (newlabel.Length > longest_label.Length)
                            longest_label = newlabel;
                    }
                    this.buttonIndex.Add(0);
                    button_id++;
                }
            }
            else
            {
                for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists.Count); i++)
                {

                    ActivityList category = this.annotatedSession.OverlappingActivityLists[0];
                    System.Windows.Forms.Label label = new System.Windows.Forms.Label();
                    System.Windows.Forms.ComboBox combo = new System.Windows.Forms.ComboBox();
                    label.Location = new System.Drawing.Point(button_x, button_y + button_id * delta_y);
                    combo.Location = new System.Drawing.Point(button_x, button_y + 37 + button_id * delta_y);
                    label.Name = button_id.ToString();
                    combo.Name = button_id.ToString();
                    label.Size = new System.Drawing.Size(button_width, button_height);
                    combo.Size = new System.Drawing.Size(button_width, button_height);
                    label.Text = category[0]._Name;
                    foreach (Activity cat in category)
                        combo.Items.Add(cat._Name);
                    combo.SelectedItem = combo.Items[0];
                    this.categoryDrops.Add(combo);
                    ((Panel)this.panels[ANNOTATE_LIST_PANEL]).Controls.Add(combo);

                    //check the longest label for this button
                    for (int j = 0; (j < category.Count); j++)
                    {
                        string newlabel = category[j]._Name;//label.Name;

                        if (newlabel.Length > longest_label.Length)
                            longest_label = newlabel;
                    }
                    this.buttonIndex.Add(0);
                    button_id++;
                }
            }

            if (longest_label.Length < 5)
                longest_label = "RESET";

    
 
            button_width = (((Panel)this.panels[ANNOTATE_LIST_PANEL]).Size.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 2;
            this.Menu = this.mainMenu1;
            this.ClientSize = new Size(240, 265);

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

               isQuitting = true;

        }

        private const int BS_MULTILINE = 0x00002000;
        private const int GWL_STYLE = -16;

        [System.Runtime.InteropServices.DllImport("coredll")]
        private static extern int GetWindowLong(IntPtr hWnd, int nIndex);

        [System.Runtime.InteropServices.DllImport("coredll")]
        private static extern int SetWindowLong(IntPtr hWnd, int nIndex, int dwNewLong);

        public static void MakeButtonMultiline(Button b)
        {
            IntPtr hwnd = b.Handle;
            int currentStyle = GetWindowLong(hwnd, GWL_STYLE);
            int newStyle = SetWindowLong(hwnd, GWL_STYLE, currentStyle | BS_MULTILINE);
        }

        public static void MakeLabelMultiline(Label b)
        {
            IntPtr hwnd = b.Handle;
            int currentStyle = GetWindowLong(hwnd, GWL_STYLE);
            int newStyle = SetWindowLong(hwnd, GWL_STYLE, currentStyle | BS_MULTILINE);
        }

        private String truncateText(String text)
        {
           
            int maxChars = 10;

            if (text.Length <= maxChars)
                return text;

            char[] delimiter ={ ' ', '-', '/' };
            String[] tokens = text.Split(delimiter);

            if (tokens.Length == 1)
                return text;

            String final = "";
            String currentLine = "";


            foreach (String part in tokens)
            {
                String temp = part;
                if (temp.StartsWith("(") && temp.EndsWith(")")) temp = temp.Substring(1, temp.Length - 2);
                else if (temp.StartsWith("(")) temp = temp.Remove(0, 1);
                else if (temp.EndsWith(")")) temp = temp.Substring(0, temp.Length - 1);

                if (temp.Equals("with")) temp = "w/";
                else if (temp.Equals("without")) temp = "w/o";
                else if (temp.Equals("morning")) temp = "AM";
                else if (temp.Equals("night")) temp = "PM";
                else if (temp.Equals("a")) temp = "";

                if ((currentLine.Length + temp.Length) >= maxChars)
                {
                    final += currentLine + " \n";
                    currentLine = "";
                }

                currentLine += temp + " ";
            }
            final += currentLine;

            return final;
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
            if (isPocketPC)
                this.button1 = new System.Windows.Forms.Button();
            else
                this.label111 = new System.Windows.Forms.Label();
            this.SuspendLayout();


            if (isPocketPC)
            {            
                // 
                // button1
                // 
                this.button1.Location = new System.Drawing.Point(17, 80);
                this.button1.Name = "button1";
                this.button1.Size = new System.Drawing.Size(72, 20);
                this.button1.TabIndex = 0;
                this.button1.Text = "button1";
            }
            else
            {
                // 
                // label111
                // 
                this.label111.Location = new System.Drawing.Point(17, 80);
                this.label111.Name = "label111";
                this.label111.Size = new System.Drawing.Size(72, 20);
                this.label111.TabIndex = 0;
                this.label111.Text = "label111";
            }


            // 
            // WocketsForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.Controls.Add(this.button1);
            this.KeyPreview = true;
            this.Menu = this.mainMenuPanel1;
            this.Name = "DataLoggerForm";
            this.Text = "Collect Data...";
            this.ResumeLayout(false);

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
        private System.Windows.Forms.MenuItem menuItem21;
        private System.Windows.Forms.MenuItem menuItem22;
        private System.Windows.Forms.MenuItem menuItem23;
        private System.Windows.Forms.MenuItem menuItem24;
        private System.Windows.Forms.MenuItem menuItem25;
        private System.Windows.Forms.Timer readDataTimer;
        private System.Windows.Forms.Label label3, label3b;
        private System.Windows.Forms.Label label2, label2b;
        private System.Windows.Forms.Label label1, label1b;
        private System.Windows.Forms.Label label6;
        private System.Windows.Forms.Label label8;
        private System.Windows.Forms.Label label7;
        private System.Windows.Forms.Label label9;
        private System.Windows.Forms.TextBox CommandBox;
        private System.Windows.Forms.Timer qualityTimer;
        private System.Windows.Forms.Label label111;

#if (PocketPC)
        private System.Windows.Forms.Button button1;
#endif

        private Color defaultColor, panelColor, clickColor;



    }
}