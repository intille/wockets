using System;
using System.Drawing;
using System.Windows.Forms;
using System.IO;
using System.Threading;
using Wockets;
using Wockets.Data.Annotation;
using WocketsApplication.Utils;
using WocketsApplication.Utils.Forms.FileBrowser;



namespace WocketsApplication
{
    partial class WocketsForm
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


        }

        #endregion

        #region Interface Functions Wockets Form
        private void InitializeInterface()
        {

            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.dataLoggerButton = new System.Windows.Forms.Button();
            this.activityTrackerButton = new System.Windows.Forms.Button();
            this.calibratorButton = new System.Windows.Forms.Button();
            this.FontSizeButton = new System.Windows.Forms.Button();
            this.SuspendLayout();

            // 
            // FontSizeButton
            // 
            this.FontSizeButton.Location = new System.Drawing.Point(3, 3);
            this.FontSizeButton.Name = "FontSizeButton";
            this.FontSizeButton.Size = new System.Drawing.Size(108, 20);
            this.FontSizeButton.TabIndex = 0;
            this.FontSizeButton.Text = "Activity Tracker";
            this.FontSizeButton.Visible = false;


            // 
            // WocketsForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.Controls.Add(this.calibratorButton);
            this.Controls.Add(this.activityTrackerButton);
            this.Controls.Add(this.dataLoggerButton);
            this.Controls.Add(this.FontSizeButton);
            this.Menu = this.mainMenu1;
            this.Name = "WocketsForm";
            this.Text = "Wockets Software";
            this.Resize += new System.EventHandler(WocketsForm_Resize);
            this.ResumeLayout(false);

        }

        void WocketsForm_Resize(object sender, System.EventArgs e)
        {
            int num_widgets = 3;
            //Dynamically adjust components based on screen size
            //Set form size
            this.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
            if (this.Width > Constants.MAX_FORM_WIDTH)
                this.Width = Constants.MAX_FORM_WIDTH;
            this.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
            if (this.Height > Constants.MAX_FORM_HEIGHT)
                this.Height = Constants.MAX_FORM_HEIGHT;


            int buttonHeight = (this.ClientSize.Height - ((num_widgets + 1) * Constants.WIDGET_SPACING)) / num_widgets;
            int buttonWidth = this.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;

            // 
            // dataLoggerButton
            // 
            this.dataLoggerButton.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
            this.dataLoggerButton.Name = "dataLoggerButton";
            this.dataLoggerButton.Size = new System.Drawing.Size(buttonWidth, buttonHeight);
            this.dataLoggerButton.TabIndex = 0;
            this.dataLoggerButton.Text = "Data Logger";
            this.dataLoggerButton.Click += new System.EventHandler(dataLoggerButton_Click);

            // 
            // activityTrackerButton
            // 
            this.activityTrackerButton.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + this.dataLoggerButton.Location.Y + this.dataLoggerButton.Height);
            this.activityTrackerButton.Name = "activityTrackerButton";
            this.activityTrackerButton.Size = new System.Drawing.Size(buttonWidth, buttonHeight);
            this.activityTrackerButton.TabIndex = 1;
            this.activityTrackerButton.Text = "Activity Tracker";
            this.activityTrackerButton.Click += new EventHandler(activityTrackerButton_Click);
            // 
            // calibratorButton
            // 
            this.calibratorButton.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + this.activityTrackerButton.Location.Y + this.activityTrackerButton.Height);
            this.calibratorButton.Name = "calibratorButton";
            this.calibratorButton.Size = new System.Drawing.Size(buttonWidth, buttonHeight);
            this.calibratorButton.TabIndex = 2;
            this.calibratorButton.Text = "Calibrate";
            this.calibratorButton.Click += new EventHandler(calibratorButton_Click);

            //Resize the fonts relative to the size of the FontSizeButton
            this.dataLoggerButton.Font = this.activityTrackerButton.Font =
              this.calibratorButton.Font = GUIHelper.CalculateBestFitFont(this.FontSizeButton.Parent.CreateGraphics(), Constants.MIN_FONT,
                 Constants.MAX_FONT, this.dataLoggerButton.Size, "Activity Tracker", this.FontSizeButton.Font, (float)0.9, (float)0.9);
        }


        #region Sensor Calibration Form
        private System.Windows.Forms.Form cForm;
        private System.Windows.Forms.MainMenu cFormMainMenu;
        private System.Windows.Forms.Label cFormLabel;
        private System.Windows.Forms.ListBox cFormListbox;
        private System.Windows.Forms.Button cFormNextButton;
        private System.Windows.Forms.Button cFormBackButton;
        void calibratorButton_Click(object sender, EventArgs e)
        {
            string longest_label = "";
            if (this.cForm == null)
            {
                this.cForm = new System.Windows.Forms.Form();
                this.cFormMainMenu = new System.Windows.Forms.MainMenu();
                this.cFormListbox = new System.Windows.Forms.ListBox();
                this.cFormLabel = new System.Windows.Forms.Label();
                this.cFormNextButton = new System.Windows.Forms.Button();
                this.cFormBackButton = new System.Windows.Forms.Button();
                this.cForm.SuspendLayout();
                // 
                // cFormListbox
                // 
                this.cFormListbox.Location = new System.Drawing.Point(72, 44);
                this.cFormListbox.Name = "cFormListbox";
                this.cFormListbox.Size = new System.Drawing.Size(100, 100);
                this.cFormListbox.TabIndex = 0;
                this.cFormListbox.SelectedIndexChanged += new System.EventHandler(cFormListbox_SelectedIndexChanged);
                // 
                // cForm
                // 
                this.cFormLabel.Location = new System.Drawing.Point(15, 9);
                this.cFormLabel.Name = "chooseWocketControllerLabel";
                this.cFormLabel.Size = new System.Drawing.Size(182, 23);
                this.cFormLabel.Text = "Choose a wocket configuration:";
                // 
                // cFormNextButton
                // 
                this.cFormNextButton.Location = new System.Drawing.Point(143, 176);
                this.cFormNextButton.Name = "cFormNextButton";
                this.cFormNextButton.Size = new System.Drawing.Size(72, 20);
                this.cFormNextButton.TabIndex = 2;
                this.cFormNextButton.Text = "Next";
                this.cFormNextButton.Click += new System.EventHandler(cFormNextButton_Click);
                // 
                // cFormBackButton
                // 
                this.cFormBackButton.Location = new System.Drawing.Point(31, 176);
                this.cFormBackButton.Name = "cFormBackButton";
                this.cFormBackButton.Size = new System.Drawing.Size(72, 20);
                this.cFormBackButton.TabIndex = 3;
                this.cFormBackButton.Text = "Back";
                this.cFormBackButton.Click += new System.EventHandler(cFormBackButton_Click);
                // 
                // aForm
                // 
                this.cForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.cForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.cForm.AutoScroll = false;
                this.cForm.ClientSize = new System.Drawing.Size(240, 268);
                this.cForm.Controls.Add(this.cFormBackButton);
                this.cForm.Controls.Add(this.cFormNextButton);
                this.cForm.Controls.Add(this.cFormLabel);
                this.cForm.Controls.Add(this.cFormListbox);
                this.cForm.Menu = this.mainMenu1;
                this.cForm.Name = "cForm";
                this.cForm.Text = "Wocket Configurations";
                this.cForm.ResumeLayout(false);


                this.cForm.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
                if (this.cForm.Width > Constants.MAX_FORM_WIDTH)
                    this.cForm.Width = Constants.MAX_FORM_WIDTH;
                this.cForm.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
                if (this.cForm.Height > Constants.MAX_FORM_HEIGHT)
                    this.cForm.Height = Constants.MAX_FORM_HEIGHT;


                double drawableWidth = this.cForm.Width;
                double drawableHeight = this.cForm.Height - 4 * Constants.WIDGET_SPACING;

                //adjust top label size and location
                this.cFormLabel.Width = (int)drawableWidth;
                this.cFormLabel.Height = (int)(drawableHeight * 0.15);
                this.cFormLabel.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
                this.cFormLabel.Font = GUIHelper.CalculateBestFitFont(this.cFormLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.cForm.Size, this.cFormLabel.Text, this.cForm.Font, (float)0.9, (float)0.9);

                this.wocketsControllers = new WocketsControllerList();
                this.wocketsControllers.FromXML(Constants.MASTER_DIRECTORY);
                for (int i = 0; (i < this.wocketsControllers.Count); i++)
                {
                    this.cFormListbox.Items.Add(this.wocketsControllers[i]._Name);
                    if (longest_label.Length < this.wocketsControllers[i]._Name.Length)
                        longest_label = this.wocketsControllers[i]._Name;
                }

                //Listbox dynamic placement
                this.cFormListbox.Width = (int)(drawableWidth * 0.90);
                this.cFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.cFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.cFormListbox.Size, longest_label, this.cFormListbox.Font, (float)0.9, (float)0.9);
                this.cFormListbox.Font = new Font(Constants.FONT_FAMILY, newFont.Size, this.Font.Style);
                this.cFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.cFormLabel.Location.Y + this.cFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.cFormNextButton.Width = (int)(drawableWidth * 0.45);
                this.cFormBackButton.Width = (int)(drawableWidth * 0.45);
                this.cFormNextButton.Height = (int)(drawableHeight * 0.20);
                this.cFormBackButton.Height = (int)(drawableHeight * 0.20);

                this.cFormBackButton.Location = new Point(Constants.WIDGET_SPACING, (int)(this.cFormListbox.Location.Y + this.cFormListbox.Height + Constants.WIDGET_SPACING));
                this.cFormNextButton.Location = new Point((int)(this.cFormNextButton.Width + Constants.WIDGET_SPACING),
                    (int)(this.cFormListbox.Location.Y + this.cFormListbox.Height + Constants.WIDGET_SPACING));
                this.cFormBackButton.Font = this.cFormNextButton.Font = GUIHelper.CalculateBestFitFont(this.cFormNextButton.Parent.CreateGraphics(), Constants.MIN_FONT,
                    Constants.MAX_FONT, this.cFormNextButton.Size, "Next", this.cFormNextButton.Font, (float)0.9, (float)0.9);
                this.cFormNextButton.Enabled = false;

            }

            if (cForm.Visible == false)
                cForm.Show();
        }

        void cFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            selectedWocketController = this.cFormListbox.SelectedIndex;
            if (this.cFormNextButton.Enabled == false)
                this.cFormNextButton.Enabled = true;
        }

        void cFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.cForm.Visible = false;

        }


        void cFormNextButton_Click(object sender, System.EventArgs e)
        {
            try
            {
                InitializeCalibrator();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Error: " + ex.Message);
                Application.Exit();
            }
        }

        #endregion Sensor Calibration Form

        void activityTrackerButton_Click(object sender, EventArgs e)
        {
            if (this.lForm == null)
            {

                this.lForm = new System.Windows.Forms.Form();
                this.lFormMainMenu = new System.Windows.Forms.MainMenu();
                this.lFormLabel = new System.Windows.Forms.Label();
                this.lFormTextBox = new System.Windows.Forms.TextBox();
                this.lFormBrowseButton = new System.Windows.Forms.Button();
                this.lFormNextButton = new System.Windows.Forms.Button();
                this.lFormBackButton = new System.Windows.Forms.Button();

                // 
                // lFormLabel
                // 
                this.lFormLabel.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
                this.lFormLabel.Location = new System.Drawing.Point(16, 23);
                this.lFormLabel.Name = "label1";
                this.lFormLabel.Size = new System.Drawing.Size(199, 32);
                this.lFormLabel.TabIndex = 5;
                this.lFormLabel.Text = "Where do you want to store your data?";
                // 
                // lFormTextBox
                // 
                this.lFormTextBox.Enabled = false;
                this.lFormTextBox.Location = new System.Drawing.Point(16, 70);
                this.lFormTextBox.Name = "lFormTextBox";
                this.lFormTextBox.Size = new System.Drawing.Size(199, 20);
                this.lFormTextBox.TabIndex = 1;
                // 
                // lFormBrowseButton
                // 
                this.lFormBrowseButton.Location = new System.Drawing.Point(16, 97);
                this.lFormBrowseButton.Name = "lFormBrowseButton";
                this.lFormBrowseButton.Size = new System.Drawing.Size(199, 20);
                this.lFormBrowseButton.TabIndex = 2;
                this.lFormBrowseButton.Text = "Choose a directory";
                this.lFormBrowseButton.Click += new System.EventHandler(this.lFormClassisifierBrowseButton_Click);
                // 
                // lFormNextButton
                // 
                this.lFormNextButton.Enabled = false;
                this.lFormNextButton.Location = new System.Drawing.Point(143, 139);
                this.lFormNextButton.Name = "lFormNextButton";
                this.lFormNextButton.Size = new System.Drawing.Size(72, 20);
                this.lFormNextButton.TabIndex = 3;
                this.lFormNextButton.Text = "Next";
                this.lFormNextButton.Click += new System.EventHandler(this.lFormClassifierNextButton_Click);
                // 
                // lFormBackButton
                // 
                this.lFormBackButton.Location = new System.Drawing.Point(16, 139);
                this.lFormBackButton.Name = "lFormBackButton";
                this.lFormBackButton.Size = new System.Drawing.Size(72, 20);
                this.lFormBackButton.TabIndex = 4;
                this.lFormBackButton.Text = "Back";
                this.lFormBackButton.Click += new System.EventHandler(this.lFormBackButton_Click);
                // 
                // lForm
                // 
                this.lForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.lForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.lForm.AutoScroll = true;
                this.lForm.ClientSize = new System.Drawing.Size(240, 268);
                this.lForm.Controls.Add(this.lFormBrowseButton);
                this.lForm.Controls.Add(this.lFormNextButton);
                this.lForm.Controls.Add(this.lFormBackButton);
                this.lForm.Controls.Add(this.lFormTextBox);
                this.lForm.Controls.Add(this.lFormLabel);
                this.lForm.Menu = this.mainMenu1;
                this.lForm.Name = "WhereStoreDataForm";
                this.lForm.Text = "Collect Data...";
                this.lForm.ResumeLayout(false);



                this.lForm.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
                if (this.lForm.Width > Constants.MAX_FORM_WIDTH)
                    this.lForm.Width = Constants.MAX_FORM_WIDTH;
                this.lForm.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
                if (this.lForm.Height > Constants.MAX_FORM_HEIGHT)
                    this.lForm.Height = Constants.MAX_FORM_HEIGHT;


                int widgetHeight = (this.ClientSize.Height - (5 * Constants.WIDGET_SPACING)) / 4;
                int widgetWidth = (int)(this.lForm.ClientSize.Width - Constants.WIDGET_SPACING);

                widgetHeight = (int)(0.9 * widgetHeight);
                widgetWidth = (int)(0.9 * widgetWidth);

                //adjust top label size and location
                this.lFormLabel.Text = "Where do you want to store your data?";
                this.lFormLabel.Width = widgetWidth;
                this.lFormLabel.Height = widgetHeight;
                this.lFormLabel.Location = new Point((int)Constants.WIDGET_SPACING, (int)Constants.WIDGET_SPACING);
                this.lFormLabel.Font = GUIHelper.CalculateBestFitFont(this.lFormLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.lFormLabel.Size, this.lFormLabel.Text, this.lFormLabel.Font, (float)0.9, (float)0.9);

                //adjust textbox
                this.lFormTextBox.Width = widgetWidth;
                this.lFormTextBox.Height = widgetHeight;
                this.lFormTextBox.Location = new Point((int)Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + this.lFormLabel.Location.Y + this.lFormLabel.Height + Constants.WIDGET_SPACING);
                this.lFormTextBox.Font = this.lFormLabel.Font;

                this.lFormBrowseButton.Width = widgetWidth;
                this.lFormBrowseButton.Height = widgetHeight;
                this.lFormBrowseButton.Location = new Point((int)Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + this.lFormTextBox.Location.Y + this.lFormTextBox.Height + Constants.WIDGET_SPACING);
                this.lFormBrowseButton.Font = GUIHelper.CalculateBestFitFont(this.lFormBrowseButton.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.lFormBrowseButton.Size, this.lFormLabel.Text, this.lFormBrowseButton.Font, (float)0.9, (float)0.9);


                this.lFormNextButton.Width = (int)(widgetWidth * 0.50);
                this.lFormBackButton.Width = (int)(widgetWidth * 0.50);
                this.lFormNextButton.Height = (int)(widgetHeight * 1.0);
                this.lFormBackButton.Height = (int)(widgetHeight * 1.0);


                this.lFormBackButton.Location = new Point((int)Constants.WIDGET_SPACING, (int)(this.lFormBrowseButton.Location.Y + this.lFormBrowseButton.Height + Constants.WIDGET_SPACING));
                this.lFormNextButton.Location = new Point((int)(Constants.WIDGET_SPACING + this.lFormNextButton.Width + Constants.WIDGET_SPACING),
                    (int)(this.lFormBrowseButton.Location.Y + this.lFormBrowseButton.Height + Constants.WIDGET_SPACING));
                this.lFormNextButton.Font = this.lFormBackButton.Font = GUIHelper.CalculateBestFitFont(this.lFormNextButton.Parent.CreateGraphics(), Constants.MIN_FONT,
                    Constants.MAX_FONT, this.lFormNextButton.Size, "Next", this.lFormNextButton.Font, (float)0.9, (float)0.9);


            }

            if (lForm.Visible == false)
                lForm.Show();
        }

        #endregion Interface Functions Wockets Form

        #region Activity Protocols Form
        private System.Windows.Forms.Form aForm;
        private System.Windows.Forms.MainMenu aFormMainMenu;
        private System.Windows.Forms.Label aFormLabel;
        private System.Windows.Forms.ListBox aFormListbox;
        private System.Windows.Forms.Button aFormNextButton;
        private System.Windows.Forms.Button aFormBackButton;
        void dataLoggerButton_Click(object sender, System.EventArgs e)
        {
            if (this.aForm == null)
            {
                this.aForm = new System.Windows.Forms.Form();
                this.aFormMainMenu = new System.Windows.Forms.MainMenu();
                this.aFormListbox = new System.Windows.Forms.ListBox();
                this.aFormLabel = new System.Windows.Forms.Label();
                this.aFormNextButton = new System.Windows.Forms.Button();
                this.aFormBackButton = new System.Windows.Forms.Button();
                this.aForm.SuspendLayout();
                // 
                // aFormListbox
                // 
                this.aFormListbox.Location = new System.Drawing.Point(72, 44);
                this.aFormListbox.Name = "aFormListbox";
                this.aFormListbox.Size = new System.Drawing.Size(100, 100);
                this.aFormListbox.TabIndex = 0;
                this.aFormListbox.SelectedIndexChanged += new System.EventHandler(aFormListbox_SelectedIndexChanged);
                // 
                // chooseActivityProtocolLabel
                // 
                this.aFormLabel.Location = new System.Drawing.Point(15, 9);
                this.aFormLabel.Name = "chooseActivityProtocolLabel";
                this.aFormLabel.Size = new System.Drawing.Size(182, 23);
                this.aFormLabel.Text = "Choose an activity protocol:";
                // 
                // activityProtocolsNextButton
                // 
                this.aFormNextButton.Location = new System.Drawing.Point(143, 176);
                this.aFormNextButton.Name = "activityProtocolsNextButton";
                this.aFormNextButton.Size = new System.Drawing.Size(72, 20);
                this.aFormNextButton.TabIndex = 2;
                this.aFormNextButton.Text = "Next";
                this.aFormNextButton.Click += new System.EventHandler(aFormNextButton_Click);
                // 
                // activityProtocolsBackButton
                // 
                this.aFormBackButton.Location = new System.Drawing.Point(31, 176);
                this.aFormBackButton.Name = "activityProtocolsBackButton";
                this.aFormBackButton.Size = new System.Drawing.Size(72, 20);
                this.aFormBackButton.TabIndex = 3;
                this.aFormBackButton.Text = "Back";
                this.aFormBackButton.Click += new System.EventHandler(aFormBackButton_Click);
                // 
                // aForm
                // 
                this.aForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.aForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.aForm.AutoScroll = false;
                this.aForm.ClientSize = new System.Drawing.Size(240, 268);
                this.aForm.Controls.Add(this.aFormBackButton);
                this.aForm.Controls.Add(this.aFormNextButton);
                this.aForm.Controls.Add(this.aFormLabel);
                this.aForm.Controls.Add(this.aFormListbox);
                this.aForm.Menu = this.mainMenu1;
                this.aForm.Name = "aForm";
                this.aForm.Text = "Activity Protocols";
                this.aForm.ResumeLayout(false);


                this.aForm.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
                if (this.aForm.Width > Constants.MAX_FORM_WIDTH)
                    this.aForm.Width = Constants.MAX_FORM_WIDTH;
                this.aForm.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
                if (this.aForm.Height > Constants.MAX_FORM_HEIGHT)
                    this.aForm.Height = Constants.MAX_FORM_HEIGHT;


                double drawableWidth = this.aForm.Width;
                double drawableHeight = this.aForm.Height - 4 * Constants.WIDGET_SPACING;

                //adjust top label size and location
                this.aFormLabel.Width = (int)drawableWidth;
                this.aFormLabel.Height = (int)(drawableHeight * 0.15);
                this.aFormLabel.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
                this.aFormLabel.Font = GUIHelper.CalculateBestFitFont(this.aFormLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.aForm.Size, this.aFormLabel.Text, this.aForm.Font, (float)0.9, (float)0.9);

                //Load the activity protocols from the master directory
                this.aProtocols = new AnnotationProtocolList();
                this.aProtocols.FromXML(Constants.MASTER_DIRECTORY + "\\ActivityProtocols.xml");
                string longest_label = "";
                for (int i = 0; (i<this.aProtocols.Count); i++)
                {
                    this.aFormListbox.Items.Add(this.aProtocols[i]._Name);
                    if (longest_label.Length < this.aProtocols[i]._Name.Length)
                        longest_label = this.aProtocols[i]._Name;
                }

                //Listbox dynamic placement
                this.aFormListbox.Width = (int)(drawableWidth * 0.90);
                this.aFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.aFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.aFormListbox.Size, longest_label, this.aFormListbox.Font, (float)0.9, (float)0.9);
                this.aFormListbox.Font = new Font(Constants.FONT_FAMILY, newFont.Size, this.Font.Style);
                this.aFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.aFormLabel.Location.Y + this.aFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.aFormNextButton.Width = (int)(drawableWidth * 0.45);
                this.aFormBackButton.Width = (int)(drawableWidth * 0.45);
                this.aFormNextButton.Height = (int)(drawableHeight * 0.20);
                this.aFormBackButton.Height = (int)(drawableHeight * 0.20);

                this.aFormBackButton.Location = new Point(Constants.WIDGET_SPACING, (int)(this.aFormListbox.Location.Y + this.aFormListbox.Height + Constants.WIDGET_SPACING));
                this.aFormNextButton.Location = new Point((int)(this.aFormNextButton.Width + Constants.WIDGET_SPACING),
                    (int)(this.aFormListbox.Location.Y + this.aFormListbox.Height + Constants.WIDGET_SPACING));
                this.aFormBackButton.Font = this.aFormNextButton.Font = GUIHelper.CalculateBestFitFont(this.aFormNextButton.Parent.CreateGraphics(), Constants.MIN_FONT,
                    Constants.MAX_FONT, this.aFormNextButton.Size, "Next", this.aFormNextButton.Font, (float)0.9, (float)0.9);
                this.aFormNextButton.Enabled = false;

            }

            if (aForm.Visible == false)
                aForm.Show();
            this.Visible = false;
        }


        void aFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            this.selectedActivityProtocol=this.aFormListbox.SelectedIndex;          
            if (this.aFormNextButton.Enabled== false)
                this.aFormNextButton.Enabled= true;
        }

        void aFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.Visible = true;
            this.aForm.Visible = false;            
        }



        #endregion Activity Protocols Form

        #region Sensors Configuration Form
        
        private System.Windows.Forms.Form sForm;
        private System.Windows.Forms.MainMenu sFormMainMenu;
        private System.Windows.Forms.Label sFormLabel;
        private System.Windows.Forms.ListBox sFormListbox;
        private System.Windows.Forms.Button sFormNextButton;
        private System.Windows.Forms.Button sFormBackButton;

        void aFormNextButton_Click(object sender, System.EventArgs e)
        {
            string longest_label = "";
            if (this.sForm == null)
            {
                this.sForm = new System.Windows.Forms.Form();
                this.sFormMainMenu = new System.Windows.Forms.MainMenu();
                this.sFormListbox = new System.Windows.Forms.ListBox();
                this.sFormLabel = new System.Windows.Forms.Label();
                this.sFormNextButton = new System.Windows.Forms.Button();
                this.sFormBackButton = new System.Windows.Forms.Button();
                this.sForm.SuspendLayout();
                // 
                // sFormListbox
                // 
                this.sFormListbox.Location = new System.Drawing.Point(72, 44);
                this.sFormListbox.Name = "sFormListbox";
                this.sFormListbox.Size = new System.Drawing.Size(100, 100);
                this.sFormListbox.TabIndex = 0;
                this.sFormListbox.SelectedIndexChanged += new System.EventHandler(sFormListbox_SelectedIndexChanged);
                // 
                // sForm
                // 
                this.sFormLabel.Location = new System.Drawing.Point(15, 9);
                this.sFormLabel.Name = "chooseWocketControllerLabel";
                this.sFormLabel.Size = new System.Drawing.Size(182, 23);
                this.sFormLabel.Text = "Choose a wocket configuration:";
                // 
                // sFormNextButton
                // 
                this.sFormNextButton.Location = new System.Drawing.Point(143, 176);
                this.sFormNextButton.Name = "sFormNextButton";
                this.sFormNextButton.Size = new System.Drawing.Size(72, 20);
                this.sFormNextButton.TabIndex = 2;
                this.sFormNextButton.Text = "Next";
                this.sFormNextButton.Click += new System.EventHandler(sFormNextButton_Click);
                // 
                // sFormBackButton
                // 
                this.sFormBackButton.Location = new System.Drawing.Point(31, 176);
                this.sFormBackButton.Name = "sFormBackButton";
                this.sFormBackButton.Size = new System.Drawing.Size(72, 20);
                this.sFormBackButton.TabIndex = 3;
                this.sFormBackButton.Text = "Back";
                this.sFormBackButton.Click += new System.EventHandler(sFormBackButton_Click);
                // 
                // aForm
                // 
                this.sForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.sForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.sForm.AutoScroll = false;
                this.sForm.ClientSize = new System.Drawing.Size(240, 268);
                this.sForm.Controls.Add(this.sFormBackButton);
                this.sForm.Controls.Add(this.sFormNextButton);
                this.sForm.Controls.Add(this.sFormLabel);
                this.sForm.Controls.Add(this.sFormListbox);
                this.sForm.Menu = this.mainMenu1;
                this.sForm.Name = "sForm";
                this.sForm.Text = "Wocket Configurations";
                this.sForm.ResumeLayout(false);


                this.sForm.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
                if (this.sForm.Width > Constants.MAX_FORM_WIDTH)
                    this.sForm.Width = Constants.MAX_FORM_WIDTH;
                this.sForm.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
                if (this.sForm.Height > Constants.MAX_FORM_HEIGHT)
                    this.sForm.Height = Constants.MAX_FORM_HEIGHT;


                double drawableWidth = this.sForm.Width;
                double drawableHeight = this.sForm.Height - 4 * Constants.WIDGET_SPACING;

                //adjust top label size and location
                this.sFormLabel.Width = (int)drawableWidth;
                this.sFormLabel.Height = (int)(drawableHeight * 0.15);
                this.sFormLabel.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
                this.sFormLabel.Font = GUIHelper.CalculateBestFitFont(this.sFormLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.sForm.Size, this.sFormLabel.Text, this.sForm.Font, (float)0.9, (float)0.9);

                this.wocketsControllers = new WocketsControllerList();
                this.wocketsControllers.FromXML(Constants.MASTER_DIRECTORY);
                for (int i = 0; (i < this.wocketsControllers.Count); i++)
                {
                    this.sFormListbox.Items.Add(this.wocketsControllers[i]._Name);
                    if (longest_label.Length < this.wocketsControllers[i]._Name.Length)
                        longest_label = this.wocketsControllers[i]._Name;
                }

                //Listbox dynamic placement
                this.sFormListbox.Width = (int)(drawableWidth * 0.90);
                this.sFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.sFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.sFormListbox.Size, longest_label, this.sFormListbox.Font, (float)0.9, (float)0.9);
                this.sFormListbox.Font = new Font(Constants.FONT_FAMILY, newFont.Size, this.Font.Style);
                this.sFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.sFormLabel.Location.Y + this.sFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.sFormNextButton.Width = (int)(drawableWidth * 0.45);
                this.sFormBackButton.Width = (int)(drawableWidth * 0.45);
                this.sFormNextButton.Height = (int)(drawableHeight * 0.20);
                this.sFormBackButton.Height = (int)(drawableHeight * 0.20);

                this.sFormBackButton.Location = new Point(Constants.WIDGET_SPACING, (int)(this.sFormListbox.Location.Y + this.sFormListbox.Height + Constants.WIDGET_SPACING));
                this.sFormNextButton.Location = new Point((int)(this.sFormNextButton.Width + Constants.WIDGET_SPACING),
                    (int)(this.sFormListbox.Location.Y + this.sFormListbox.Height + Constants.WIDGET_SPACING));
                this.sFormBackButton.Font = this.sFormNextButton.Font = GUIHelper.CalculateBestFitFont(this.sFormNextButton.Parent.CreateGraphics(), Constants.MIN_FONT,
                    Constants.MAX_FONT, this.sFormNextButton.Size, "Next", this.sFormNextButton.Font, (float)0.9, (float)0.9);
                this.sFormNextButton.Enabled = false;

            }

            if (sForm.Visible == false)
                sForm.Show();
            this.aForm.Visible = false;
        }


        void sFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            selectedWocketController=this.sFormListbox.SelectedIndex;
            if (this.sFormNextButton.Enabled == false)
                this.sFormNextButton.Enabled = true;
        }

        void sFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.aForm.Visible = true;
            this.sForm.Visible = false;

        }



        #endregion Sensors Configuration Form


        private System.Windows.Forms.Form lForm;
        private System.Windows.Forms.MainMenu lFormMainMenu;
        private System.Windows.Forms.Label lFormLabel;
        private System.Windows.Forms.TextBox lFormTextBox;
        private System.Windows.Forms.Button lFormBrowseButton;
        private System.Windows.Forms.Button lFormNextButton;
        private System.Windows.Forms.Button lFormBackButton;

        void lFormClassisifierBrowseButton_Click(object sender, System.EventArgs e)
        {
            FolderBrowserDialog folderSelect = new FolderBrowserDialog();
            folderSelect.ShowDialog();
            this.lFormTextBox.Text = folderSelect.SelectedPath;
            this.storageDirectory = folderSelect.SelectedPath;
            if (Directory.Exists(this.storageDirectory))
            {
                if (DirectoryHelper.isDirectoryEmpty(this.storageDirectory))
                {
                    this.lFormNextButton.Enabled = false;
                    MessageBox.Show("Error: Directory is empty");

                }
                else
                    this.lFormNextButton.Enabled = true;
            }
            else
            {
                this.lFormNextButton.Enabled = false;
                MessageBox.Show("Error: Directory not found");
            }
        }

        void lFormClassifierNextButton_Click(object sender, System.EventArgs e)
        {
            this.lForm.Visible = false;
            try
            {
                InitializeActivityTracker();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Error: " + ex.Message);
                Application.Exit();
            }
        }

        void lFormBrowseButton_Click(object sender, System.EventArgs e)
        {
            FolderBrowserDialog folderSelect = new FolderBrowserDialog();
            folderSelect.ShowDialog();
            this.lFormTextBox.Text = folderSelect.SelectedPath;
            this.storageDirectory = folderSelect.SelectedPath;
            if (Directory.Exists(this.storageDirectory))
            {
                if (!(DirectoryHelper.isDirectoryEmpty(this.storageDirectory)))
                {
                    this.lFormNextButton.Enabled = false;
                    MessageBox.Show("Error: Directory is not empty");

                }
                else
                    this.lFormNextButton.Enabled = true;
            }
            else
            {
                this.lFormNextButton.Enabled = false;
                MessageBox.Show("Error: Directory not found");
            }
        }

        void lFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.sForm.Visible = true;
            this.lForm.Visible = false;
        }

        void sFormNextButton_Click(object sender, System.EventArgs e)
        {
             //initialize the path as an empty string
            string firstCard = "";

            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();
           
            //iterate through them
            for (int x = 0; x < fsi.Length; x++)
            {
                //check to see if this is a temporary storage card (e.g. SD card)
                if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                {
                    //if so, return the path
                    firstCard = fsi[x].FullName;
                    break;
                }
            }
            string name = firstCard + "\\Wockets\\Session" + DateTime.Now.Month + "-" + DateTime.Now.Day + "-" + DateTime.Now.Hour + "-" + DateTime.Now.Minute + "-" + DateTime.Now.Second;
            Directory.CreateDirectory(name);
            this.storageDirectory = name;
            this.sForm.Visible = false;
            try
            {
                InitializeDataLogger();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Error: " + ex.Message);
                Application.Exit();
            }
        }



        private System.Windows.Forms.Button dataLoggerButton;
        private System.Windows.Forms.Button activityTrackerButton;
        private System.Windows.Forms.Button calibratorButton;
        private System.Windows.Forms.Button FontSizeButton;

        #region PC and PocketPC Specific Widgets
#if (PocketPC)


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