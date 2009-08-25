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
        private MenuItem NextItem;
        private MenuItem BackItem;

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
            this.NextItem = new MenuItem();
            this.BackItem = new MenuItem();
            this.mainList = new ListView();
            this.SuspendLayout();




            //
            // WocketsForm
            //
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = false;
            this.mainList.Columns.Add("", mainList.Size.Width, HorizontalAlignment.Left);
            ListViewItem item = new ListViewItem();
            item.Text = "Data Logger";
            this.mainList.Items.Add(item);
            item = new ListViewItem();
            item.Text = "Activity Tracker";
            this.mainList.Items.Add(item);
            item = new ListViewItem();
            item.Text = "Calibrate";
            this.mainList.Items.Add(item);
            item = new ListViewItem();
            item.Text = "Play Exergame";
            this.mainList.Items.Add(item);
            this.mainList.SelectedIndexChanged += new EventHandler(this.mainViewChanged);
            this.mainMenu1.MenuItems.Add(this.BackItem);
            this.mainMenu1.MenuItems.Add(this.NextItem);
            this.mainList.View = View.List;
            this.Controls.Add(this.mainList);


            this.Menu = this.mainMenu1;
            this.Name = "WocketsForm";
            this.Text = "Wockets Software";
            this.Resize += new System.EventHandler(WocketsForm_Resize);
            this.ResumeLayout(false);

        }

        void WocketsForm_Resize(object sender, System.EventArgs e)
        {
            int num_widgets = 1;
            //Dynamically adjust components based on screen size
            //Set form size
            this.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
            if (this.Width > Constants.MAX_FORM_WIDTH)
                this.Width = Constants.MAX_FORM_WIDTH;
            this.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
            if (this.Height > Constants.MAX_FORM_HEIGHT)
                this.Height = Constants.MAX_FORM_HEIGHT;

            Form l = new Form();
            l.Size = new Size(this.Width, this.Height - 20);
            Font f=GUIHelper.CalculateBestFitFont(l.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, l.Size, "Play Exergame", new Font("Tahoma", 18F, System.Drawing.FontStyle.Bold), (float)0.9, (float)0.9);


            int buttonHeight = (this.ClientSize.Height - ((num_widgets + 1) * Constants.WIDGET_SPACING)) / num_widgets;
            int buttonWidth = this.ClientSize.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
            this.mainList.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
            this.mainList.Name = "Main List";
            this.mainList.Size = new Size(this.Width, this.Height - 20);
            this.mainList.Font = f;//new Font("Tahoma", 18F, System.Drawing.FontStyle.Bold);


            //NextItem
            this.NextItem.Text = "Next";
            this.NextItem.Enabled = false;
            this.NextItem.Click += new EventHandler(this.mainNext_Click);

            //BackItem
            this.BackItem.Text = "Back";
            this.BackItem.Enabled = false;


        }


        #region Sensor Calibration Form
        private System.Windows.Forms.Form cForm;
        private System.Windows.Forms.MainMenu cFormMainMenu;
        private System.Windows.Forms.Label cFormLabel;
        private System.Windows.Forms.ListView cFormListbox;
        private System.Windows.Forms.MenuItem cFormNextButton;
        private System.Windows.Forms.MenuItem cFormBackButton;

        void mainNext_Click(object sender, EventArgs e)
        {
            if (this.mainList.SelectedIndices[0] == 0)
            {
                this.dataLoggerButton_Click(sender, e);
            }
            else if (this.mainList.SelectedIndices[0] == 1)
            {
                this.activityTrackerButton_Click(sender, e);
            }
            else if (this.mainList.SelectedIndices[0] == 2)
            {
                this.calibratorButton_Click(sender, e);
            }
            else if (this.mainList.SelectedIndices[0] == 3)
            {
                this.playExergameButton_Click(sender, e);
            }
        }


        void mainViewChanged(object sender, EventArgs e)
        {
            this.NextItem.Enabled = true;
        }

        void calibratorButton_Click(object sender, EventArgs e)
        {
            string longest_label = "";
            if (this.cForm == null)
            {
                this.cForm = new System.Windows.Forms.Form();
                this.cFormMainMenu = new System.Windows.Forms.MainMenu();
                this.cFormListbox = new System.Windows.Forms.ListView();
                this.cFormLabel = new System.Windows.Forms.Label();
                this.cFormNextButton = new System.Windows.Forms.MenuItem();
                this.cFormBackButton = new System.Windows.Forms.MenuItem();
                this.cForm.SuspendLayout();
                //
                // cFormListbox
                //
                this.cFormListbox.Location = new System.Drawing.Point(72, 44);
                this.cFormListbox.View = View.List;
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
                this.cFormNextButton.Text = "Next";
                this.cFormNextButton.Click += new System.EventHandler(cFormNextButton_Click);
                //
                // cFormBackButton
                //
                this.cFormBackButton.Text = "Back";
                this.cFormBackButton.Click += new System.EventHandler(cFormBackButton_Click);
                //
                // aForm
                //
                this.cForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.cForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.cForm.AutoScroll = false;
                this.cForm.ClientSize = new System.Drawing.Size(240, 268);
                this.cFormMainMenu.MenuItems.Add(this.cFormBackButton);
                this.cFormMainMenu.MenuItems.Add(this.cFormNextButton);
                this.cForm.Controls.Add(this.cFormLabel);
                this.cForm.Controls.Add(this.cFormListbox);
                this.cForm.Menu = this.cFormMainMenu;
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
                    this.cFormListbox.Items.Add(new ListViewItem(this.wocketsControllers[i]._Name));
                    if (longest_label.Length < this.wocketsControllers[i]._Name.Length)
                        longest_label = this.wocketsControllers[i]._Name;
                }

                //Listbox dynamic placement
                this.cFormListbox.Width = (int)(drawableWidth * 0.90);
                this.cFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.cFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.cFormListbox.Size, longest_label, this.cFormListbox.Font, (float)0.9, (float)0.9);
                this.cFormListbox.Font = new Font(Constants.FONT_FAMILY, 12F, this.Font.Style);
                this.cFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.cFormLabel.Location.Y + this.cFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons

                this.cFormNextButton.Enabled = false;

            }

            if (cForm.Visible == false)
                cForm.Show();
        }

        void cFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            if (this.cFormNextButton.Enabled == false)
                this.cFormNextButton.Enabled = true;
        }

        void cFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.cForm.Visible = false;

        }


        void cFormNextButton_Click(object sender, System.EventArgs e)
        {
            selectedWocketController = this.cFormListbox.SelectedIndices[0];
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
                this.BackItem.Enabled = true;
                this.lForm = new System.Windows.Forms.Form();
                this.lFormMainMenu = new System.Windows.Forms.MainMenu();
                this.lFormLabel = new System.Windows.Forms.Label();
                this.lFormTextBox = new System.Windows.Forms.TextBox();
                this.lFormNextButton = new System.Windows.Forms.MenuItem();
                this.lFormBackButton = new System.Windows.Forms.MenuItem();

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
                // lFormNextButton
                //
                this.lFormNextButton.Text = "Browse";
                this.lFormNextButton.Click += new System.EventHandler(this.lFormClassisifierBrowseButton_Click);
                //
                // lFormBackButton
                //
                this.lFormBackButton.Text = "Back";
                this.lFormBackButton.Click += new System.EventHandler(this.lFormBackButton_Click);
                //
                // lForm
                //
                this.lForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.lForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.lForm.AutoScroll = false;
                this.lForm.ClientSize = new System.Drawing.Size(240, 268);
                this.lFormMainMenu.MenuItems.Add(this.lFormBackButton);
                this.lFormMainMenu.MenuItems.Add(this.lFormNextButton);
                this.lForm.Controls.Add(this.lFormTextBox);
                this.lForm.Controls.Add(this.lFormLabel);
                this.lForm.Menu = this.lFormMainMenu;
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

            }

            if (lForm.Visible == false)
                lForm.Show();
        }

        #endregion Interface Functions Wockets Form

        #region Activity Protocols Form
        private System.Windows.Forms.Form aForm;
        private System.Windows.Forms.MainMenu aFormMainMenu;
        private System.Windows.Forms.Label aFormLabel;
        private System.Windows.Forms.ListView aFormListbox;
        private System.Windows.Forms.MenuItem aFormNextButton;
        private System.Windows.Forms.MenuItem aFormBackButton;
        void dataLoggerButton_Click(object sender, System.EventArgs e)
        {
            if (this.aForm == null)
            {
                this.aForm = new System.Windows.Forms.Form();
                this.aFormMainMenu = new System.Windows.Forms.MainMenu();
                this.aFormListbox = new System.Windows.Forms.ListView();
                this.aFormLabel = new System.Windows.Forms.Label();
                this.aFormNextButton = new System.Windows.Forms.MenuItem();
                this.aFormBackButton = new System.Windows.Forms.MenuItem();
                this.aForm.SuspendLayout();
                //
                // aFormListbox
                //
                this.aFormListbox.Location = new System.Drawing.Point(72, 44);
                this.aFormListbox.View = View.List;
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
                this.aFormNextButton.Text = "Next";
                this.aFormNextButton.Click += new System.EventHandler(aFormNextButton_Click);
                //
                // activityProtocolsBackButton
                //
                this.aFormBackButton.Text = "Back";
                this.aFormBackButton.Click += new System.EventHandler(aFormBackButton_Click);
                //
                // aForm
                //
                this.aForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.aForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.aForm.AutoScroll = false;
                this.aForm.ClientSize = new System.Drawing.Size(240, 268);
                this.aFormMainMenu.MenuItems.Add(this.aFormBackButton);
                this.aFormMainMenu.MenuItems.Add(this.aFormNextButton);
                this.aForm.Controls.Add(this.aFormLabel);
                this.aForm.Controls.Add(this.aFormListbox);
                this.aForm.Menu = this.aFormMainMenu;
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
                for (int i = 0; (i < this.aProtocols.Count); i++)
                {
                    this.aFormListbox.Items.Add(new ListViewItem(this.aProtocols[i]._Name));
                    if (longest_label.Length < this.aProtocols[i]._Name.Length)
                        longest_label = this.aProtocols[i]._Name;
                }

                //Listbox dynamic placement
                this.aFormListbox.Width = (int)(drawableWidth * 0.90);
                this.aFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.aFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.aFormListbox.Size, longest_label, this.aFormListbox.Font, (float)0.9, (float)0.9);
                this.aFormListbox.Font = new Font(Constants.FONT_FAMILY, 12F, this.Font.Style);
                this.aFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.aFormLabel.Location.Y + this.aFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.aFormNextButton.Enabled = false;

            }

            if (aForm.Visible == false)
                aForm.Show();
            this.Visible = false;
        }


        void aFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            if (this.aFormNextButton.Enabled == false)
                this.aFormNextButton.Enabled = true;
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
        private System.Windows.Forms.ListView sFormListbox;
        private System.Windows.Forms.MenuItem sFormNextButton;
        private System.Windows.Forms.MenuItem sFormBackButton;

        void aFormNextButton_Click(object sender, System.EventArgs e)
        {
            this.selectedActivityProtocol = this.aFormListbox.SelectedIndices[0];
            string longest_label = "";
            if (this.sForm == null)
            {
                this.sForm = new System.Windows.Forms.Form();
                this.sFormMainMenu = new System.Windows.Forms.MainMenu();
                this.sFormListbox = new System.Windows.Forms.ListView();
                this.sFormLabel = new System.Windows.Forms.Label();
                this.sFormNextButton = new System.Windows.Forms.MenuItem();
                this.sFormBackButton = new System.Windows.Forms.MenuItem();
                this.sForm.SuspendLayout();
                //
                // sFormListbox
                //
                this.sFormListbox.Location = new System.Drawing.Point(72, 44);
                this.sFormListbox.View = View.List;
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
                this.sFormNextButton.Text = "Next";
                this.sFormNextButton.Click += new System.EventHandler(sFormNextButton_Click);
                //
                // sFormBackButton
                //
                this.sFormBackButton.Text = "Back";
                this.sFormBackButton.Click += new System.EventHandler(sFormBackButton_Click);
                //
                // aForm
                //
                this.sForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.sForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.sForm.AutoScroll = false;
                this.sForm.ClientSize = new System.Drawing.Size(240, 268);
                this.sFormMainMenu.MenuItems.Add(this.sFormBackButton);
                this.sFormMainMenu.MenuItems.Add(this.sFormNextButton);
                this.sForm.Controls.Add(this.sFormLabel);
                this.sForm.Controls.Add(this.sFormListbox);
                this.sForm.Menu = this.sFormMainMenu;
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
                    this.sFormListbox.Items.Add(new ListViewItem(this.wocketsControllers[i]._Name));
                    if (longest_label.Length < this.wocketsControllers[i]._Name.Length)
                        longest_label = this.wocketsControllers[i]._Name;
                }

                //Listbox dynamic placement
                this.sFormListbox.Width = (int)(drawableWidth * 0.90);
                this.sFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.sFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.sFormListbox.Size, longest_label, this.sFormListbox.Font, (float)0.9, (float)0.9);
                this.sFormListbox.Font = new Font(Constants.FONT_FAMILY, 12F, this.Font.Style);
                this.sFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.sFormLabel.Location.Y + this.sFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.sFormNextButton.Enabled = false;

            }

            if (sForm.Visible == false)
                sForm.Show();
            this.aForm.Visible = false;
        }


        void sFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
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
        private System.Windows.Forms.MenuItem lFormNextButton;
        private System.Windows.Forms.MenuItem lFormBackButton;

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
            if (this.storageDirectory == "")
            {
                FolderBrowserDialog folderSelect = new FolderBrowserDialog();
                folderSelect.ShowDialog();
                this.lFormTextBox.Text = folderSelect.SelectedPath;
                this.storageDirectory = folderSelect.SelectedPath;
                if (Directory.Exists(this.storageDirectory))
                {
                    if (!(DirectoryHelper.isDirectoryEmpty(this.storageDirectory)))
                    {
                        this.storageDirectory = "";
                        MessageBox.Show("Error: Directory is not empty");

                    }
                    else
                        ((MenuItem)sender).Text = "Next";
                }
                else
                {
                    this.storageDirectory = "";
                    MessageBox.Show("Error: Directory not found");
                }
            }
            else
                this.lFormClassifierNextButton_Click(sender, e);
        }

        void lFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.sForm.Visible = true;
            this.lForm.Visible = false;
        }

        void sFormNextButton_Click(object sender, System.EventArgs e)
        {
            //initialize the path as an empty string
            this.selectedWocketController = this.sFormListbox.SelectedIndices[0];
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



        private System.Windows.Forms.ListView mainList;

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

        #region Exergame


        private System.Windows.Forms.Form eForm;
        private System.Windows.Forms.MainMenu eFormMainMenu;
        private System.Windows.Forms.Label eFormLabel;
        private System.Windows.Forms.ListView eFormListbox;
        private System.Windows.Forms.MenuItem eFormNextButton;
        private System.Windows.Forms.MenuItem eFormBackButton;

        void playExergameButton_Click(object sender, System.EventArgs e)
        {
            if (this.eForm == null)
            {
                this.eForm = new System.Windows.Forms.Form();
                this.eFormMainMenu = new System.Windows.Forms.MainMenu();
                this.eFormListbox = new System.Windows.Forms.ListView();
                this.eFormLabel = new System.Windows.Forms.Label();
                this.eFormNextButton = new System.Windows.Forms.MenuItem();
                this.eFormBackButton = new System.Windows.Forms.MenuItem();
                this.eForm.SuspendLayout();
                //
                // eFormListbox
                //
                this.eFormListbox.Location = new System.Drawing.Point(72, 44);
                this.eFormListbox.View = View.List;
                this.eFormListbox.Name = "eFormListbox";
                this.eFormListbox.Size = new System.Drawing.Size(100, 100);
                this.eFormListbox.TabIndex = 0;
                this.eFormListbox.SelectedIndexChanged += new System.EventHandler(eFormListbox_SelectedIndexChanged);
                //
                // chooseActivityProtocolLabel
                //
                this.eFormLabel.Location = new System.Drawing.Point(15, 9);
                this.eFormLabel.Name = "chooseActivityProtocolLabel";
                this.eFormLabel.Size = new System.Drawing.Size(182, 23);
                this.eFormLabel.Text = "Choose an activity protocol:";
                //
                // activityProtocolsNextButton
                //
                this.eFormNextButton.Text = "Next";
                this.eFormNextButton.Click += new System.EventHandler(eFormNextButton_Click);
                //
                // activityProtocolsBackButton
                //
                this.eFormBackButton.Text = "Back";
                this.eFormBackButton.Click += new System.EventHandler(eFormBackButton_Click);
                //
                // eForm
                //
                this.eForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.eForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.eForm.AutoScroll = false;
                this.eForm.ClientSize = new System.Drawing.Size(240, 268);
                this.eFormMainMenu.MenuItems.Add(this.eFormBackButton);
                this.eFormMainMenu.MenuItems.Add(this.eFormNextButton);
                this.eForm.Controls.Add(this.eFormLabel);
                this.eForm.Controls.Add(this.eFormListbox);
                this.eForm.Menu = this.eFormMainMenu;
                this.eForm.Name = "eForm";
                this.eForm.Text = "Activity Protocols";
                this.eForm.ResumeLayout(false);


                this.eForm.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
                if (this.eForm.Width > Constants.MAX_FORM_WIDTH)
                    this.eForm.Width = Constants.MAX_FORM_WIDTH;
                this.eForm.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
                if (this.eForm.Height > Constants.MAX_FORM_HEIGHT)
                    this.eForm.Height = Constants.MAX_FORM_HEIGHT;


                double drawableWidth = this.eForm.Width;
                double drawableHeight = this.eForm.Height - 4 * Constants.WIDGET_SPACING;

                //adjust top label size and location
                this.eFormLabel.Width = (int)drawableWidth;
                this.eFormLabel.Height = (int)(drawableHeight * 0.15);
                this.eFormLabel.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
                this.eFormLabel.Font = GUIHelper.CalculateBestFitFont(this.eFormLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.eForm.Size, this.eFormLabel.Text, this.eForm.Font, (float)0.9, (float)0.9);

                //Load the activity protocols from the master directory
                this.aProtocols = new AnnotationProtocolList();
                this.aProtocols.FromXML(Constants.MASTER_DIRECTORY + "\\ActivityProtocols.xml");
                string longest_label = "";
                for (int i = 0; (i < this.aProtocols.Count); i++)
                {
                    this.eFormListbox.Items.Add(new ListViewItem(this.aProtocols[i]._Name));
                    if (longest_label.Length < this.aProtocols[i]._Name.Length)
                        longest_label = this.aProtocols[i]._Name;
                }

                //Listbox dynamic placement
                this.eFormListbox.Width = (int)(drawableWidth * 0.90);
                this.eFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.eFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.eFormListbox.Size, longest_label, this.eFormListbox.Font, (float)0.9, (float)0.9);
                this.eFormListbox.Font = new Font(Constants.FONT_FAMILY, 12F, this.Font.Style);
                this.eFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.eFormLabel.Location.Y + this.eFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.eFormNextButton.Enabled = false;

            }

            if (eForm.Visible == false)
                eForm.Show();
            this.Visible = false;
        }

        void eFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            if (this.eFormNextButton.Enabled == false)
                this.eFormNextButton.Enabled = true;
        }

        void eFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.Visible = true;
            this.eForm.Visible = false;
        }

        void eFormNextButton_Click(object sender, System.EventArgs e)
        {
            string longest_label = "";
            if (this.xForm == null)
            {
                this.xForm = new System.Windows.Forms.Form();
                this.xFormMainMenu = new System.Windows.Forms.MainMenu();
                this.xFormListbox = new System.Windows.Forms.ListView();
                this.xFormLabel = new System.Windows.Forms.Label();
                this.xFormNextButton = new System.Windows.Forms.MenuItem();
                this.xFormBackButton = new System.Windows.Forms.MenuItem();
                this.xForm.SuspendLayout();
                //
                // xFormListbox
                //
                this.xFormListbox.Location = new System.Drawing.Point(72, 44);
                this.xFormListbox.View = View.List;
                this.xFormListbox.Name = "xFormListbox";
                this.xFormListbox.Size = new System.Drawing.Size(100, 100);
                this.xFormListbox.TabIndex = 0;
                this.xFormListbox.SelectedIndexChanged += new System.EventHandler(xFormListbox_SelectedIndexChanged);
                //
                // xForm
                //
                this.xFormLabel.Location = new System.Drawing.Point(15, 9);
                this.xFormLabel.Name = "chooseWocketControllerLabel";
                this.xFormLabel.Size = new System.Drawing.Size(182, 23);
                this.xFormLabel.Text = "Choose a wocket configuration:";
                //
                // xFormNextButton
                //
                this.xFormNextButton.Text = "Next";
                this.xFormNextButton.Click += new System.EventHandler(xFormNextButton_Click);
                //
                // xFormBackButton
                //
                this.xFormBackButton.Text = "Back";
                this.xFormBackButton.Click += new System.EventHandler(xFormBackButton_Click);
                //
                // eForm
                //
                this.xForm.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
                this.xForm.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
                this.xForm.AutoScroll = false;
                this.xForm.ClientSize = new System.Drawing.Size(240, 268);
                this.xFormMainMenu.MenuItems.Add(this.xFormBackButton);
                this.xFormMainMenu.MenuItems.Add(this.xFormNextButton);
                this.xForm.Controls.Add(this.xFormLabel);
                this.xForm.Controls.Add(this.xFormListbox);
                this.xForm.Menu = this.xFormMainMenu;
                this.xForm.Name = "xForm";
                this.xForm.Text = "Wocket Configurations";
                this.xForm.ResumeLayout(false);


                this.xForm.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
                if (this.xForm.Width > Constants.MAX_FORM_WIDTH)
                    this.xForm.Width = Constants.MAX_FORM_WIDTH;
                this.xForm.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
                if (this.xForm.Height > Constants.MAX_FORM_HEIGHT)
                    this.xForm.Height = Constants.MAX_FORM_HEIGHT;


                double drawableWidth = this.xForm.Width;
                double drawableHeight = this.xForm.Height - 4 * Constants.WIDGET_SPACING;

                //adjust top label size and location
                this.xFormLabel.Width = (int)drawableWidth;
                this.xFormLabel.Height = (int)(drawableHeight * 0.15);
                this.xFormLabel.Location = new Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
                this.xFormLabel.Font = GUIHelper.CalculateBestFitFont(this.xFormLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                       Constants.MAX_FONT, this.xForm.Size, this.xFormLabel.Text, this.xForm.Font, (float)0.9, (float)0.9);

                this.wocketsControllers = new WocketsControllerList();
                this.wocketsControllers.FromXML(Constants.MASTER_DIRECTORY);
                for (int i = 0; (i < this.wocketsControllers.Count); i++)
                {
                    this.xFormListbox.Items.Add(new ListViewItem(this.wocketsControllers[i]._Name));
                    if (longest_label.Length < this.wocketsControllers[i]._Name.Length)
                        longest_label = this.wocketsControllers[i]._Name;
                }


                //Listbox dynamic placement
                this.xFormListbox.Width = (int)(drawableWidth * 0.90);
                this.xFormListbox.Height = (int)(drawableHeight * 0.60);
                Font newFont = GUIHelper.CalculateBestFitFont(this.xFormListbox.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.xFormListbox.Size, longest_label, this.xFormListbox.Font, (float)0.9, (float)0.9);
                this.xFormListbox.Font = new Font(Constants.FONT_FAMILY, 12F, this.Font.Style);
                this.xFormListbox.Location = new Point(Constants.WIDGET_SPACING, (int)this.xFormLabel.Location.Y + this.xFormLabel.Height + Constants.WIDGET_SPACING);

                // buttons
                this.xFormNextButton.Enabled = false;

            }

            if (xForm.Visible == false)
                xForm.Show();
            this.eForm.Visible = false;
        }

        private System.Windows.Forms.Form xForm;
        private System.Windows.Forms.MainMenu xFormMainMenu;
        private System.Windows.Forms.Label xFormLabel;
        private System.Windows.Forms.ListView xFormListbox;
        private System.Windows.Forms.MenuItem xFormNextButton;
        private System.Windows.Forms.MenuItem xFormBackButton;

        void xFormListbox_SelectedIndexChanged(object sender, System.EventArgs e)
        {
            selectedWocketController = this.xFormListbox.SelectedIndices[0];
            if (this.xFormNextButton.Enabled == false)
                this.xFormNextButton.Enabled = true;
        }

        void xFormBackButton_Click(object sender, System.EventArgs e)
        {
            this.eForm.Visible = true;
            this.xForm.Visible = false;

        }

        void xFormNextButton_Click(object sender, System.EventArgs e)
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
            this.xForm.Visible = false;
            try
            {

                InitializeExergame();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Error: " + ex.Message);
                Application.Exit();
            }
        }

        #endregion Exergame

    }
}