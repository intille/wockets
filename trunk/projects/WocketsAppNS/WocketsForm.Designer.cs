using System;
using System.Drawing;
using System.Windows.Forms;
using System.IO;
using System.Threading;
using Wockets;
using Wockets.Data.Annotation;
using WocketsAppNS.Utils;



namespace WocketsAppNS
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



        void mainNext_Click(object sender, EventArgs e)
        {
            if (this.mainList.SelectedIndices[0] == 0)
            {
                this.dataLoggerButton_Click(sender, e);
            }

        }

        void mainViewChanged(object sender, EventArgs e)
        {
            this.NextItem.Enabled = true;
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
                    firstCard = fsi[x].FullName;
                    try
                    {
                        Directory.CreateDirectory(firstCard+"\\writable");
                        Directory.Delete(firstCard + "\\writable");
                    }
                    catch (Exception)
                    {
                        firstCard = "";
                        continue;
                    }
                    //if so, return the path
                  
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


    }
}