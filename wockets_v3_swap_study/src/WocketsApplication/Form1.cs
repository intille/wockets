﻿using System;
using System.Linq;
using System.Collections.Generic;
using System.Collections;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using WocketsApplication.Controls;
using WocketsApplication.Controls.Alpha;
using System.Threading;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Diagnostics;
using System.IO;
using  Microsoft.Win32;
using Wockets.Kernel.Types;
using Wockets.Utils.IPC;
using Wockets.Utils;
using Wockets.Kernel;
using Wockets.Data.Annotation;
using Wockets.Data.Plotters;
using Wockets;
using Microsoft.VisualBasic;

using OpenNETCF.GDIPlus;
using Charts.twodimensional;
using OpenNETCF.Windows.Forms;

using WocketsWeka;
using weka.classifiers;
using weka;
using weka.core;
using weka.classifiers.trees;
using Wockets.Data.Features;
using Wockets.Utils.feedback;
using Wockets.Data.Configuration;
using WocketsApplication.Controls.Utils;

#if (PocketPC)
    using Wockets.Utils.IPC.MMF;
#endif


namespace WocketsApplication
{
    public enum ActivityStatus
    {
        Measuring,
        Annotating,
        None
    }


    public partial class Form1 : Form
    {

        #region Variables

        //private const int NUMBER_BUTTONS=9;

        //--- Primary Screen Dimentions ---
        // P3300: 240x320
        // Diamond Touch: 480x640
        // Diamond Touch 2: 480x800
        private int SCREEN_RESOLUTION_X = Screen.PrimaryScreen.Bounds.Width; 
        private int SCREEN_RESOLUTION_Y = Screen.PrimaryScreen.Bounds.Height; 

        private ClickableAlphaPanel[] panels= new ClickableAlphaPanel[ControlID.NUMBER_PANELS];
        private int[] slidingPanels = new int[2] { 0, 1 };
        private int[] numberButtons = new int[ControlID.NUMBER_PANELS];
        private int currentPanel = 0;
        private int currentPanelIndex = 0;
        private Rectangle clientArea;
        public bool pushed = false;
        private AlphaContainer _alphaManager;
  
         private Sound disconnectedAlert =null;
         private Sound connectedAlert = null;


        private Thread kListenerThread;


        delegate void UpdatewWocketsListCallback();
        private bool disposed = false;

        public void UpdatewWocketsList()
        {
            if (!disposed)
            {
                if (wocketsList.InvokeRequired)
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                {
                    UpdatewWocketsListCallback d = new UpdatewWocketsListCallback(UpdatewWocketsList);
                    this.Invoke(d, new object[] { });
                }
                else
                {
                    wocketsList._Location = 0;
                    wocketsList.Controls.Clear();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH);

                    if (rk != null)
                    {
                        //BUG crashing
                        string[] sensors = rk.GetSubKeyNames();
                        rk.Close();
                        if (sensors.Length > 0)
                        {
                            wocketsList._Status = "";
                            for (int i = 0; (i < sensors.Length); i++)
                            {

                                rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH + "\\" + sensors[i]); ;
                                WocketListItem wi = new WocketListItem((string)rk.GetValue("Name"), (string)rk.GetValue("MacAddress"), i + 1);
                                rk.Close();
                                wi.Index = i;
                                wi.Name = wi.Index.ToString();
                                wi.Location = new Point(0, wi.Height * i);
                                wi.Click += new EventHandler(wocketClickHandler);
                                wocketsList.Controls.Add(wi);
                            }
                            wocketsList._Status = "";
                        }
                        else
                        {
                            wocketsList._Status = "No Wockets Found...";
                        }
                    }
                    else
                    {
                        wocketsList._Status = "No Wockets Found...";
                    }
                    wocketsList.Refresh();


                }
            }
        }

        
        private Thread soundThread = null;

        private void SoundThread()
        {

            MemoryMappedFileStream[] shead = new MemoryMappedFileStream[selectedWockets.Count];
            for (int i = 0; (i < selectedWockets.Count); i++)
            {                
                shead[i] = new MemoryMappedFileStream("\\Temp\\whead" + i + ".dat", "whead" + i, sizeof(int), MemoryProtection.PageReadWrite);
                shead[i].MapViewToProcessMemory(0, sizeof(int));
            }
            byte[] head = new byte[4];
            int[] prevHeads = new int[selectedWockets.Count];
            bool[] disconnected=new bool[selectedWockets.Count];
            for (int i = 0; (i < selectedWockets.Count); i++)
                disconnected[i]=false;
            while (true)
            {
                if (Core._Connected)
                {                    
                    for (int i = 0; (i < selectedWockets.Count); i++)
                    {
                        shead[i].Read(head, 0, 4);
                        int currentHead = BitConverter.ToInt32(head, 0);

                        if ((disconnected[i]) && (currentHead != prevHeads[i]))
                        {
                            disconnected[i] = false;
                            connectedAlert.Play();
                        }
                        else if (currentHead == prevHeads[i])
                            disconnected[i] = true;
                        
                        prevHeads[i] = currentHead;
                        shead[i].Seek(0, System.IO.SeekOrigin.Begin);
                    }

                    for (int i=0;(i<selectedWockets.Count);i++)
                        if (disconnected[i])
                        {
                            disconnectedAlert.Play();
                            Thread.Sleep(200);
                        }
                }
                Thread.Sleep(5000);
            }
        }


        private SimpleFeatureVector fv;
        private TextWriter trainingTW = null;
        private TextWriter structureTW = null;
        private Thread mlThread = null;
        private string arffFileName = "";


        #endregion


        #region Form Related functions

            public Form1()
        {

            RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\MIT\\Wockets", true);
            if (rk == null)
            {
                if (MessageBox.Show("Thanks for installing the wockets\nThe setup will continue. Are you ready?", "",
                        MessageBoxButtons.YesNo,
                        MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.No)
                    Application.Exit();
            }




            ScreenUtils.ShowTaskBar(false);
            ScreenUtils.ShowTrayBar(false);
            InitializeComponent();
            InitializeInterface();

            //all commands should be sent after initializing interface
            wocketsList._Status = "Refresh wockets...";
            _alphaManager = new AlphaContainer(this);
            this.Refresh();
        }

            void Form1_Activated(object sender, EventArgs e)
        {
            ScreenUtils.ShowTaskBar(false);
            ScreenUtils.ShowTrayBar(false);
        }

            void Form1_Deactivate(object sender, EventArgs e)
        {
            ScreenUtils.ShowTaskBar(true);
        }

        #endregion 


        #region Declare Variables Interface
            //private Color[] colors = new Color[ControlID.NUMBER_PANELS] { Color.White, Color.Black, Color.Red, Color.Green, Color.FromArgb(245, 219, 186), Color.FromArgb(245, 219, 186) };
            //private BluetoothPanel pp;

            private AnnotationProtocolList models;
            private Bitmap[] _backBuffers = new Bitmap[ControlID.NUMBER_PANELS];
            private Transitions currentTransition;
            public void AddButton(int panelID, int buttonID, string pressedFilename, string unpressedFilename, int x, int y, int size, string unpressedText, ButtonType type)
            {
                this.panels[panelID]._UnpressedButtonControls[buttonID] = new AlphaPictureBox();
                this.panels[panelID]._UnpressedButtonControls[buttonID].Name = buttonID.ToString();
                this.panels[panelID]._UnpressedButtonControls[buttonID].Size = new Size(size, size);
                this.panels[panelID]._UnpressedButtonControls[buttonID].Image = AlphaImage.CreateFromFile(Constants.PATH + unpressedFilename);
                this.panels[panelID]._UnpressedButtonControls[buttonID].Visible = true;

                this.panels[panelID]._UnpressedButtonControls[buttonID].Location = new Point(x, y);
                this.panels[panelID]._UnpressedButtonControls[buttonID].Click += new EventHandler(clickHandler);
                if (unpressedText != null)
                {
                    this.panels[panelID]._ButtonText[buttonID] = new AlphaLabel();

                    this.panels[panelID]._ButtonText[buttonID].Text = unpressedText;
                    this.panels[panelID]._ButtonText[buttonID].ForeColor = Color.FromArgb(205, 183, 158);
                    this.panels[panelID]._ButtonText[buttonID].Allign = System.Drawing.StringAlignment.Center;
                    this.panels[panelID]._ButtonText[buttonID].Visible = true;
                    if (size == 128)
                    {
                        this.panels[panelID]._ButtonText[buttonID].Font = new Font(FontFamily.GenericSerif, 9.0f, System.Drawing.FontStyle.Regular);
                        this.panels[panelID]._ButtonText[buttonID].Size = new Size(128, 40);
                        this.panels[panelID]._ButtonText[buttonID].Allign = System.Drawing.StringAlignment.Center;
                        this.panels[panelID]._ButtonText[buttonID].Location = new Point(x, y + size + 2);
                    }
                    else if (size == 200)
                    {
                        this.panels[panelID]._ButtonText[buttonID].Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Regular);
                        this.panels[panelID]._ButtonText[buttonID].Size = new Size(500, 100);
                        this.panels[panelID]._ButtonText[buttonID].Allign = System.Drawing.StringAlignment.Center;
                        this.panels[panelID]._ButtonText[buttonID].Location = new Point((Screen.PrimaryScreen.WorkingArea.Width - 500) / 2, y + size + 2);
                    }
                }


                this.panels[panelID]._PressedButtonControls[buttonID] = new AlphaPictureBox();
                this.panels[panelID]._PressedButtonControls[buttonID].Name = buttonID.ToString();
                this.panels[panelID]._PressedButtonControls[buttonID].Size = new Size(128, 30);
                this.panels[panelID]._PressedButtonControls[buttonID].Image = AlphaImage.CreateFromFile(Constants.PATH + pressedFilename);
                this.panels[panelID]._PressedButtonControls[buttonID].Visible = false;
                this.panels[panelID]._PressedButtonControls[buttonID].Location = new Point(x, y);
                this.panels[panelID]._PressedButtonControls[buttonID].Click += new EventHandler(clickHandler);
                this.panels[panelID]._ButtonType[buttonID] = type;
                this.panels[panelID]._ButtonSize[buttonID] = size;
                if (type == ButtonType.Alternating)
                {
                    this.panels[panelID]._PressedButtonControls[buttonID].Enabled = false;
                }
            }


            WocketSlidingList wocketsList = null;
            private Panel bluetoothPanel;
            private Label bluetoothName;
            ArrayList selectedWockets = new ArrayList();
            WocketsScalablePlotter plotter = null;
            private Panel plotterPanel;


            private System.Windows.Forms.ListView annotationProtocolsList;
            private AnnotationProtocolList aProtocols;
            private Button startAnnnotationButton;
            private Label annotationLabel;
            private AlphaLabel statusLabel;
            //private string currentStatus = "";


            private System.Windows.Forms.ListView modelsList;
            private AnnotationProtocolList aModels;
            private Button startMeasuringButton;
            private Label modelLabel;


            private CheckBox saveFeatures;


            private AlphaLabel chooseActivityLabel;
            private Button doneAnnotation;
            private Label examplesLabel;

            private AlphaLabel bestGuessLabel;
            private Button doneClassifying;

            #region EE Panel
            private Chart pieChart;
            private IntPtr token;
            private GdiplusStartupInput input = new GdiplusStartupInput();
            private GdiplusStartupOutput output;
            private Button doneEE;
            #endregion EE Panel


            const int SW_MINIMIZED = 6;
            private const int ACTIVITY_TIMER = 1;
            private ATimer activityTimer;

            [DllImport("coredll.dll")]
            static extern int ShowWindow(IntPtr hWnd, int nCmdShow);

            #endregion


        #region Interface Related Functions

            public void InitializeInterface()
            {
                //GdiplusStartupInput input = new GdiplusStartupInput();
                //GdiplusStartupOutput output;
                //GpStatusPlus stat = NativeMethods.GdiplusStartup(out token, input, out output);

                currentTransition = Transitions.LEFT_TO_RIGHT;

                Constants.PATH = System.IO.Path.GetDirectoryName(
                   System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase) + "\\NeededFiles\\";


                disconnectedAlert = new Sound(Constants.PATH + "sounds\\Disconnected.wav");
                connectedAlert = new Sound(Constants.PATH + "sounds\\Connected.wav");

                this.AutoScroll = false;
                this.numberButtons[ControlID.HOME_PANEL] = ControlID.HOME_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.ABOUT_PANEL] = ControlID.ABOUT_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.SETTINGS_PANEL] = ControlID.SETTINGS_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.WOCKETS_PANEL] = ControlID.WOCKETS_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.WOCKETS_CONFIGURATION_PANEL] = ControlID.WOCKETS_CONFIGURATION_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.PLOTTER_PANEL] = ControlID.PLOTTER_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.ANNOTATION_PROTCOLS_PANEL] = ControlID.ANNOTATION_PROTOCOLS_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.ANNOTATION_BUTTON_PANEL] = ControlID.ANNOTATION_BUTTON_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.ACTIVITY_PANEL] = ControlID.ACTIVITY_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.MODELS_PANEL] = ControlID.MODELS_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.CLASSIFICATION_PANEL] = ControlID.CLASSIFICATION_PANEL_BUTTON_COUNT;
                this.numberButtons[ControlID.EE_PANEL] = ControlID.EE_PANEL_BUTTON_COUNT;


                for (int i = 0; (i < ControlID.NUMBER_PANELS); i++)
                {

                    this.panels[i] = new ClickableAlphaPanel(this.numberButtons[i]);
                    this.panels[i].Size = new Size(SCREEN_RESOLUTION_X, SCREEN_RESOLUTION_Y);
                    this.panels[i].MouseDown += new MouseEventHandler(owner_MouseDown);
                    this.panels[i].MouseUp += new MouseEventHandler(owner_MouseUp);
                    //this.panels[i].BackColor=colors[i];
                    this.panels[i].Dock = DockStyle.Fill;
                    this.panels[i]._Backbuffer = new Bitmap(SCREEN_RESOLUTION_X, SCREEN_RESOLUTION_Y, PixelFormat.Format16bppRgb555);
                    this.Controls.Add(this.panels[i]);
                }


                //setup backgrounds
                this.panels[ControlID.HOME_PANEL]._Background = new Bitmap(Constants.PATH + "Backgrounds\\DottedBlack.png");
                this.panels[ControlID.HOME_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
                this.panels[ControlID.ABOUT_PANEL]._Background = (Bitmap)this.panels[ControlID.HOME_PANEL]._Background.Clone();
                this.panels[ControlID.ABOUT_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
                this.panels[ControlID.SETTINGS_PANEL]._Background = (Bitmap)this.panels[ControlID.HOME_PANEL]._Background.Clone();
                this.panels[ControlID.SETTINGS_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
                this.panels[ControlID.ACTIVITY_PANEL]._Background = (Bitmap)this.panels[ControlID.HOME_PANEL]._Background.Clone();
                this.panels[ControlID.ACTIVITY_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";

                this.panels[ControlID.MODELS_PANEL].BackColor = Color.FromArgb(250, 237, 221);
                this.panels[ControlID.MODELS_PANEL]._ClearCanvas = true;
                this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].BackColor = Color.FromArgb(250, 237, 221);
                this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL]._ClearCanvas = true;
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].BackColor = Color.FromArgb(250, 237, 221);
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL]._ClearCanvas = true;
                this.panels[ControlID.CLASSIFICATION_PANEL].BackColor = Color.FromArgb(250, 237, 221);
                this.panels[ControlID.CLASSIFICATION_PANEL]._ClearCanvas = true;
                this.panels[ControlID.EE_PANEL].BackColor = Color.FromArgb(250, 237, 221);
                this.panels[ControlID.EE_PANEL]._ClearCanvas = true;




                #region Activity Panel
                AddButton(ControlID.ACTIVITY_PANEL, ControlID.MEASURE_ACTIVITY_BUTTON, "Buttons\\MeasureActivityPressed-200.png", "Buttons\\MeasureActivityUnpressed-200.png", (Screen.PrimaryScreen.WorkingArea.Width - 200) / 2, 100, 200, "Measure Activity", ButtonType.Fixed);
                AddButton(ControlID.ACTIVITY_PANEL, ControlID.ANNOTATE_ACTIVITY_BUTTON, "Buttons\\AnnotatePressed-200.png", "Buttons\\AnnotateUnpressed-200.png", (Screen.PrimaryScreen.WorkingArea.Width - 200) / 2, 400, 200, "Annotate Activity", ButtonType.Fixed);
                AddButton(ControlID.ACTIVITY_PANEL, ControlID.HOME_ACTIVITY_BUTTON, "Buttons\\HomePressed-128.png", "Buttons\\HomeUnpressed-128.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                #endregion Activity Panel

                #region Annotation Protocols Panel
                //Setup the annotation protcols list
                annotationProtocolsList = new ListView();
                annotationProtocolsList.Location = new System.Drawing.Point(72, 44);
                annotationProtocolsList.BackColor = Color.White;
                annotationProtocolsList.ForeColor = Color.Black;
                annotationProtocolsList.View = View.List;
                annotationProtocolsList.Name = "annotationProtocolsList";
                annotationProtocolsList.Size = new System.Drawing.Size(100, 100);
                annotationProtocolsList.TabIndex = 0;
                annotationProtocolsList.SelectedIndexChanged += new EventHandler(annotationProtocolsList_SelectedIndexChanged);
                //adjust top label size and location
                annotationLabel = new Label();
                annotationLabel.Width = (int)(Screen.PrimaryScreen.WorkingArea.Width * 0.90);
                annotationLabel.Height = (int)(Screen.PrimaryScreen.WorkingArea.Width * 0.15);
                annotationLabel.Location = new Point(2, 2);
                //Load the activity protocols from the master directory
                this.aProtocols = new AnnotationProtocolList();
                this.aProtocols.FromXML(Constants.PATH + "Master\\ActivityProtocols.xml");
                string longest_label = "";
                for (int i = 0; (i < this.aProtocols.Count); i++)
                {
                    annotationProtocolsList.Items.Add(new ListViewItem(this.aProtocols[i]._Name));
                    if (longest_label.Length < this.aProtocols[i]._Name.Length)
                        longest_label = this.aProtocols[i]._Name;
                }

                //Listbox dynamic placement
                annotationProtocolsList.Width = (int)(Screen.PrimaryScreen.WorkingArea.Width * 0.90);
                annotationProtocolsList.Height = (int)(Screen.PrimaryScreen.WorkingArea.Height * 0.60);
                annotationProtocolsList.Font = new Font(GUIHelper.FONT_FAMILY, 14F, this.Font.Style);
                annotationProtocolsList.Location = new Point((int)(Screen.PrimaryScreen.WorkingArea.Width * 0.05), (int)annotationLabel.Location.Y + annotationLabel.Height + 2);
                this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Controls.Add(annotationProtocolsList);

                //add save features checkbox
                saveFeatures = new CheckBox();
                saveFeatures.Size = new Size(600, 50);
                saveFeatures.Text = "Learn and Annotate";
                saveFeatures.BackColor = Color.FromArgb(250, 237, 221);
                saveFeatures.ForeColor = Color.Black;
                saveFeatures.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
                saveFeatures.Visible = true;
                saveFeatures.Location = new Point(10, annotationProtocolsList.Location.Y + annotationProtocolsList.Height + 10);
                saveFeatures.CheckState = CheckState.Checked;
                saveFeatures.CheckStateChanged += new EventHandler(saveFeatures_CheckStateChanged);
                this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Controls.Add(saveFeatures);

                //add annotation label
                annotationLabel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, 50);
                annotationLabel.Text = "Choose a protocol";
                annotationLabel.BackColor = Color.FromArgb(250, 237, 221);
                annotationLabel.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
                annotationLabel.Visible = true;
                annotationLabel.Location = new Point((int)(Screen.PrimaryScreen.WorkingArea.Width * 0.05), 10);
                this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Controls.Add(annotationLabel);

                //add a button to start
                startAnnnotationButton = new Button();
                startAnnnotationButton.Size = new Size(400, 80);
                startAnnnotationButton.Text = "Begin Annotation";
                startAnnnotationButton.BackColor = Color.LightGray;
                startAnnnotationButton.ForeColor = Color.Black;
                startAnnnotationButton.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
                startAnnnotationButton.Enabled = false;
                startAnnnotationButton.Visible = true;
                startAnnnotationButton.Click += new EventHandler(startAnnnotationButton_Click);
                startAnnnotationButton.Location = new Point(Screen.PrimaryScreen.WorkingArea.Width / 2 - 200, saveFeatures.Location.Y + saveFeatures.Height + 10);
                this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Controls.Add(startAnnnotationButton);

                AddButton(ControlID.ANNOTATION_PROTCOLS_PANEL, ControlID.HOME_ANNOTATION_PROTOCOL_BUTTON, "Buttons\\HomePressed-128.png", "Buttons\\HomeUnpressed-128.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                #endregion Annotation Protocols Panel

                #region Models Panel
                //Setup the annotation protcols list
                modelsList = new ListView();
                modelsList.Location = new System.Drawing.Point(72, 44);
                modelsList.View = View.List;
                modelsList.Name = "modelsList";
                modelsList.BackColor = Color.White;
                modelsList.ForeColor = Color.Black;
                modelsList.Size = new System.Drawing.Size(100, 100);
                modelsList.TabIndex = 0;
                modelsList.SelectedIndexChanged += new EventHandler(modelsList_SelectedIndexChanged);
                //adjust top label size and location
                modelLabel = new Label();
                modelLabel.Width = (int)(Screen.PrimaryScreen.WorkingArea.Width * 0.90);
                modelLabel.Height = (int)(Screen.PrimaryScreen.WorkingArea.Width * 0.15);
                modelLabel.Location = new Point(2, 2);


                //Listbox dynamic placement
                modelsList.Width = (int)(Screen.PrimaryScreen.WorkingArea.Width * 0.90);
                modelsList.Height = (int)(Screen.PrimaryScreen.WorkingArea.Height * 0.60);
                modelsList.Font = new Font(GUIHelper.FONT_FAMILY, 14F, this.Font.Style);
                modelsList.Location = new Point((int)(Screen.PrimaryScreen.WorkingArea.Width * 0.05), (int)modelLabel.Location.Y + modelLabel.Height + 2);
                this.panels[ControlID.MODELS_PANEL].Controls.Add(modelsList);


                //add annotation label
                modelLabel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, 50);
                modelLabel.Text = "Select a learning profile";
                modelLabel.BackColor = Color.FromArgb(250, 237, 221);
                modelLabel.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
                modelLabel.Visible = true;
                modelLabel.Location = new Point((int)(Screen.PrimaryScreen.WorkingArea.Width * 0.05), 10);
                this.panels[ControlID.MODELS_PANEL].Controls.Add(modelLabel);

                //add a button to start
                startMeasuringButton = new Button();
                startMeasuringButton.Size = new Size(400, 80);
                startMeasuringButton.Text = "Begin Measuring";
                startMeasuringButton.BackColor = Color.LightGray;
                startMeasuringButton.ForeColor = Color.Black;
                startMeasuringButton.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
                startMeasuringButton.Enabled = false;
                startMeasuringButton.Visible = true;
                startMeasuringButton.Click += new EventHandler(startMeasuringButton_Click);
                startMeasuringButton.Location = new Point(Screen.PrimaryScreen.WorkingArea.Width / 2 - 200, modelsList.Location.Y + modelsList.Height + 10);
                this.panels[ControlID.MODELS_PANEL].Controls.Add(startMeasuringButton);

                AddButton(ControlID.MODELS_PANEL, ControlID.HOME_MODELS_BUTTON, "Buttons\\HomePressed-128.png", "Buttons\\HomeUnpressed-128.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                #endregion Models Panel

                #region Annotation Buttons Panel
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].AutoScroll = true;
                this.chooseActivityLabel = new AlphaLabel();
                this.chooseActivityLabel.Size = new Size(500, 40);
                this.chooseActivityLabel.Text = "Choose your activity";
                this.chooseActivityLabel.ForeColor = Color.Black;
                this.chooseActivityLabel.Font = new Font(FontFamily.GenericSerif, 10.0f, System.Drawing.FontStyle.Bold);
                this.chooseActivityLabel.Visible = true;
                this.chooseActivityLabel.Location = new Point(1, 1);
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Add(this.chooseActivityLabel);

                this.examplesLabel = new Label();
                this.examplesLabel.Size = new Size(100, 30);
                this.examplesLabel.Text = "00:00";
                this.examplesLabel.ForeColor = Color.Black;
                this.examplesLabel.Font = new Font(FontFamily.GenericSerif, 10.0f, System.Drawing.FontStyle.Bold);
                this.examplesLabel.Visible = true;
                this.examplesLabel.Location = new Point(130, this.Height - 100);
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Add(this.examplesLabel);

                doneAnnotation = new Button();
                MakeButtonMultiline(doneAnnotation);
                doneAnnotation.Size = new Size(200, 80);
                doneAnnotation.Text = "Stop\nLearning";
                doneAnnotation.Font = new Font(FontFamily.GenericSerif, 10.0f, System.Drawing.FontStyle.Bold);
                doneAnnotation.Enabled = true;
                doneAnnotation.Visible = true;
                doneAnnotation.Click += new EventHandler(doneAnnotation_Click);
                doneAnnotation.Location = new Point(250, this.Height - 110);
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Add(doneAnnotation);

                AddButton(ControlID.ANNOTATION_BUTTON_PANEL, ControlID.HOME_ANNOTATION_BUTTON_BUTTON, "Buttons\\HomePressed-128.png", "Buttons\\HomeUnpressed-128.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                //AddButton(ControlID.ANNOTATION_BUTTON_PANEL, ControlID.FINISH_ANNOTATION_BUTTON_BUTTON, "Buttons\\StopPressed-128.png", "Buttons\\StopUnpressed-128.png", 300, this.Height - 130, 128, null, ButtonType.Fixed);
                #endregion Annotation Buttons Panel





                #region Classification Panel
                this.bestGuessLabel = new AlphaLabel();
                this.bestGuessLabel.Size = new Size(500, 60);
                this.bestGuessLabel.Text = "Activity Classification";
                this.bestGuessLabel.ForeColor = Color.Black;
                this.bestGuessLabel.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
                this.bestGuessLabel.Visible = true;
                this.bestGuessLabel.Location = new Point(1, 1);
                this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(this.bestGuessLabel);
                doneClassifying = new Button();
                doneClassifying.Size = new Size(300, 80);
                doneClassifying.Text = "Stop Measuring";
                doneClassifying.Font = new Font(FontFamily.GenericSerif, 12.0f, System.Drawing.FontStyle.Bold);
                doneClassifying.Enabled = true;
                doneClassifying.Visible = true;
                doneClassifying.Click += new EventHandler(doneClassifying_Click);
                doneClassifying.Location = new Point(150, this.Height - 100);
                this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(doneClassifying);
                AddButton(ControlID.CLASSIFICATION_PANEL, ControlID.HOME_CLASSIFICATION_BUTTON, "Buttons\\HomePressed-128.png", "Buttons\\HomeUnpressed-128.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                #endregion Classification Panel



                #region EE Panel


                /*  GpStatusPlus stat = NativeMethods.GdiplusStartup(out token, input, out output);
            pieChart = new Charts.twodimensional.PieChart();
            pieChart.Location = new Point(0, 0);
            pieChart.Size = new Size(200, 200);
            pieChart.IsStretch = true;
            //pieChart.SetCalories(10, 5);
            pieChart.SetActivity("No Activity");
            Hashtable activities = new Hashtable();
            activities.Add("Biceps Curls", 10);
            activities.Add("Jumping Jacks", 10);
            activities.Add("Walking", 10);
            activities.Add("Running", 10);
            activities.Add("Empty", 60 );

            pieChart.Data = activities;
            pieChart.Invalidate();
            

            this.panels[ControlID.EE_PANEL].Controls.Add(pieChart);
            */
                this.activityTimer = new ATimer();
                doneEE = new Button();
                doneEE.Size = new Size(300, 80);
                doneEE.Text = "Done";
                doneEE.Font = new Font(FontFamily.GenericSerif, 12.0f, System.Drawing.FontStyle.Bold);
                doneEE.Enabled = true;
                doneEE.Visible = true;
                doneEE.Click += new EventHandler(doneEE_Click);
                doneEE.Location = new Point(150, this.Height - 100);
                this.panels[ControlID.EE_PANEL].Controls.Add(doneEE);
                AddButton(ControlID.EE_PANEL, ControlID.HOME_EE_BUTTON, "Buttons\\HomePressed-128.png", "Buttons\\HomeUnpressed-128.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                #endregion EE Panel

                //Main Page
                //Home Screen Bottom  Buttons
                //Line 1
                AddButton(ControlID.HOME_PANEL, ControlID.SETTINGS_BUTTON, "Buttons\\SettingsPressed.png", "Buttons\\SettingsUnpressed.png", 0, this.Height - 130, 128, null, ButtonType.Fixed);
                AddButton(ControlID.HOME_PANEL, ControlID.MINIMIZE_BUTTON, "Buttons\\MinimizePressed.png", "Buttons\\MinimizeUnpressed.png", 160, this.Height - 130, 128, null, ButtonType.Fixed);
                AddButton(ControlID.HOME_PANEL, ControlID.RESET_BUTTON, "Buttons\\TurnOffPressed.png", "Buttons\\TurnOffUnpressed.png", 310, this.Height - 130, 128, null, ButtonType.Fixed);



                //Home Screen Buttons
                //Line 1
                AddButton(ControlID.HOME_PANEL, ControlID.LINE_CHART_BUTTON, "Buttons\\LineChartPressed.png", "Buttons\\LineChartUnpressed.png", 0, 50, 128, "Plot", ButtonType.Fixed);
                AddButton(ControlID.HOME_PANEL, ControlID.ACTIVITY_BUTTON, "Buttons\\ActivityPressed-128.png", "Buttons\\ActivityUnpressed-128.png", 160, 50, 128, "Activity", ButtonType.Fixed);

                //Line 2            
                AddButton(ControlID.HOME_PANEL, ControlID.CONNECT_BUTTON, "Buttons\\DisconnectUnpressed-128.png", "Buttons\\ConnectUnpressed-128.png", 310, 50, 128, "Connect", ButtonType.Alternating);
                AddButton(ControlID.HOME_PANEL, ControlID.KERNEL_BUTTON, "Buttons\\StopKernelUnpressed-128.png", "Buttons\\StartKernelUnpressed-128.png", 0, 210, 128, "Start Kernel", ButtonType.Alternating);


                //Add top status bar information
                statusLabel = new AlphaLabel();
                statusLabel.Size = new Size(300, 35);
                statusLabel.Text = "Kernel Stopped";
                statusLabel.ForeColor = Color.FromArgb(250, 237, 221);
                statusLabel.Font = new Font(FontFamily.GenericSerif, 8.0f, System.Drawing.FontStyle.Bold);
                statusLabel.Visible = true;
                statusLabel.Location = new Point(1, 1);
                this.panels[ControlID.HOME_PANEL].Controls.Add(statusLabel);

                //Settings Bottom  Buttons
                AddButton(ControlID.SETTINGS_PANEL, ControlID.BACK_BUTTON, "Buttons\\BackPressed.png", "Buttons\\BackUnpressed.png", 310, this.Height - 130, 128, null, ButtonType.Fixed);

                //Settings Buttons
                AddButton(ControlID.SETTINGS_PANEL, ControlID.BLUETOOTH_BUTTON, "Buttons\\BluetoothPressed.png", "Buttons\\BluetoothUnpressed.png", 0, 50, 128, "Wockets", ButtonType.Fixed);
                AddButton(ControlID.SETTINGS_PANEL, ControlID.SOUND_BUTTON, "Buttons\\SoundPressed.png", "Buttons\\SoundUnpressed.png", 160, 50, 128, "Sound", ButtonType.Fixed);

                //Wockets Screen

                AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_BACK_BUTTON, "Buttons\\Back48Pressed.png", "Buttons\\Back48Unpressed.png", 400, this.Height - 48, 48, null, ButtonType.Fixed);
                AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_UP_BUTTON, "Buttons\\Up48Pressed.png", "Buttons\\Up48Unpressed.png", 250, this.Height - 48, 48, null, ButtonType.Fixed);
                AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_DOWN_BUTTON, "Buttons\\Down48Pressed.png", "Buttons\\Down48Unpressed.png", 180, this.Height - 48, 48, null, ButtonType.Fixed);
                AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_RELOAD_BUTTON, "Buttons\\BluetoothReloadPressed-48.png", "Buttons\\BluetoothReloadUnpressed-48.png", 20, this.Height - 48, 48, null, ButtonType.Fixed);


                wocketsList = new WocketSlidingList();
                wocketsList.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
                wocketsList.Location = new Point(0, 0);
                this.panels[ControlID.WOCKETS_PANEL].Controls.Add(wocketsList);
                wocketsList.BringToFront();


                //Wockets Configuration Panel

                //AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_BLUETOOTH_BUTTON, "Buttons\\BluetoothUnpressed-64.png", "Buttons\\BluetoothPressed-64.png", 0, this.Height - 64, 64, null, ButtonType.Fixed);
                //AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_COMMAND_BUTTON, "Buttons\\CommandPressed-64.png", "Buttons\\CommandUnpressed-64.png", 80, this.Height - 64, 64, null, ButtonType.Fixed);
                //AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_TIMERS_BUTTON, "Buttons\\TimerPressed-64.png", "Buttons\\TimerUnpressed-64.png", 160, this.Height - 64, 64, null, ButtonType.Fixed);
                //AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_STATUS_BUTTON, "Buttons\\StatusPressed-64.png", "Buttons\\StatusUnpressed-64.png", 240, this.Height - 64, 64, null, ButtonType.Fixed);
                //AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_INFORMATION_BUTTON, "Buttons\\InformationPressed-64.png", "Buttons\\InformationUnpressed-64.png", 320, this.Height - 64, 64, null, ButtonType.Fixed);
                //AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_BACK_BUTTON, "Buttons\\Back64Pressed.png", "Buttons\\Back64Unpressed.png", 400, this.Height - 64, 64, null,  ButtonType.Fixed);

                bluetoothPanel = new Panel();
                bluetoothPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
                bluetoothPanel.Visible = true;
                bluetoothPanel.BackColor = Color.FromArgb(245, 219, 186);
                bluetoothName = new Label();
                bluetoothName.Location = new Point(10, 10);
                bluetoothName.Size = new Size(250, 40);
                bluetoothName.Font = new Font(FontFamily.GenericSansSerif, 14.0f, System.Drawing.FontStyle.Underline | System.Drawing.FontStyle.Bold);
                bluetoothPanel.Controls.Add(bluetoothName);
                this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Controls.Add(bluetoothPanel);

                //Plotter Panel
                AddButton(ControlID.PLOTTER_PANEL, ControlID.WOCKETS_BACK_BUTTON, "Buttons\\Back48Pressed.png", "Buttons\\Back48Unpressed.png", 400, this.Height - 48, 48, null, ButtonType.Fixed);
                plotterPanel = new Panel();
                plotterPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
                plotterPanel.Visible = true;
                plotterPanel.BackColor = Color.FromArgb(250, 237, 221);//Color.FromArgb(245, 219, 186);
                plotterPanel.Paint += new PaintEventHandler(plotterPanel_Paint);
                plotterTimer = new System.Windows.Forms.Timer();
                plotterTimer.Interval = 50;
                plotterTimer.Tick += new EventHandler(plotterTimer_Tick);

                this.panels[ControlID.PLOTTER_PANEL].Controls.Add(plotterPanel);


                for (int i = 0; (i < ControlID.NUMBER_PANELS); i++)
                {
                    //cache panels with drawn backgrounds
                    //this._backBuffers[i] = new Bitmap(480, 640, PixelFormat.Format32bppRgb);
                    if (this.panels[i]._Background != null)
                    {
                        Graphics offscreen = Graphics.FromImage(this.panels[i]._Backbuffer);
                        offscreen.DrawImage(this.panels[i]._Background, 0, 0);
                    }
                    this.panels[i].Initialize();
                }

                this.panels[currentPanel].Location = new Point(0, 0);
                this.panels[currentPanel].Update();
                this.panels[currentPanel].Visible = true;

                this.Deactivate += new EventHandler(Form1_Deactivate);
                this.Activated += new EventHandler(Form1_Activated);



            }

            void doneEE_Click(object sender, EventArgs e)
            {
                if (MessageBox.Show("Are you done measuring?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                {
                    this.activityStatus = ActivityStatus.None;
                    this.panels[ControlID.HOME_PANEL].Visible = true;
                    //this.panels[ControlID.EE_PANEL].Visible = false;
                    this.panels[ControlID.CLASSIFICATION_PANEL].Visible = false;
                    this.currentPanel = ControlID.HOME_PANEL;
                }
            }

            void doneClassifying_Click(object sender, EventArgs e)
            {
                if (MessageBox.Show("Are you done measuring?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                {
                    this.activityStatus = ActivityStatus.None;

                    for (int i = 0; i < activityButtons.Count; i++)
                    {
                        System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                        for (int j = 0; j < activityList.Length; j++)
                            this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Remove(activityList[j]);
                    }
                    foreach (Label l in classifiedLabels.Values)
                        this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Remove(l);

                    activityButtons.Clear();
                    this.panels[ControlID.HOME_PANEL].Visible = true;
                    this.panels[ControlID.CLASSIFICATION_PANEL].Visible = false;
                    this.currentPanel = ControlID.HOME_PANEL;
                    //if (this.saveFeatures.Checked)
                    CleanupML();
                    //remove all existing labels


                }
            }

       #endregion 


        #region Wockets Kernel Functions


        private void LoadWockets()
        {

            if (!Core._KernalStarted)
            {
                if (!Core.Start())
                    MessageBox.Show("Failed to start kernel");
                else
                    Thread.Sleep(5000);
            }
            else
            {
                //Make sure no kernels are running
                if (Core.Terminate())
                {
                    if (!Core.Start())
                        MessageBox.Show("Failed to start kernel");
                    else
                        Thread.Sleep(5000);
                }
                else
                    MessageBox.Show("Failed to shutdown kernel");

            }

            Thread.Sleep(5000);
            Core.Ping();
        }


        delegate void UpdateFormCallback(KernelResponse response);
        /// <summary>
        /// Handles kernel response events
        /// </summary>
        /// <param name="rsp"></param>
        private void EventListener(KernelResponse rsp)
        {
            try
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.InvokeRequired || this.InvokeRequired)
                {
                    UpdateFormCallback d = new UpdateFormCallback(EventListener);
                    this.Invoke(d, new object[] { rsp });
                }
                else
                {

                    switch (rsp)
                    {
                        case KernelResponse.STARTED:
                        case KernelResponse.PING_RESPONSE:                           
                            this.statusLabel.Text = "Registering";     
                            Core.Register();
                            break;
                        case KernelResponse.REGISTERED:
                            this.statusLabel.Text = "Registered";
                            break;
                        case KernelResponse.SENSORS_UPDATED:
                            this.statusLabel.Text = "Sensors selected";
                            break;
                        case KernelResponse.DISCOVERED:
                            this.statusLabel.Text = "Discovered";
                            UpdatewWocketsList(); 
                            break; 
                        case KernelResponse.CONNECTED:

                            this.statusLabel.Text = "Connected";

                            #region commented
                            //UpdatePlotter();
                            //this.currentStatus = "Connected";
                            //UpdateStatus();
                            #endregion 

                            if (plotter != null)
                            {
                                plotterTimer.Enabled = false;
                                plotter.Dispose();
                            }
                            plotterPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
                            plotter = new WocketsScalablePlotter(plotterPanel);
                            plotterPanel.Visible = true;
                            plotterTimer.Enabled = true;
                    

                            //if the activity protocol is already selected, copy it and load it after connecting
                            if (this.selectedActivityProtocol != -1)
                            {
                                if (File.Exists(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName))
                                {
                                    File.Copy(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName,
                                           Core._StoragePath + "\\ActivityLabelsRealtime.xml");
                                    this.annotatedSession = new Session();
                                    annotatedSession.FromXML(Core._StoragePath + "\\ActivityLabelsRealtime.xml");

                                    if (this._SaveFeatures)
                                        InitializeML();
                                }
                            }


                            //Initialize the sound notifications
                            soundThread = new Thread(new ThreadStart(SoundThread));
                            soundThread.Start();            
                            break;

                        case KernelResponse.DISCONNECTED:
                            Core._Connected = false;
                            this.selectedActivityProtocol = -1;
                            this.statusLabel.Text = "Disconnected";

                            #region commented
                            //this.currentStatus = "Ready to connect";
                            //UpdateStatus();
                            #endregion

                            //if you disconnect stop and cleanup the ML and save any existing arff file
                            CleanupML();

                            if (soundThread != null)
                            {
                                soundThread.Abort();
                                soundThread = null;
                            }
                            break;

                        default:
                            break;
                    }

                    this.Refresh();

                }
            }
            catch
            {
            }
        }



        #endregion 


        #region Algorithm Related Functions

        delegate void UpdateExamplesCallback();
        public void UpdateExamples()
        {
            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.examplesLabel.InvokeRequired)
                {
                    UpdateExamplesCallback d = new UpdateExamplesCallback(UpdateExamples);
                    this.Invoke(d, new object[] { });
                }
                else
                {

                    this.examplesLabel.Text = this.trainingExamples.ToString();
                }
            }
        }

        private void InitializeML()
        {

            //FullFeatureExtractor.Initialize(selectedWockets.Count, 90, CurrentWockets._Configuration, this.annotatedSession.OverlappingActivityLists[0]);
            //FullFeatureExtractor.Initialize3(selectedWockets.Count, 90, CurrentWockets._Configuration, this.annotatedSession.OverlappingActivityLists[0]);

            //Create the feature vector structure
            fv = new SimpleFeatureVector(selectedWockets.Count, 128, 90);


            if (trainingTW == null)
            {
                //Initialize the arff file (where the features are storaged)
                arffFileName = Core._StoragePath + "\\output" + DateTime.Now.ToString().Replace('/', '_').Replace(':', '_').Replace(' ', '_') + ".arff";
                trainingTW = new StreamWriter(arffFileName);

                //Add the arff headers
                trainingTW.WriteLine("@RELATION wockets");
                string arffHeader = fv.GetHeader();
                arffHeader += "\n@ATTRIBUTE activity {";
                int i = 0;
                for (i = 0; (i < ((this.annotatedSession.OverlappingActivityLists[0]).Count - 1)); i++)
                    arffHeader += this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + ",";
                arffHeader += this.annotatedSession.OverlappingActivityLists[0][i]._Name.Replace(' ', '_') + "}\n";
                arffHeader += "\n@DATA\n\n";
                trainingTW.WriteLine(arffHeader);


                string structureArffFile = Core._StoragePath + "\\structure.arff";
                structureTW = new StreamWriter(structureArffFile);
                structureTW.WriteLine("@RELATION wockets");
                structureTW.WriteLine(arffHeader);

                //Initialize the activity recognition thread
                mlThread = new Thread(new ThreadStart(MLThread));
                mlThread.Start();


            }

        }

        private void CleanupML()
        {
            if (mlThread != null)
            {
                mlThread.Abort();
                mlThread = null;
            }

            if (classificationThread != null)
            {
                classificationThread.Abort();
                classificationThread = null;
            }

            if (trainingTW != null)
            {
                trainingTW.Flush();
                trainingTW.Close();
                trainingTW = null;
            }

            if (structureTW != null)
            {
                structureTW.Flush();
                structureTW.Close();
                structureTW = null;
            }


            if (fv != null)
                fv.Cleanup();


            //Save any existing arff files
            if ((this._SaveFeatures) && (arffFileName != ""))
            {
                Keyboard.KeyboardOpen = true;
                Thread.Sleep(2000);
                string title = Microsoft.VisualBasic.Interaction.InputBox("Please type a name for this session", "Session Name", "", 50, 300);


                if (title != "")
                {
                    models = new AnnotationProtocolList();
                    if (File.Exists(Constants.PATH + "models.xml"))
                        models.FromXML(Constants.PATH + "models.xml");


                    AnnotationProtocol protocol = new AnnotationProtocol();
                    protocol._Name = title;
                    protocol._FileName = arffFileName;
                    protocol._Description = "";
                    models.Add(protocol);

                    TextWriter tw = new StreamWriter(Constants.PATH + "models.xml");
                    tw.WriteLine(models.ToXML());
                    tw.Close();
                    arffFileName = "";
                }
            }
        }

        
        int trainingExamples = 0;
        double windowLength = 0;
        long[] lastTotalSamples;
        int[] last_extracted;
        int[] no_fv_iterations;

        private void MLThread()
        {

            int structureFileExamples = 0;
            string prev_activity = "";
            lastTotalSamples = new long[CurrentWockets._Controller._Decoders.Count];
            last_extracted = new int[CurrentWockets._Controller._Decoders.Count];
            no_fv_iterations = new int[CurrentWockets._Controller._Decoders.Count];
            bool extracted = false;
            while (true)
            {
                string current_activity = "unknown";
                lock (annotationLock)
                {
                    if (this.currentRecord != null)
                        current_activity = this.currentRecord.Activities._CurrentActivity;
                }

                //Check if each decoder decoded the desired number of samples
                bool readyFV = true;
                for (int i = 0; (i < CurrentWockets._Controller._Decoders.Count); i++)
                {
                    long numNewSamples = CurrentWockets._Controller._Decoders[i].TotalSamples - lastTotalSamples[i];
                    if (numNewSamples == 0)
                    {
                        readyFV = false;
                    }
                    else if (numNewSamples < fv._Length)
                    {
                        if (no_fv_iterations[i] > 7) // a disconnection occurred, so reset the window you are looking at
                        {
                            //reinitialize all
                            for (int j = 0; (j < CurrentWockets._Controller._Decoders.Count); j++)
                                no_fv_iterations[j] = 0;
                        }
                        readyFV = false;
                        no_fv_iterations[i] = no_fv_iterations[i] + 1;
                        break;
                    }
                }

                if (!readyFV)
                {
                    Thread.Sleep(1000);
                    continue;
                }

                extracted = fv.Extract();

                for (int i = 0; (i < CurrentWockets._Controller._Decoders.Count); i++)
                    lastTotalSamples[i] = CurrentWockets._Controller._Decoders[i].TotalSamples;

                if (current_activity != "unknown")
                {
                    //skip boundary don't use it
                    if ((prev_activity == current_activity) && (extracted))
                    {
                        string arffSample = fv.toString() + "," + current_activity;
                        trainingTW.WriteLine(arffSample);
                        if (structureFileExamples < 10)
                        {
                            structureTW.WriteLine(arffSample);
                            structureFileExamples++;
                        }
                        trainingExamples++;
                        UpdateExamples();
                    }
                    if (prev_activity != current_activity)
                        trainingExamples = 0;
                    prev_activity = current_activity;

                }
                Thread.Sleep(1000);
            }
        }


        #endregion


        #region commented
        /*delegate void UpdateStatusCallback();
        public void UpdateStatus()
        {

            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.statusLabel.InvokeRequired)
                {
                    UpdateStatusCallback d = new UpdateStatusCallback(UpdateStatus);
                    this.Invoke(d, new object[] { });

                }
                else
                {
                    this.statusLabel.Text = this.currentStatus;
                    this.Refresh();
                }
                
            }

        }*/

        /*delegate void UpdatePlotterCallback();
        public void UpdatePlotter()
        {

            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.plotterPanel.InvokeRequired)
                {
                    UpdatePlotterCallback d = new UpdatePlotterCallback(UpdatePlotter);
                    this.Invoke(d, new object[] { });

                }
                else
                {

                    if (plotter != null)
                    {
                        plotterTimer.Enabled = false;
                        plotter.Dispose();
                    }
                    plotterPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
                    plotter = new WocketsScalablePlotter(plotterPanel);
                    plotterPanel.Visible = true;
                    plotterTimer.Enabled = true;
                    
                        
                }
            }

        }*/
        #endregion commented


        #region Classification Related Functions

        double totalCalories = 0.0;
        double prevHrs;
        int reps = 0;
        delegate void UpdateTimerCallback();
        public void UpdateTimer()
        {
            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.panels[ControlID.CLASSIFICATION_PANEL].InvokeRequired)
                {
                    UpdateTimerCallback d = new UpdateTimerCallback(UpdateTimer);
                    this.Invoke(d, new object[] {  });
                }
                else
                {

                    this.panels[ControlID.CLASSIFICATION_PANEL].Refresh();
                    /*TimeSpan ts = TimeSpan.FromSeconds(activityTimer.Ticks);
                    ((Label)this.classifiedLabels["timer"]).Text = "Time Elapsed: "+ ts.Hours.ToString("00") + ":" + ts.Minutes.ToString("00") + ":" + ts.Seconds.ToString("00");
                    double hrs = (ts.Hours + ts.Minutes / 60.0 + ts.Seconds / 3600.0);
                    double difference=(hrs - prevHrs);
                    if (difference>0)
                        totalCalories += (kcal_kg_hr * kgs * difference);
                    prevHrs = hrs;
                    ((Label)this.classifiedLabels["kcals"]).Text = "Calories Burned: " + totalCalories.ToString("0.0");
                     */
                    //((Label)this.classifiedLabels["reps"]).Text = "Reps: " +reps;
                    //pieChart.SetTime(ts.Hours,ts.Minutes,ts.Seconds);
                    //pieChart.Invalidate();
                    this.panels[ControlID.CLASSIFICATION_PANEL].Invalidate();
                }
            }

        }

        string prevActivity="no-activity";
        delegate void UpdateClassificationCallback(string activity,double intensity);
        public void UpdateClassification(string activity,double color)
        {
            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (this.panels[ControlID.CLASSIFICATION_PANEL].InvokeRequired)
                {
                    UpdateClassificationCallback d = new UpdateClassificationCallback(UpdateClassification);
                    this.Invoke(d, new object[] {activity,color });
                }
                else
                {
                    
                    ((Label)this.classifiedLabels[activity]).ForeColor = Color.FromArgb((int)(250 * color), (int)(237 * color), (int)(221 * color));
                    ((Label)this.classifiedLabels[activity]).Invalidate();

                    #region commented
                    /*if (prevActivity != activity)
                    {
                        ((AlphaPictureBox)this.activityPictures[activity]).Visible = true;
                        if (prevActivity == "Reconnecting")
                            ((AlphaPictureBox)this.activityPictures["no-activity"]).Visible = false;
                        else
                            ((AlphaPictureBox)this.activityPictures[prevActivity]).Visible = false;
                        prevActivity = activity;
                        if (color == 1)
                        {
                            ((Label)this.classifiedLabels["classification"]).Text = "Reconnecting...";
                            ((Label)this.classifiedLabels["classification"]).ForeColor = Color.Red;
                            prevActivity = "Reconnecting";
                        }
                        else
                        {
                            if (activity=="no-activity")
                                ((Label)this.classifiedLabels["classification"]).ForeColor = Color.Black;
                            else
                                ((Label)this.classifiedLabels["classification"]).ForeColor = Color.Green;
                            ((Label)this.classifiedLabels["classification"]).Text = "Now: " + activity;
                        }
                        ((Label)this.classifiedLabels["classification"]).Invalidate();
                        this.panels[ControlID.CLASSIFICATION_PANEL].Refresh();
                    }*/
                    //pieChart.SetActivity(activity);                    
                    //pieChart.Invalidate();
                    //this.panels[ControlID.EE_PANEL].Invalidate();
                    #endregion


                }
            }

        }

        int[] labelCounters=null;
        J48 classifier = null;
        FastVector fvWekaAttributes;
        Instances instances=null;
        string[] activityLabels=null;
        Hashtable labelIndex ;
        private Thread classificationThread = null;
        int classificationCounter = 0;
        int kgs = 80;
        double kcal_kg_hr = 0;
        string mets = "?";
    

        private void ClassificationThread()
        {
            string previousActivity = "";
            int missedExtractions = 0;
            bool extracted = false;


            lastTotalSamples = new long[CurrentWockets._Controller._Decoders.Count];
            last_extracted = new int[CurrentWockets._Controller._Decoders.Count];
            no_fv_iterations = new int[CurrentWockets._Controller._Decoders.Count];


            while (true)
            {

                //Check if each decoder decoded the desired number of samples
                bool readyFV = true;
                for (int i = 0; (i < CurrentWockets._Controller._Decoders.Count); i++)
                {
                    long numNewSamples = CurrentWockets._Controller._Decoders[i].TotalSamples - lastTotalSamples[i];
                    if (numNewSamples == 0)
                        readyFV = false;
                    else if (numNewSamples < (fv._Length/2))
                    {
                        if (no_fv_iterations[i] > 7) // a disconnection occurred, so reset the window you are looking at
                        {
                            //reinitialize all
                            for (int j = 0; (j < CurrentWockets._Controller._Decoders.Count); j++)
                                no_fv_iterations[j] = 0;
                        }
                        readyFV = false;
                        no_fv_iterations[i] = no_fv_iterations[i] + 1;
                        break;
                    }
                }

                if (!readyFV)
                {
                    Thread.Sleep(1000);
                    missedExtractions++;
                    //if (missedExtractions>6)
                      //  UpdateClassification("no-activity", 1); 
                    continue;
                }

                extracted = fv.Extract();

                for (int i = 0; (i < CurrentWockets._Controller._Decoders.Count); i++)
                    lastTotalSamples[i] = CurrentWockets._Controller._Decoders[i].TotalSamples;


                if (extracted)
                {
                    missedExtractions = 0;
                    Instance newinstance = new Instance(instances.numAttributes());
                    newinstance.Dataset = instances;
                    for (int i = 0; (i < fv._Values.Length); i++)
                        newinstance.setValue(instances.attribute(i), fv._Values[i]);
                    double predicted = classifier.classifyInstance(newinstance);
                    string predicted_activity = newinstance.dataset().classAttribute().value_Renamed((int)predicted);

                    int currentIndex = (int)labelIndex[predicted_activity];
                    labelCounters[currentIndex] = (int)labelCounters[currentIndex] + 1;
                    classificationCounter++;

                    if (classificationCounter >= 5) //CurrentWockets._Configuration._SmoothWindowCount)
                    {

                        int mostCount = -1;
                        string mostActivity = "";
                        //Color indicate;
                        //int level;
                        for (int j = 0; (j < labelCounters.Length); j++)
                        {
                            // level = 240 - 240 * labelCounters[j] / configuration._SmoothWindows;
                            //indicate = Color.FromArgb(level, level, level);
                            //this.ActGUIlabels[j].ForeColor = indicate;
                            //this.ActGUIlabels[j].Invalidate();
                            double intensity = (1.0 - ((double)labelCounters[j] / (double)5));                            
                            UpdateClassification(activityLabels[j], intensity);
                            if (labelCounters[j] > mostCount)
                            {
                                mostActivity = activityLabels[j];
                                mostCount = labelCounters[j];
                            }


                            labelCounters[j] = 0;
                        }

                       /* if (previousActivity != mostActivity)
                        {
                            this.activityTimer.stop();
                            this.activityTimer.reset();
                            this.activityTimer.start();
                        }*/

                        UpdateClassification(mostActivity, 0);

                        if (mostActivity == "walking")
                        {
                            mets = "3.1 KCals/min";
                            kcal_kg_hr = 2; //3 METs
                        }
                        else if (mostActivity == "running")
                        {
                            mets = "3.8 KCals/min";
                            kcal_kg_hr = 4; // 6 METs
                        }
                        else if (mostActivity == "jumping-jacks")
                        {
                            mets = "8 KCals/min";
                            kcal_kg_hr = 6; // 8 METs
                        }
                        else if (mostActivity == "bicycling")
                        {
                            mets = "1 KCals/min";
                            kcal_kg_hr = 5; // 8 METs
                        }
                        else if (mostActivity == "no-activity")
                        {
                            mets = "1.8 KCals/min";
                            kcal_kg_hr = 1.0; // 
                        }
                        else if (mostActivity == "biceps-curls")
                        {
                            mets = "1.8 KCals/min";
                            kcal_kg_hr = 1.8; // 1 METs
                        }
                        else if (mostActivity == "pushups")
                        {
                            mets = "3.2 KCals/min";
                            kcal_kg_hr = 3.2; // 1 METs
                        }
                        else
                        {
                            mets = "1.0 KCals/min";
                            kcal_kg_hr = 1.0; // 1 METs
                        }
                        classificationCounter = 0;
                        previousActivity = mostActivity;
                    }
                    UpdateTimer();
                }
                //else if (missedExtractions > 5)                
                    
                //else
                  //  missedExtractions++;
                
                Thread.Sleep(500);
            }
        }

        private void ClassificationThread3()
        {
            int window_size=512;//Get from FullFeature
            long[] last_extracted = new long[CurrentWockets._Controller._Decoders.Count];
            int[] no_fv_iterations = new int[CurrentWockets._Controller._Decoders.Count];

            for (int i = 0; (i < CurrentWockets._Controller._Decoders.Count); i++)
            {
                last_extracted[i] = CurrentWockets._Controller._Decoders[i].TotalSamples;
                no_fv_iterations[i] = 0;
            }

            while (true)
            {
                //Check if each decoder decoded the desired number of samples
                bool readyFV = true;
                for (int i = 0; (i<CurrentWockets._Controller._Decoders.Count); i++)
                {
                    long numNewSamples = CurrentWockets._Controller._Decoders[i].TotalSamples - last_extracted[i];
                    if ((numNewSamples>0) && (numNewSamples < window_size))
                    {
                        if (no_fv_iterations[i]>7) // a disconnection occurred, so reset the window you are looking at
                            last_extracted[i] = CurrentWockets._Controller._Decoders[i].TotalSamples;
                        readyFV = false;
                        no_fv_iterations[i] = no_fv_iterations[i] + 1;
                        break;
                    }                                                            
                }

                // Here we are ready to do the feature extraction because we have collected
                // sufficient data from all sensors
                if (readyFV)
                {
                    //Copy the last 512 elements along with the new data
                    FullFeatureExtractor.StoreWocketsWindow3();

                    //Generate the feature vector without any checks on quality, because we are
                    //doing it on recently collected data
                    FullFeatureExtractor.GenerateFeatureVector3();

                    Instance newinstance = new Instance(instances.numAttributes());
                    newinstance.Dataset = instances;
                    for (int i = 0; (i < FullFeatureExtractor.Features.Length); i++)
                        newinstance.setValue(instances.attribute(i), FullFeatureExtractor.Features[i]);
                    double predicted = classifier.classifyInstance(newinstance);
                    string predicted_activity = newinstance.dataset().classAttribute().value_Renamed((int)predicted);

                    int currentIndex = (int)labelIndex[predicted_activity];
                    labelCounters[currentIndex] = (int)labelCounters[currentIndex] + 1;
                    classificationCounter++;

                    if (classificationCounter >= CurrentWockets._Configuration._SmoothWindowCount)
                    {
                        int mostCount = 0;
                        string mostActivity = "";
                        //Color indicate;
                        //int level;
                        for (int j = 0; (j < labelCounters.Length); j++)
                        {
                            // level = 240 - 240 * labelCounters[j] / configuration._SmoothWindows;
                            //indicate = Color.FromArgb(level, level, level);
                            //this.ActGUIlabels[j].ForeColor = indicate;
                            //this.ActGUIlabels[j].Invalidate();
                            double intensity = (1.0 - ((double)labelCounters[j] / (double)CurrentWockets._Configuration._SmoothWindowCount));
                            //((Label)this.classifiedLabels[activityLabels[j]]).ForeColor = Color.FromArgb((int) (250 *intensity) , (int)(237 * intensity), (int)(221 * intensity));
                            UpdateClassification(activityLabels[j], intensity);
                            if (labelCounters[j] > mostCount)
                            {
                                mostActivity = activityLabels[j];
                                mostCount = labelCounters[j];
                            }

                            //    UpdateClassification(mostActivity, intensity);                      
                            labelCounters[j] = 0;
                        }

                        classificationCounter = 0;


                    }

                    Thread.Sleep(1000);
                }
            }
        }

        #endregion



        #region Activity Prediction Related Functions
 
        private string modelDirectory = "";
        private Hashtable classifiedLabels;
        private Hashtable activityPictures;
        
        void startMeasuringButton_Click(object sender, EventArgs e)
        {
            //Copy the annotation file to the storage directory
            this.selectedModel = this.modelsList.SelectedIndices[0];
            if (!File.Exists(this.aModels[this.selectedModel]._FileName))
            {
                MessageBox.Show("Profile does not exist", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1);
                return; 
            }


            this.startMeasuringButton.Enabled = false;
            modelDirectory = this.aModels[this.selectedModel]._FileName.Substring(0, this.aModels[this.selectedModel]._FileName.LastIndexOf('\\'));
                
            this.annotatedSession = new Session();
            this.annotatedSession.FromXML(modelDirectory + "\\ActivityLabelsRealtime.xml");
            //CurrentWockets._Configuration = new WocketsConfiguration();//new DTConfiguration();
            //CurrentWockets._Configuration.FromXML(modelDirectory + "\\Configuration.xml");
            //CurrentWockets._Configuration._MemoryMode = MemoryConfiguration.SHARED;
            CurrentWockets._Controller = new WocketsController("", "", "");
            CurrentWockets._Controller._Mode = Wockets.MemoryMode.SharedToLocal;
            CurrentWockets._Controller.FromXML(modelDirectory + "\\SensorData.xml");
            CurrentWockets._Controller.Initialize();


            // 1- Make the classifier dependent on the samples rather than the actual sampling rate
            // 2- No need to spread the signal, assume equally spaced
            // 3- interpolate the signal to compute the FFT
            // 4- Do experiments on ideal window size
            // 5- Low Pass the data + Band Pass the data..
            // 6- Ensure that the decision tree is reloaded in the right order
            // 7- Add commonsense knowledge for the specific activities we are looking at
            // 8- Upload to the server the classification when there is a change
            // Bench Presses, JJs, Walking 2 intensities, No Activity, Curls
            // Common sense JJs ---> 2 sensors have to show motion
            // Curls -> 1 and only 1 sensor has to show motion            
            // No Activity -> No sensor should show signficant motion: very low movement on sensors
            // threshold based on activity count...
            
            
            // Restrictions: No Activity, other - No sensors should show signficant motion
            // - JJs : both Wrist and Ankle sensors have to show signficant motion
            // - Curls, Bench Press : Wrist has to show motion
            // - Walking: ankle has to show motion (2 intensities)

            //if no signficant motion -> No Activity   (could be resting between curls or presses)
            // else if signficant motion and consistent from the ankle then              
                //JJs or walking (Decision Tree)
            // else 
                // Curls or Presses (Decision Tree)
           
            //Smmo

            
            //FullFeatureExtractor.Initialize(CurrentWockets._Controller._Sensors.Count, 90, CurrentWockets._Configuration, this.annotatedSession.OverlappingActivityLists[0]);
            //FullFeatureExtractor.Initialize3(CurrentWockets._Controller._Sensors.Count, 90, CurrentWockets._Configuration, this.annotatedSession.OverlappingActivityLists[0]);
            fv = new SimpleFeatureVector(selectedWockets.Count, 128, 90);

           // this.annotatedSession = new Session();
           // this.annotatedSession.FromXML(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName);
            classifier = new J48();
            classifier.set_MinNumObj(5);
            classifier.set_ConfidenceFactor((float)0.25);
            if (!File.Exists(modelDirectory + "\\model.xml"))
            {
                instances = new Instances(new StreamReader(this.aModels[this.selectedModel]._FileName));
                instances.Class = instances.attribute(fv._Names.Length);
                classifier.buildClassifier(instances);
                TextWriter tc = new StreamWriter(modelDirectory + "\\model.xml");
                classifier.toXML(tc);
                tc.Flush();
                tc.Close();
            }
            else
            {
                instances = new Instances(new StreamReader(modelDirectory + "\\structure.arff"));
                instances.Class = instances.attribute(fv._Names.Length);
                classifier.buildClassifier(modelDirectory + "\\model.xml", instances);
            }


            fvWekaAttributes = new FastVector(fv._Names.Length + 1);
            for (int i = 0; (i < fv._Names.Length); i++)
                fvWekaAttributes.addElement(new weka.core.Attribute(fv._Names[i]));

            FastVector fvClassVal = new FastVector();
            labelCounters = new int[this.annotatedSession.OverlappingActivityLists[0].Count];
            activityLabels = new string[this.annotatedSession.OverlappingActivityLists[0].Count];
            //for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists[0].Count); i++)
           // {

            labelIndex = new Hashtable();
            for (int i = 0; (i < instances.classAttribute().numValues()); i++)
            {

                labelCounters[i] = 0;
                string activity = instances.classAttribute().value_Renamed(i);
                activityLabels[i] = activity;
                labelIndex.Add(activity, i);
                fvClassVal.addElement(activity);
            }

            classifiedLabels = new Hashtable();



            #region commented
            /*
            activityPictures = new Hashtable();

            AlphaPictureBox picture = new AlphaPictureBox();            
            picture.Name = "running";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH +"images\\" + picture.Name+".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);

            picture = new AlphaPictureBox();
            picture.Name = "bicycling";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);

            picture = new AlphaPictureBox();
            picture.Name = "walking";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);

            picture = new AlphaPictureBox();
            picture.Name = "biceps-curls";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);

            picture = new AlphaPictureBox();
            picture.Name = "jumping-jacks";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);

            picture = new AlphaPictureBox();
            picture.Name = "no-activity";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);


            picture = new AlphaPictureBox();
            picture.Name = "pushups";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);


            picture = new AlphaPictureBox();
            picture.Name = "exercise-1";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);

            picture = new AlphaPictureBox();
            picture.Name = "exercise-2";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);


            picture = new AlphaPictureBox();
            picture.Name = "exercise-3";
            picture.Size = new Size(240, 240);
            picture.Image = AlphaImage.CreateFromFile(Constants.PATH + "images\\" + picture.Name + ".gif");
            picture.Visible = false;
            picture.Location = new Point(40, 90);
            activityPictures.Add(picture.Name, picture);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(picture);
            */
            /*
            Label label = new Label();
            label.Size = new Size(500, 100);
            label.Text = "";
            label.BackColor = Color.FromArgb(250, 237, 221);
            label.ForeColor = Color.Black;
            label.Font = new Font(FontFamily.GenericSerif, 16.0f, System.Drawing.FontStyle.Bold);
            label.Visible = true;
            label.Location = new Point(30, this.Height-450);
            classifiedLabels.Add("classification", label);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(label);
            */
            /*
            label = new Label();
            label.Size = new Size(500, 70);
            label.Text = "";
            label.BackColor = Color.FromArgb(250, 237, 221);
            label.ForeColor = Color.Black;
            label.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
            label.Visible = true;
            label.Location = new Point(30, this.Height - 320);
            classifiedLabels.Add("kcals", label);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(label);

            label = new Label();
            label.Size = new Size(500, 70);
            label.Text = "";
            label.BackColor = Color.FromArgb(250, 237, 221);
            label.ForeColor = Color.Black;
            label.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
            label.Visible = true;
            label.Location = new Point(30, this.Height - 250);
            classifiedLabels.Add("timer", label);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(label);


            label = new Label();
            label.Size = new Size(500, 70);
            label.Text = "";
            label.BackColor = Color.FromArgb(250, 237, 221);
            label.ForeColor = Color.Black;
            label.Font = new Font(FontFamily.GenericSerif, 14.0f, System.Drawing.FontStyle.Bold);
            label.Visible = true;
            label.Location = new Point(30, this.Height - 180);
            classifiedLabels.Add("reps", label);
            this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(label);
            */
            #endregion 




            //add the labels to the interface
            int yLocation=40;
          
            
            for (int i = 0; (i < instances.classAttribute().numValues()); i++)
            {
                string activity= instances.classAttribute().value_Renamed(i);
                Label label = new Label();
                label.Size = new Size(500, 60);
                label.Text = activity;
                label.BackColor = Color.FromArgb(250, 237, 221);
                label.ForeColor = Color.FromArgb(250, 237, 221);
                label.Font = new Font(FontFamily.GenericSerif, 16.0f, System.Drawing.FontStyle.Bold);
                label.Visible = true;
                label.Location = new Point(10,yLocation );

                classifiedLabels.Add(activity, label);
                this.panels[ControlID.CLASSIFICATION_PANEL].Controls.Add(label);
                yLocation += 70;
            }
            this.activityStatus = ActivityStatus.Measuring;
           
            this.panels[ControlID.CLASSIFICATION_PANEL].Visible = true;
            this.panels[currentPanel].Visible = false;
            this.currentPanel = ControlID.CLASSIFICATION_PANEL;
            
            /*this.panels[ControlID.EE_PANEL].Visible = true;
            this.panels[currentPanel].Visible = false;
            this.currentPanel = ControlID.EE_PANEL;
            */

            classificationCounter = 0;
            classificationThread = new Thread(new ThreadStart(ClassificationThread));
            classificationThread.Start();

           
        }

        private int selectedModel = -1;
        void modelsList_SelectedIndexChanged(object sender, EventArgs e)
        {
            this.selectedModel = -1;
            if ((!startMeasuringButton.Enabled) && (((ListView)sender).SelectedIndices.Count == 1))
                startMeasuringButton.Enabled = true;
            else
                startMeasuringButton.Enabled = false;
        }

        void doneAnnotation_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you done annotating?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                this.selectedActivityProtocol = -1;
                this.activityStatus = ActivityStatus.None;

                for (int i = 0; i < activityButtons.Count; i++)
                {
                    System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                    for (int j = 0; j < activityList.Length; j++)
                        this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Remove(activityList[j]);
                }
                activityButtons.Clear();
                this.panels[ControlID.HOME_PANEL].Visible = true;
                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Visible = false;
                //if (this.saveFeatures.Checked)
                CleanupML();
                this.currentPanel = ControlID.HOME_PANEL;
            }
        }

        void annotateActivityButton_Click(object sender, EventArgs e)
        {
            throw new NotImplementedException();
        }

        void measureActivityButton_Click(object sender, EventArgs e)
        {
            throw new NotImplementedException();
        }


        private bool _SaveData = false;
        void saveData_CheckStateChanged(object sender, EventArgs e)
        {
            _SaveData = ((CheckBox)sender).Checked;
        }

        private bool _SaveFeatures = true;
        void saveFeatures_CheckStateChanged(object sender, EventArgs e)
        {
            if (((CheckBox)sender).Checked)
                ((CheckBox)sender).Text = "Learn and Annotate";
            else
                ((CheckBox)sender).Text = "Annotate Only";
            _SaveFeatures = ((CheckBox)sender).Checked;
        }


        #endregion


        #region Annotation Related Functions

        private Session annotatedSession;
        private int selectedActivityProtocol=-1;
        private ActivityStatus activityStatus= ActivityStatus.None;
        private ArrayList activityButtons = new ArrayList();

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


        //truncate text if labels text is too long
        private String truncateText(String text)
        {

            int maxChars = 10;

            if (text.Length <= maxChars)
                return text;

            char[] delimiter = { ' ', '-', '/' };
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


        ArrayList selectedButtons = new ArrayList();
        char[] delimiter = { '_' };
        private Annotation currentRecord = null;
        private object annotationLock = new object();
        private void activityButton_Click(object sender, EventArgs e)
        {
            Button button = (Button)sender;
            string[] name = button.Name.Split('_');
            int category = Convert.ToInt32(name[0]);
            int index = Convert.ToInt32(name[1]);


            System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[category];
            for (int j = 0; j < activityList.Length; j++)
            {
                if (activityList[j].BackColor == Color.DodgerBlue)
                {
                    activityList[j].BackColor = Color.SkyBlue;
                    selectedButtons.Remove(activityList[j]);
                }
                else if (index == j)
                {
                    activityList[j].BackColor = Color.DodgerBlue;
                    selectedButtons.Add(activityList[j]);
                }
            }

            if (this.currentRecord != null)
            {
                lock (annotationLock)
                {
                    stopAnnotation();
                }
                TextWriter tw = new StreamWriter(Core._StoragePath + "\\AnnotationIntervals.xml");
                tw.WriteLine(this.annotatedSession.ToXML());
                tw.Close();
            }
            if (selectedButtons.Count > 0)
            {
                lock (annotationLock)
                {
                    startAnnotation();
                }
            }
        }


        ArrayList records = new ArrayList();

        private void startAnnotation()
        {
            this.currentRecord = new Annotation();
            this.currentRecord._StartDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            this.currentRecord._StartHour = DateTime.Now.Hour;
            this.currentRecord._StartMinute = DateTime.Now.Minute;
            this.currentRecord._StartSecond = DateTime.Now.Second;
            this.currentRecord._StartMillisecond = DateTime.Now.Millisecond;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._StartUnix = ts.TotalSeconds;

     
            if (this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Visible)
            {
                for (int i = 0; i < selectedButtons.Count; i++)
                {
                    System.Windows.Forms.Button but = (System.Windows.Forms.Button)selectedButtons[i];
                    string[] name = but.Name.Split('_');
                    int category = Convert.ToInt32(name[0]);
                    int index = Convert.ToInt32(name[1]);
                    this.currentRecord.Activities.Add(new Activity(this.annotatedSession.OverlappingActivityLists[category][index]._Name, this.annotatedSession.OverlappingActivityLists[category]._Name));
                }
            }
            //this.wocketsController.currentRecord = this.currentRecord;
        }

        private void stopAnnotation()
        {
            this.currentRecord._EndDate = DateTime.Now.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
            this.currentRecord._EndHour = DateTime.Now.Hour;
            this.currentRecord._EndMinute = DateTime.Now.Minute;
            this.currentRecord._EndSecond = DateTime.Now.Second;
            this.currentRecord._EndMillisecond = DateTime.Now.Millisecond;
            TimeSpan ts = (DateTime.Now - new DateTime(1970, 1, 1, 0, 0, 0));
            this.currentRecord._EndUnix = ts.TotalSeconds;
            this.annotatedSession.Annotations.Add(this.currentRecord);
            this.currentRecord = null;
            //this.wocketsController.currentRecord = null;

        }

        void startAnnnotationButton_Click(object sender, EventArgs e)
        {

            //Copy the annotation file to the storage directory
            this.selectedActivityProtocol = this.annotationProtocolsList.SelectedIndices[0];
            this.annotatedSession = new Session();
            this.annotatedSession.FromXML(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName);


            //this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Add(this.chooseActivityLabel);
            
            
            this.panels[ControlID.ANNOTATION_BUTTON_PANEL].AutoScroll = true;
            int max_buttons_per_row = 3;
            int act_button_width = 0;
            int act_button_height = 0;
            int numberOfButtons = 0;
            float fontSize = 12F;
            int act_button_x = 0;
            int act_button_y = 0;
            int marginHeight = 20;
            int screenWidth = this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Width;
            int screenHeight = this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Height;
            int scrollbarWidth = 28;

            for (int i = 0; (i < this.annotatedSession.OverlappingActivityLists.Count); i++)
            {
                Activity[] acts = this.annotatedSession.OverlappingActivityLists[i].ToArray();
                if (Platform.NativeMethods.GetPlatformType() == "PocketPC")
                {
                    System.Windows.Forms.Button[] buttons = new System.Windows.Forms.Button[acts.Length];

                    for (int j = 0; j < buttons.Length; j++)
                    {
                        buttons[j] = new System.Windows.Forms.Button();
                        MakeButtonMultiline(buttons[j]);
                        buttons[j].Name = i + "_" + j;
                        buttons[j].Text = truncateText(acts[j]._Name);
                        buttons[j].Click += new EventHandler(this.activityButton_Click);
                        buttons[j].BackColor = Color.SkyBlue;
                        buttons[j].ForeColor= Color.Black;
                        numberOfButtons += 1;
                    }
                    activityButtons.Add(buttons);
                }
            }

            if (numberOfButtons > 12)
            {
                max_buttons_per_row = 5;
                screenWidth -= scrollbarWidth;
                act_button_width = act_button_height = screenWidth / max_buttons_per_row;
            }
            else if ((numberOfButtons <= 12) && (numberOfButtons > 8))
            {
                max_buttons_per_row = 3;
                act_button_width = screenWidth / max_buttons_per_row;
                act_button_height = act_button_width + (act_button_width / 3);
            }
            else if ((numberOfButtons <= 8) && (numberOfButtons > 3))
            {
                max_buttons_per_row = 2; 
                act_button_width = (screenWidth - 10) / max_buttons_per_row;
                int numRows = (int)System.Math.Ceiling(numberOfButtons / 2.0);
                act_button_height = (screenHeight - 120) / numRows;
                fontSize = 12F;
            }
            else
            {
                int dBlockSize = screenWidth / max_buttons_per_row;
                max_buttons_per_row = 1;
                act_button_width = screenWidth - 2;
                act_button_height = (dBlockSize * 4) / numberOfButtons;
                fontSize = 14F;
            }

            if (Platform.NativeMethods.GetPlatformType() == "PocketPC")
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
                        activityList[j].Location = new System.Drawing.Point(act_button_x, act_button_y+40);
                        activityList[j].Font = new System.Drawing.Font("Microsoft Sans Serif", fontSize, System.Drawing.FontStyle.Regular | System.Drawing.FontStyle.Bold);
                        ((Panel)this.panels[ControlID.ANNOTATION_BUTTON_PANEL]).Controls.Add(activityList[j]);
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


            //if already connected copy the activity protocol
            if (Core._Connected)
            {
                if (File.Exists(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName))
                {
                    if (!File.Exists(Core._StoragePath + "\\ActivityLabelsRealtime.xml"))
                    {

                        File.Copy(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName,
                               Core._StoragePath + "\\ActivityLabelsRealtime.xml");
                        if (this.saveFeatures.Checked)
                            InitializeML();
                    }
                    else
                    {
                        if (MessageBox.Show("There is an existing annotation, would you like to overwrite it?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                        {
                            File.Copy(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName,
                               Core._StoragePath + "\\ActivityLabelsRealtime.xml", true);
                            this.annotatedSession = new Session();
                            annotatedSession.FromXML(Core._StoragePath + "\\ActivityLabelsRealtime.xml");
                            
                        }
                        else
                        {
                            this.selectedActivityProtocol = -1;
                            this.annotatedSession = null;
                            this.activityStatus = ActivityStatus.None;
                            for (int i = 0; i < activityButtons.Count; i++)
                            {
                                System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                                for (int j = 0; j < activityList.Length; j++)
                                    this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Remove(activityList[j]);
                            }
                            activityButtons.Clear();
                            return;
                        }
                    }
                    
                }
            }

            this.activityStatus = ActivityStatus.Annotating;
            this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Visible = true;
            this.panels[currentPanel].Visible = false;
            this.currentPanel = ControlID.ANNOTATION_BUTTON_PANEL;

            

            /*if (File.Exists(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName))
            {
                File.Copy(Constants.PATH + "ActivityProtocols\\" + this.aProtocols[this.selectedActivityProtocol]._FileName,
                       Core._StoragePath + "\\ActivityLabelsRealtime.xml");
                this.annotatedSession = new Session();
                annotatedSession.FromXML(Core._StoragePath + "\\ActivityLabelsRealtime.xml");
            }*/


            //add buttons to the interface


            

        }

        void annotationProtocolsList_SelectedIndexChanged(object sender, EventArgs e)
        {
            this.selectedActivityProtocol = -1;
            if ((!startAnnnotationButton.Enabled) && (((ListView)sender).SelectedIndices.Count == 1))
                startAnnnotationButton.Enabled = true;
            else
                startAnnnotationButton.Enabled = false;
            //throw new NotImplementedException();
        }


        #endregion 


        #region Mouse Click Handler

            void owner_MouseUp(object sender, MouseEventArgs e)
            {
                //if ((pushed)&& (clientArea.Contains(e.X, e.Y)))                   
                //    timeAnimation_Tick();            
                //this.pushed = false;

                if (this.panels[currentPanel]._UnpressedButtonControls != null)
                {
                    for (int i = 0; (i < this.panels[currentPanel]._UnpressedButtonControls.Length); i++)
                    {
                        if ((this.panels[currentPanel]._ButtonType[i] == ButtonType.Fixed) && (this.panels[currentPanel]._ButtonPressed[i]))
                        {
                            this.panels[currentPanel]._UnpressedButtonControls[i].Visible = true;
                            this.panels[currentPanel]._PressedButtonControls[i].Visible = false;
                            this.panels[currentPanel]._ButtonPressed[i] = false;
                        }

                    }
                }
            }

            void owner_MouseDown(object sender, MouseEventArgs e)
            {
                Control p = (Control)sender;
                if (!p.Enabled)
                    return;

                if ((!pushed) && (this.slidingPanels.Contains(currentPanel)))
                {
                    if (e.X < (Screen.PrimaryScreen.WorkingArea.Width / 3))
                    {
                        this.currentTransition = Transitions.LEFT_TO_RIGHT;
                        this.pushed = true;
                        this.clientArea = new Rectangle((Screen.PrimaryScreen.WorkingArea.Width / 2), e.Y - (Screen.PrimaryScreen.WorkingArea.Height / 5), Screen.PrimaryScreen.WorkingArea.Width, (Screen.PrimaryScreen.WorkingArea.Height / 5) * 2);
                    }
                    else if (e.X > (Screen.PrimaryScreen.WorkingArea.Width * (2 / 3)))
                    {
                        this.currentTransition = Transitions.RIGHT_TO_LEFT;
                        this.pushed = true;
                        this.clientArea = new Rectangle(0, e.Y - (Screen.PrimaryScreen.WorkingArea.Height / 5), (Screen.PrimaryScreen.WorkingArea.Width / 2), (Screen.PrimaryScreen.WorkingArea.Height / 5) * 2);
                    }
                }


                if (this.panels[currentPanel]._UnpressedButtonControls != null)
                {
                    for (int i = 0; (i < this.panels[currentPanel]._UnpressedButtonControls.Length); i++)
                    {

                        if (this.panels[currentPanel]._UnpressedButtonControls[i].HitTest(e.X, e.Y))
                        {
                            if ((this.panels[currentPanel]._ButtonType[i] == ButtonType.Fixed) && (!this.panels[currentPanel]._ButtonPressed[i]))
                            {
                                this.panels[currentPanel]._PressedButtonControls[i].Size = new Size(this.panels[currentPanel]._ButtonSize[i], this.panels[currentPanel]._ButtonSize[i]);
                                this.panels[currentPanel]._PressedButtonControls[i].Visible = true;
                                this.panels[currentPanel]._UnpressedButtonControls[i].Visible = false;
                                this.panels[currentPanel]._ButtonPressed[i] = true;
                                this.panels[currentPanel]._PressedButtonControls[i].Refresh();
                            }
                        }
                        else if ((this.panels[currentPanel]._ButtonType[i] == ButtonType.Fixed) && (this.panels[currentPanel]._ButtonPressed[i]))
                        {
                            this.panels[currentPanel]._UnpressedButtonControls[i].Size = new Size(this.panels[currentPanel]._ButtonSize[i], this.panels[currentPanel]._ButtonSize[i]);
                            this.panels[currentPanel]._UnpressedButtonControls[i].Visible = true;
                            this.panels[currentPanel]._PressedButtonControls[i].Visible = false;
                            this.panels[currentPanel]._ButtonPressed[i] = false;
                            this.panels[currentPanel]._UnpressedButtonControls[i].Refresh();

                        }
                    }
                }
                this.Refresh();

            }

            private void wocketClickHandler(object sender, EventArgs e)
            {
                WocketListItem wi = (WocketListItem)sender;
                int name = Convert.ToInt32(wi.Name);
                if ((wi.AddHitTest(wi.LastX, wi.LastY)) && !selectedWockets.Contains(wi))
                {
                    selectedWockets.Add(wi);
                    wi.BackColor = Color.FromArgb(205, 183, 158);
                }
                else if (wi.RemoveHitTest(wi.LastX, wi.LastY) && selectedWockets.Contains(wi))
                {
                    selectedWockets.Remove(wi);
                    wi.BackColor = Color.FromArgb(245, 219, 186);
                }
                selectedWockets.Sort();
                /* else                        
                 {
                     bluetoothName.Text = wi._Name;                
                     this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Visible = true;
                     this.panels[ControlID.WOCKETS_PANEL].Visible = false;
                     currentPanel = ControlID.WOCKETS_CONFIGURATION_PANEL;
                 }*/
            }
            
            public delegate void ClickHandler(object sender, EventArgs e);



            private double clickTime = 0;
            private Thread startupThread;

            private void clickHandler(object sender, EventArgs e)
            {
                AlphaPictureBox p = (AlphaPictureBox)sender;



                int name = Convert.ToInt32(p.Name);
                #region Activity Panel
                if (currentPanel == ControlID.ACTIVITY_PANEL)
                {
                    if (name == ControlID.HOME_ACTIVITY_BUTTON)
                    {

                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[currentPanel].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;

                    }
                    else if (name == ControlID.MEASURE_ACTIVITY_BUTTON)
                    {
                        this.panels[currentPanel].Visible = false;
                        this.panels[ControlID.MODELS_PANEL].Location = new Point(0, 0);
                        this.panels[ControlID.MODELS_PANEL].BringToFront();
                        this.panels[ControlID.MODELS_PANEL].Visible = true;
                        this.panels[ControlID.MODELS_PANEL].Dock = DockStyle.None;

                        //Load the most recent models list before showing the models panel
                        modelsList.Clear();
                        this.aModels = new AnnotationProtocolList();                    
                        if (File.Exists(Constants.PATH + "models.xml"))
                        {
                            this.aModels.FromXML(Constants.PATH + "models.xml");   
                            for (int i = 0; (i < this.aModels.Count); i++)                        
                                modelsList.Items.Add(new ListViewItem(this.aModels[i]._Name));                        
                        }

                        this.currentPanel = ControlID.MODELS_PANEL;
                    }
                    else if (name == ControlID.ANNOTATE_ACTIVITY_BUTTON)
                    {
                        this.panels[currentPanel].Visible = false;
                        this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Location = new Point(0, 0);
                        this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].BringToFront();
                        this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Visible = true;
                        this.panels[ControlID.ANNOTATION_PROTCOLS_PANEL].Dock = DockStyle.None;
                        this.currentPanel = ControlID.ANNOTATION_PROTCOLS_PANEL;
                    }
                }
                #endregion Activity Panel

                #region Annotation Protocols Panel
                else if (currentPanel == ControlID.MODELS_PANEL)
                {
                    if (name == ControlID.HOME_ANNOTATION_PROTOCOL_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[currentPanel].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                    }
                }
                #endregion Annotation Protocols Panel

                #region Annotation Protocols Panel
                else if (currentPanel == ControlID.ANNOTATION_PROTCOLS_PANEL)
                {
                    if (name == ControlID.HOME_ANNOTATION_PROTOCOL_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[currentPanel].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                    }
                }
                #endregion Annotation Protocols Panel

                #region Annotation Button Panel
                else if (currentPanel == ControlID.ANNOTATION_BUTTON_PANEL)
                {
                    if (name == ControlID.HOME_ANNOTATION_BUTTON_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                    }
                }
                #endregion Annotation Button Panel

                #region Classification Panel
                else if (currentPanel == ControlID.CLASSIFICATION_PANEL)
                {
                    if (name == ControlID.HOME_CLASSIFICATION_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[ControlID.CLASSIFICATION_PANEL].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                    }
                }
                #endregion Classification Panel
                #region EE Panel
                else if (currentPanel == ControlID.EE_PANEL)
                {
                    if (name == ControlID.HOME_EE_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[ControlID.EE_PANEL].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                    }
                }
                #endregion EE Panel
                else if (currentPanel == ControlID.WOCKETS_PANEL)
                {
                    if (name == ControlID.WOCKETS_BACK_BUTTON)
                    {                    
                        //this.panels[ControlID.SETTINGS_PANEL].Visible = true;
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[ControlID.WOCKETS_PANEL].Visible = false;
                        currentPanel = ControlID.HOME_PANEL;
                        ArrayList s = new ArrayList();
                        for (int i = 0; (i < selectedWockets.Count); i++)
                        {
                            s.Add(((WocketListItem)selectedWockets[i])._MacAddress);
                        }
                        Core.SetSensors(s);
                        //Core.SetSensorsAsync(s);
                    }
                    else if (name == ControlID.WOCKETS_UP_BUTTON)
                        wocketsList.MoveDown();
                    else if (name == ControlID.WOCKETS_DOWN_BUTTON)
                        wocketsList.MoveUp();
                    else if (name == ControlID.WOCKETS_RELOAD_BUTTON)
                    {
                        wocketsList._Location = 0;
                        wocketsList.Controls.Clear();     
                        wocketsList._Status = "Searching for Wockets...";
                        wocketsList.Refresh();
                        Core.Discover();
                    }
      
                }
                else if (currentPanel == ControlID.WOCKETS_CONFIGURATION_PANEL)
                {
                    if (name == ControlID.WOCKETS_CONFIGURATIONS_BACK_BUTTON)
                    {

                        this.panels[ControlID.WOCKETS_PANEL].Visible = true;
                        this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Visible = false;
                        this.currentPanel = ControlID.WOCKETS_PANEL;
                    }

                }

                else if (currentPanel == ControlID.HOME_PANEL)
                {
                    if (name == ControlID.MINIMIZE_BUTTON)
                    {
                        ShowWindow(this.Handle, SW_MINIMIZED);
                    }
                    else if (name == ControlID.KERNEL_BUTTON)
                    {
                        if (!this.panels[currentPanel]._ButtonPressed[ControlID.KERNEL_BUTTON])
                        {


                            statusLabel.Text = "Kernel Starting...";
                            this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].Enabled = false;
                            this.panels[currentPanel]._PressedButtonControls[ControlID.KERNEL_BUTTON].Size = new Size(128, 128);
                            this.panels[currentPanel]._PressedButtonControls[ControlID.KERNEL_BUTTON].Visible = true;
                            this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].Visible = false;
                            this.panels[currentPanel]._ButtonText[ControlID.KERNEL_BUTTON].Text = "Stop Kernel";
                            this.panels[currentPanel]._ButtonPressed[ControlID.KERNEL_BUTTON] = true;
                            this.Refresh();



                            Core.SubscribeEvent(KernelResponse.STARTED, EventListener);
                            Core.SubscribeEvent(KernelResponse.REGISTERED, EventListener);
                            Core.SubscribeEvent(KernelResponse.UNREGISTERED, EventListener);
                            Core.SubscribeEvent(KernelResponse.STOPPED, EventListener);
                            Core.SubscribeEvent(KernelResponse.DISCOVERED, EventListener);
                            Core.SubscribeEvent(KernelResponse.CONNECTED, EventListener);
                            Core.SubscribeEvent(KernelResponse.DISCONNECTED, EventListener);
                            Core.SubscribeEvent(KernelResponse.SENSORS_UPDATED, EventListener);
                            Core.SubscribeEvent(KernelResponse.PING_RESPONSE, EventListener);
                            startupThread = new Thread(new ThreadStart(LoadWockets));
                            startupThread.Start();
                            
                        }
                        else
                        {

                            if ((WocketsTimer.GetUnixTime() - clickTime) < 3000)
                                return;
                            if (MessageBox.Show("Are you sure you want to stop wockets kernel?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                            {
                                this.panels[currentPanel]._PressedButtonControls[ControlID.KERNEL_BUTTON].Enabled = false;
                                this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].Size = new Size(128, 128);
                                this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].Visible = true;
                                //this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].BringToFront();
                                this.panels[currentPanel]._PressedButtonControls[ControlID.KERNEL_BUTTON].Visible = false;
                                this.panels[currentPanel]._ButtonText[ControlID.KERNEL_BUTTON].Text = "Start Kernel";
                                this.panels[currentPanel]._ButtonPressed[ControlID.KERNEL_BUTTON] = false;


                                if (Core._KernalStarted)
                                {

                                    if (soundThread != null)
                                    {
                                        soundThread.Abort();
                                        soundThread = null;
                                    }
                                    
                                    Core.Disconnect();
                                    Core._Connected = false;
                                    Core._Registered = false;
                                    selectedWockets.Clear();                              
                                    Core.Terminate();

                                    plotter = null;
                                    this.selectedActivityProtocol = -1;
                                    this.annotatedSession = null;
                                    this.activityStatus = ActivityStatus.None;
                                    for (int i = 0; i < activityButtons.Count; i++)
                                    {
                                        System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                                        for (int j = 0; j < activityList.Length; j++)
                                            this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Remove(activityList[j]);
                                    }
                                    activityButtons.Clear();                 
                                    CleanupML();
                                    this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].Visible = true;
                                    this.panels[currentPanel]._PressedButtonControls[ControlID.KERNEL_BUTTON].Visible = false;
                                    this.panels[currentPanel]._ButtonText[ControlID.KERNEL_BUTTON].Text = "Start Kernel";
                                    this.panels[currentPanel]._ButtonPressed[ControlID.KERNEL_BUTTON] = false;

                                    this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Enabled = false;
                                    this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Size = new Size(128, 128);
                                    this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Visible = true;
                                    this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Visible = false;
                                    this.panels[currentPanel]._ButtonText[ControlID.CONNECT_BUTTON].Text = "Connect";
                                    this.panels[currentPanel]._ButtonPressed[ControlID.CONNECT_BUTTON] = false;
                                    this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Enabled = true;

                                }
                                this.panels[currentPanel]._UnpressedButtonControls[ControlID.KERNEL_BUTTON].Enabled = true;
                                statusLabel.Text = "Kernel Stopped";                  
                            }
                        }

                    }
      
                    else if (name == ControlID.ACTIVITY_BUTTON)
                    {
                        if (Core._Connected)
                        {
                            if (this.activityStatus == ActivityStatus.Annotating)
                            {
                                this.panels[currentPanel].Visible = false;
                                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Location = new Point(0, 0);
                                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].BringToFront();
                                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Visible = true;
                                this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Dock = DockStyle.None;
                                this.currentPanel = ControlID.ANNOTATION_BUTTON_PANEL;
                            }
                            else if (this.activityStatus == ActivityStatus.Measuring)
                            {
                                this.panels[currentPanel].Visible = false;
                                this.panels[ControlID.CLASSIFICATION_PANEL].Location = new Point(0, 0);
                                this.panels[ControlID.CLASSIFICATION_PANEL].BringToFront();
                                this.panels[ControlID.CLASSIFICATION_PANEL].Visible = true;
                                this.panels[ControlID.CLASSIFICATION_PANEL].Dock = DockStyle.None;
                                this.currentPanel = ControlID.CLASSIFICATION_PANEL;

                            }
                            else
                            {
                                this.panels[currentPanel].Visible = false;
                                this.panels[ControlID.ACTIVITY_PANEL].Location = new Point(0, 0);
                                this.panels[ControlID.ACTIVITY_PANEL].BringToFront();
                                this.panels[ControlID.ACTIVITY_PANEL].Visible = true;
                                this.panels[ControlID.ACTIVITY_PANEL].Dock = DockStyle.None;
                                this.currentPanel = ControlID.ACTIVITY_PANEL;
                            }
                        }
                        else
                            MessageBox.Show("Please connect to wockets!");

                    }
                    else if (name == ControlID.RESET_BUTTON)
                    {
                        if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                        {
                            
                            Core.Unregister();
                            ScreenUtils.ShowTaskBar(true);


                            this.selectedActivityProtocol = -1;
                            this.annotatedSession = null;

                            this.activityStatus = ActivityStatus.None;
                            //cleanup any annotation buttons
                            for (int i = 0; i < activityButtons.Count; i++)
                            {
                                System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                                for (int j = 0; j < activityList.Length; j++)
                                    this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Remove(activityList[j]);
                            }
                            activityButtons.Clear();
                            
                            //Cleanup the machine learning buffers if needed
                            CleanupML();
                            Core.Terminate();
                            Application.Exit();
                            System.Diagnostics.Process.GetCurrentProcess().Kill();
                        }
                    }
                    else if (name == ControlID.SETTINGS_BUTTON)
                    {


                        if (!Core._KernalStarted)
                            MessageBox.Show("Please start the kernel before changing the settings", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button1);
                        else
                        {
                            if (Core._Connected)
                                MessageBox.Show("Cannot change the settings while connected", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button1);
                            else
                            {

                                this.panels[ControlID.HOME_PANEL].Visible = false;
                                this.panels[ControlID.WOCKETS_PANEL].Location = new Point(0, 0);                           
                                this.panels[ControlID.WOCKETS_PANEL].Visible = true;
                                this.panels[ControlID.WOCKETS_PANEL].Dock = DockStyle.None;
                                this.currentPanel = ControlID.WOCKETS_PANEL;
                                selectedWockets.Clear();
                                UpdatewWocketsList();
                            }
                        }

                    }
                    else if (name == ControlID.CONNECT_BUTTON)
                    {
                        if (Core._KernalStarted)
                        {
                            if (Core._Registered)
                            {
                                if (selectedWockets.Count != 0)
                                {

                                    if (!this.panels[currentPanel]._ButtonPressed[ControlID.CONNECT_BUTTON])
                                    {
                                        Core.Connect();
                                        statusLabel.Text = "Connecting...";

                                        this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Enabled = false;
                                        this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Size = new Size(128, 128);
                                        this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Visible = true;
                                        this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Visible = false;
                                        this.panels[currentPanel]._ButtonText[ControlID.CONNECT_BUTTON].Text = "Disconnect";
                                        this.panels[currentPanel]._ButtonPressed[ControlID.CONNECT_BUTTON] = true;
                                        this.Refresh();
                                        this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Enabled = true;
                                        clickTime = WocketsTimer.GetUnixTime();
                                    }
                                    else
                                    {
                                        if ((WocketsTimer.GetUnixTime() - clickTime) < 3000)
                                            return;
                                        if (MessageBox.Show("Are you sure you want to disconnect?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
                                        {
                                            if (Core._Connected)
                                            {

                                                if (soundThread != null)
                                                {
                                                    soundThread.Abort();
                                                    soundThread = null;
                                                }
                                                statusLabel.Text = "Disconnecting...";
                                                Core._Connected = false;
                                                selectedWockets.Clear();
                                                this.selectedActivityProtocol = -1;
                                                
                                                this.activityStatus = ActivityStatus.None;
                                                
                                                //cleanup any activity buttons
                                                for (int i = 0; i < activityButtons.Count; i++)
                                                {
                                                    System.Windows.Forms.Button[] activityList = (System.Windows.Forms.Button[])activityButtons[i];
                                                    for (int j = 0; j < activityList.Length; j++)
                                                        this.panels[ControlID.ANNOTATION_BUTTON_PANEL].Controls.Remove(activityList[j]);
                                                }
                                                activityButtons.Clear();

                                                Core.Disconnect();
                                                plotter = null;
                                          
                                                this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Enabled = false;
                                                this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Size = new Size(128, 128);
                                                this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Visible = true;
                                                this.panels[currentPanel]._PressedButtonControls[ControlID.CONNECT_BUTTON].Visible = false;
                                                this.panels[currentPanel]._ButtonText[ControlID.CONNECT_BUTTON].Text = "Connect";
                                                this.panels[currentPanel]._ButtonPressed[ControlID.CONNECT_BUTTON] = false;
                                                this.panels[currentPanel]._UnpressedButtonControls[ControlID.CONNECT_BUTTON].Enabled = true;
                                                statusLabel.Text = "Ready to connect";
                                            }
                                                                      
                                        }
                                    }
                                }
                                else
                                    MessageBox.Show("Please select wockets before connecting", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button2);
                            }
                            else
                                MessageBox.Show("Application not registered with the kernel", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button2);
                        }
                        else
                            MessageBox.Show("Please start the kernel before connecting to the wockets", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button2);
                    }
                    else if (name == ControlID.LINE_CHART_BUTTON)
                    {
                        if (Core._Connected)
                        {
                            //plotterTimer.Enabled = true;
                            this.panels[currentPanel].Visible = false;
                            this.panels[ControlID.PLOTTER_PANEL].Location = new Point(0, 0);
                            this.panels[ControlID.PLOTTER_PANEL].BringToFront();
                            this.panels[ControlID.PLOTTER_PANEL].Visible = true;
                            this.panels[ControlID.PLOTTER_PANEL].Dock = DockStyle.None;
                            this.currentPanel = ControlID.PLOTTER_PANEL;
                            //UpdatePlotter();
                            if (plotter != null)
                            {
                                plotterTimer.Enabled = false;
                                plotter.Dispose();
                            }
                            plotterPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
                            plotter = new WocketsScalablePlotter(plotterPanel);
                            plotterPanel.Visible = true;
                            plotterTimer.Enabled = true;
                        

                        }
                        else
                            MessageBox.Show("Cannot plot without connecting wockets!");

                    }
                    else if (name == ControlID.ACTIVITY_BUTTON)
                    {
                    }

                }
                else if (currentPanel == ControlID.SETTINGS_PANEL)
                {
                    if (name == ControlID.BACK_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[ControlID.SETTINGS_PANEL].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                    }
                    else if (name == ControlID.BLUETOOTH_BUTTON)
                    {
                        if (!Core._KernalStarted)
                            MessageBox.Show("Please start the kernel before selecting wockets", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button1);
                        else
                        {
                            if (Core._Connected)
                                MessageBox.Show("Cannot change the wockets while connected", "Confirm", MessageBoxButtons.OK, MessageBoxIcon.Exclamation, MessageBoxDefaultButton.Button1);
                            else
                            {

                                this.panels[ControlID.SETTINGS_PANEL].Visible = false;
                                this.panels[ControlID.WOCKETS_PANEL].Location = new Point(0, 0);
                                //this.panels[ControlID.WOCKETS_PANEL].BringToFront();                   
                                this.panels[ControlID.WOCKETS_PANEL].Visible = true;
                                this.panels[ControlID.WOCKETS_PANEL].Dock = DockStyle.None;
                                this.currentPanel = ControlID.WOCKETS_PANEL;
                                selectedWockets.Clear();
                                UpdatewWocketsList();
                            }
                        }
                    }
                }
                else if (currentPanel == ControlID.PLOTTER_PANEL)
                {
                    if (name == ControlID.PLOTTER_BACK_BUTTON)
                    {
                        this.panels[ControlID.HOME_PANEL].Visible = true;
                        this.panels[ControlID.PLOTTER_PANEL].Visible = false;
                        this.currentPanel = ControlID.HOME_PANEL;
                        plotterTimer.Enabled = false;
                        plotterPanel.Visible = false;

                        //Core.SetSniff(wocketsKernelGuid, SleepModes.Sleep1Second);
                    }
                }
          
              
                this.Refresh();
            }


        #endregion 


        #region Plot/Visualization Related functions

            private Bitmap backBuffer = null;
            private System.Windows.Forms.Timer plotterTimer = null;

            void plotterTimer_Tick(object sender, EventArgs e)
            {
                if (plotter != null)
                {
                    if (backBuffer == null) // || (isResized))
                    {
                        backBuffer = new Bitmap(plotterPanel.Width, (int)(plotterPanel.Height));
                    }
                    using (Graphics g = Graphics.FromImage(backBuffer))
                    {

                        plotter.Draw(g);
                        g.Dispose();

                    }
                }
            }

            void plotterPanel_Paint(object sender, PaintEventArgs e)
            {
                if (plotterPanel.Visible)
                {
                    if (backBuffer != null)
                        e.Graphics.DrawImage(backBuffer, 0, 0);
                }
            }


            public override void Refresh()
            {
                if (this.panels[currentPanel]._Background != null)
                {
                    // AlphaContainer._backBuffer
                    Graphics offscreen = Graphics.FromImage(this.panels[currentPanel]._Backbuffer);
                    offscreen.DrawImage(this.panels[currentPanel]._Background, 0, 0);
                }
                base.Refresh();
            }

            int m = 0;
            private void timeAnimation_Tick()
            {
                int prevPanelIndex = currentPanelIndex;
                int prevPanel = slidingPanels[currentPanelIndex];
                currentPanelIndex++;
                currentPanelIndex = currentPanelIndex % slidingPanels.Length;
                currentPanel = slidingPanels[currentPanelIndex];
                if (this.currentTransition == Transitions.LEFT_TO_RIGHT)
                {
                    this.panels[currentPanel].Location = new Point(0 - this.panels[currentPanel].Width, 0);
                    this.panels[currentPanel].BringToFront();
                    this.panels[currentPanel].Visible = true;

                    this.panels[currentPanel].Dock = DockStyle.None;
                    m = 0;

                    for (int x = -480; (x <= 0); x += 100)
                    // for (int x = Screen.PrimaryScreen.WorkingArea.Width; (x >=0 ); x -= 100)
                    {
                        this.panels[currentPanel].Location = new Point(x, this.panels[currentPanel].Location.Y);
                        //this.panels[currentPanel]._Backbuffer = this._backBuffers[currentPanel];
                        this.panels[currentPanel].Update();
                    }

                    this.panels[currentPanel].Location = new Point(0, this.panels[currentPanel].Location.Y);
                    this.panels[prevPanel].Visible = false;
                }
                else if (this.currentTransition == Transitions.RIGHT_TO_LEFT)
                {
                    this.panels[currentPanel].Location = new Point(0 - this.panels[currentPanel].Width, 0);
                    this.panels[currentPanel].BringToFront();
                    this.panels[currentPanel].Visible = true;

                    this.panels[currentPanel].Dock = DockStyle.None;
                    m = 0;

                    //for (int x = -480; (x <= 0); x += 100)
                    for (int x = Screen.PrimaryScreen.WorkingArea.Width; (x >= 0); x -= 100)
                    {
                        this.panels[currentPanel].Location = new Point(x, this.panels[currentPanel].Location.Y);
                        //this.panels[currentPanel]._Backbuffer = this._backBuffers[currentPanel];
                        this.panels[currentPanel].Update();
                    }

                    this.panels[currentPanel].Location = new Point(0, this.panels[currentPanel].Location.Y);
                    this.panels[prevPanel].Visible = false;
                }
            }


            #region commented
                /* protected override void OnPaintBackground(PaintEventArgs e)
                {
                // Prevent flicker, we will take care of the background in OnPaint()
                }*/
            #endregion

            protected override void OnPaint(PaintEventArgs e)
            {
                // this.Invalidate();
                //SHFullScreen(this.Handle, SHFS_HIDETASKBAR | SHFS_HIDESIPBUTTON | SHFS_HIDESTARTICON);
                _alphaManager.OnPaint(e);

            }

       #endregion 



    }
}