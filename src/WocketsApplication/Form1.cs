using System;
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
using  Microsoft.Win32;
using Wockets.Kernel.Types;
using Wockets.IPC;
using Wockets.Kernel;
using Wockets.Data.Plotters;



namespace WocketsApplication
{
    public partial class Form1 : Form
    {
        private const int NUMBER_PANELS=6;
        //private const int NUMBER_BUTTONS=9;
        private ClickableAlphaPanel[] panels= new ClickableAlphaPanel[NUMBER_PANELS];
        private int[] slidingPanels = new int[2] { 0, 1 };
        private int[] numberButtons = new int[NUMBER_PANELS];
        private int currentPanel = 0;
        private int currentPanelIndex = 0;
        private Rectangle clientArea;
        public bool pushed = false;
        private AlphaContainer _alphaManager;
        private Thread slidingThread;
       // private ClickableAlphaPanel[] buttonPanels = new ClickableAlphaPanel[9];
        //private Bitmap[] _buttonBackBuffers = new Bitmap[9];

        private string wocketsKernelGuid = null;

        private Thread kListenerThread;


        delegate void UpdatewWocketsListCallback();
        private bool disposed = false;

        public void UpdatewWocketsList()
        {
            if (!disposed)
            {
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                if (wocketsList.InvokeRequired)
                {
                    UpdatewWocketsListCallback d = new UpdatewWocketsListCallback(UpdatewWocketsList);
                    this.Invoke(d, new object[] { });
                }
                else
                {

                    wocketsList.Controls.Clear();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH); ;
                    string[] sensors = rk.GetSubKeyNames();
                    rk.Close();
                    if (sensors.Length > 0)
                    {
                        wocketsList._Status = "";
                        for (int i = 0; (i < sensors.Length); i++)
                        {

                            rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH + "\\" + sensors[i]); ;
                            WocketListItem wi = new WocketListItem((string)rk.GetValue("Name"), (string)rk.GetValue("MacAddress"));
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
                        wocketsList.Refresh();
                    }
              
                }
            }

        }

        private bool wocketsConnected = false;
        private void KernelListener()
        {
            NamedEvents namedEvent = new NamedEvents();
            while (true)
            {
                //ensures prior synchronization

                namedEvent.Receive(wocketsKernelGuid);


                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + wocketsKernelGuid + "}");
                string response = (string)rk.GetValue("Message");
                rk.Close();

              if (response == ApplicationResponse.DISCOVERY_COMPLETED.ToString())
                {
                    UpdatewWocketsList();
                }
                else if (response == ApplicationResponse.CONNECT_SUCCESS.ToString())
                {
                   wocketsConnected = true;
                   //plotterTimer.Enabled = true;
                   UpdatePlotter();
                  
                }
                else if (response == ApplicationResponse.DISCONNECT_SUCCESS.ToString())
                {
                    wocketsConnected = false;                   
                }
                namedEvent.Reset();
            }
        }

  
        delegate void UpdatePlotterCallback();
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
                        plotter.Dispose();
                    plotter = new WocketsScalablePlotter(plotterPanel, selectedWockets.Count);
                    plotterPanel.Visible = true;
                    plotterTimer.Enabled = true;        
                }
            }

        }

        public Form1()
        {                    
            //MainThreadID = Thread.CurrentThread.ManagedThreadId;
            RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\MIT\\Wockets", true);
            if (rk == null)
            {
                if (MessageBox.Show("Thanks for installing the wockets\nThe setup will continue. Are you ready?", "",
                        MessageBoxButtons.YesNo,
                        MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.No)
                    Application.Exit();                
            }

            wocketsKernelGuid = Core.Register();
            if ((wocketsKernelGuid != null) && (wocketsKernelGuid.Length > 0))
            {
                kListenerThread = new Thread(new ThreadStart(KernelListener));
                kListenerThread.Start();
            } 
            ScreenUtils.ShowTaskBar(false);
            ScreenUtils.ShowTrayBar(false);
            InitializeComponent();
            InitializeInterface();

            //all commands should be sent after initializing interface

            wocketsList._Status = "Refresh wockets...";
            //this.slidingThread = new Thread(new ThreadStart(timeAnimation_Tick));
            _alphaManager = new AlphaContainer(this);
             this.Refresh();    
        }



        private Color[] colors = new Color[NUMBER_PANELS] { Color.White, Color.Black, Color.Red, Color.Green, Color.FromArgb(245, 219, 186), Color.FromArgb(245, 219, 186) };
        private Bitmap[] _backBuffers = new Bitmap[NUMBER_PANELS];

        //private BluetoothPanel pp;
        private Transitions currentTransition;

        public void AddButton(int panelID, int buttonID, string pressedFilename,string unpressedFilename, int x, int y,int size)
        {
            this.panels[panelID]._UnpressedButtonControls[buttonID] = new AlphaPictureBox();
            this.panels[panelID]._UnpressedButtonControls[buttonID].Name = buttonID.ToString();
            this.panels[panelID]._UnpressedButtonControls[buttonID].Size = new Size(size, size);
            this.panels[panelID]._UnpressedButtonControls[buttonID].Image = AlphaImage.CreateFromFile(Constants.PATH + unpressedFilename);
            this.panels[panelID]._UnpressedButtonControls[buttonID].Visible = true;
            this.panels[panelID]._UnpressedButtonControls[buttonID].Location = new Point(x, y);
            this.panels[panelID]._UnpressedButtonControls[buttonID].Click += new EventHandler(clickHandler);

            this.panels[panelID]._PressedButtonControls[buttonID] = new AlphaPictureBox();
            this.panels[panelID]._PressedButtonControls[buttonID].Name = buttonID.ToString();
            this.panels[panelID]._PressedButtonControls[buttonID].Size = new Size(128, 128);
            this.panels[panelID]._PressedButtonControls[buttonID].Image = AlphaImage.CreateFromFile(Constants.PATH + pressedFilename);
            this.panels[panelID]._PressedButtonControls[buttonID].Visible = false;
            this.panels[panelID]._PressedButtonControls[buttonID].Location = new Point(x, y);
            this.panels[panelID]._PressedButtonControls[buttonID].Click += new EventHandler(clickHandler);
            
            

        }


        
 


        WocketSlidingList wocketsList = null;
        private Panel bluetoothPanel;
        private Label bluetoothName;
        private Label bluetoothMac;
        private Label bluetoothPIN;
        private ComboBox bluetoothTP;
        private ComboBox bluetoothSM;

        private WocketListItem currentWi;
        ArrayList selectedWockets = new ArrayList();
        WocketsScalablePlotter plotter=null;
        private Panel plotterPanel;
        public void InitializeInterface()
        {
            

            currentTransition = Transitions.LEFT_TO_RIGHT;

            Constants.PATH = System.IO.Path.GetDirectoryName(
               System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase)+"\\NeededFiles\\";


            this.AutoScroll = false;
            this.numberButtons[ControlID.HOME_PANEL] = ControlID.HOME_PANEL_BUTTON_COUNT;
            this.numberButtons[ControlID.ABOUT_PANEL] = ControlID.ABOUT_PANEL_BUTTON_COUNT;
            this.numberButtons[ControlID.SETTINGS_PANEL] = ControlID.SETTINGS_PANEL_BUTTON_COUNT;
            this.numberButtons[ControlID.WOCKETS_PANEL] = ControlID.WOCKETS_PANEL_BUTTON_COUNT;
            this.numberButtons[ControlID.WOCKETS_CONFIGURATION_PANEL] = ControlID.WOCKETS_CONFIGURATION_PANEL_BUTTON_COUNT;
            this.numberButtons[ControlID.PLOTTER_PANEL] = ControlID.PLOTTER_PANEL_BUTTON_COUNT;

           
            for (int i = 0; (i < NUMBER_PANELS); i++)
           {

               this.panels[i] = new ClickableAlphaPanel(this.numberButtons[i]);
                this.panels[i].Size = new Size(480, 640);
                this.panels[i].MouseDown += new MouseEventHandler(owner_MouseDown);
                this.panels[i].MouseUp += new MouseEventHandler(owner_MouseUp);                
                this.panels[i].BackColor=colors[i];
                this.panels[i].Dock = DockStyle.Fill;
                this.panels[i]._Backbuffer=new Bitmap(480, 640, PixelFormat.Format32bppRgb);
                this.Controls.Add(this.panels[i]);
            }

            //setup backgrounds
            this.panels[ControlID.HOME_PANEL]._Background = new Bitmap(Backgrounds.DottedBlack);
            this.panels[ControlID.HOME_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
            this.panels[ControlID.ABOUT_PANEL]._Background = new Bitmap(Backgrounds.DottedBlack);
            this.panels[ControlID.ABOUT_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
            this.panels[ControlID.SETTINGS_PANEL]._Background = new Bitmap(Backgrounds.DottedBlack);
            this.panels[ControlID.SETTINGS_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
            this.panels[ControlID.WOCKETS_PANEL]._Background = new Bitmap(Backgrounds.DottedBlack);
            this.panels[ControlID.WOCKETS_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";            
            this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL]._Background = new Bitmap(Backgrounds.DottedBlack);
            this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";
            this.panels[ControlID.PLOTTER_PANEL]._Background = new Bitmap(Backgrounds.DottedBlack);
            this.panels[ControlID.PLOTTER_PANEL]._BackgroundFile = Constants.PATH + "Backgrounds\\DottedBlack.png";


            //Main Page
            //Home Screen Bottom  Buttons
            AddButton(ControlID.HOME_PANEL, ControlID.SETTINGS_BUTTON, "Buttons\\SettingsPressed.png", "Buttons\\SettingsUnpressed.png", 0, this.Height - 130, 128);
            AddButton(ControlID.HOME_PANEL, ControlID.MINIMIZE_BUTTON, "Buttons\\MinimizePressed.png", "Buttons\\MinimizeUnpressed.png", 160, this.Height - 130, 128);
            AddButton(ControlID.HOME_PANEL, ControlID.RESET_BUTTON, "Buttons\\TurnOffPressed.png", "Buttons\\TurnOffUnpressed.png", 310, this.Height - 130, 128);

            //Home Screen Buttons
            AddButton(ControlID.HOME_PANEL, ControlID.LINE_CHART_BUTTON, "Buttons\\LineChartPressed.png", "Buttons\\LineChartUnpressed.png", 0, 0, 128);
            AddButton(ControlID.HOME_PANEL, ControlID.BATTERY_BUTTON, "Buttons\\BatteryPressed.png", "Buttons\\BatteryUnpressed.png", 160, 0, 128);
            AddButton(ControlID.HOME_PANEL, ControlID.GREEN_POWER_BUTTON, "Buttons\\SavePowerPressed-128.png", "Buttons\\SavePowerUnpressed-128.png", 310, 0, 128);

            //AddButton(ControlID.HOME_PANEL, ControlID.START_KERNEL_BUTTON, "Buttons\\StartKernelPressed-128.png", "Buttons\\StartKernelUnpressed-128.png", 0, 160, 128);
            //AddButton(ControlID.HOME_PANEL, ControlID.STOP_KERNEL_BUTTON, "Buttons\\StopKernelPressed-128.png", "Buttons\\StopKernelUnpressed-128.png", 160, 160, 128);

            AddButton(ControlID.HOME_PANEL, ControlID.CONNECT_BUTTON, "Buttons\\ConnectPressed-128.png", "Buttons\\ConnectUnpressed-128.png", 0, 160, 128);
            AddButton(ControlID.HOME_PANEL, ControlID.DISCONNECT_BUTTON, "Buttons\\DisconnectPressed-128.png", "Buttons\\DisconnectUnpressed-128.png", 160, 160, 128);

            
            
            //AddButton(ControlID.HOME_PANEL, ControlID.ANNOTATE_BUTTON, "Buttons\\AnnotatePressed.png", "Buttons\\AnnotateUnpressed.png", 0, 160, 128);
            //AddButton(ControlID.HOME_PANEL, ControlID.STATISTICS_BUTTON, "Buttons\\StatisticsPressed.png", "Buttons\\StatisticsUnpressed.png", 310, 0, 128);
            //AddButton(ControlID.HOME_PANEL, ControlID.QUALITY_BUTTON, "Buttons\\SignalQualityPressed.png", "Buttons\\SignalQualityUnpressed.png", 0, 160, 128);
            
            //AddButton(ControlID.HOME_PANEL, ControlID.HEALTH_BUTTON, "Buttons\\HeartPressed.png", "Buttons\\HeartUnpressed.png", 310, 160, 128);
            

  
            
            

            //Settings Bottom  Buttons
            AddButton(ControlID.SETTINGS_PANEL, ControlID.BACK_BUTTON, "Buttons\\BackPressed.png", "Buttons\\BackUnpressed.png", 310, this.Height - 130, 128);

            //Settings Buttons
            AddButton(ControlID.SETTINGS_PANEL, ControlID.BLUETOOTH_BUTTON, "Buttons\\BluetoothPressed.png", "Buttons\\BluetoothUnpressed.png", 0, 0, 128);
            AddButton(ControlID.SETTINGS_PANEL, ControlID.SOUND_BUTTON, "Buttons\\SoundPressed.png", "Buttons\\SoundUnpressed.png", 160, 0, 128);

            //Wockets Screen

            AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_BACK_BUTTON, "Buttons\\Back48Pressed.png", "Buttons\\Back48Unpressed.png", 400, this.Height -48, 48);
            AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_UP_BUTTON, "Buttons\\Up48Pressed.png", "Buttons\\Up48Unpressed.png", 250, this.Height - 48, 48);
            AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_DOWN_BUTTON, "Buttons\\Down48Pressed.png", "Buttons\\Down48Unpressed.png", 180, this.Height - 48, 48);
            AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_RELOAD_BUTTON, "Buttons\\BluetoothReloadPressed-48.png", "Buttons\\BluetoothReloadUnpressed-48.png", 20, this.Height - 48, 48);
            //AddButton(ControlID.WOCKETS_PANEL, ControlID.WOCKETS_SAVE_BUTTON, "Buttons\\SavePressed-64.png", "Buttons\\SaveUnpressed-64.png", 100, this.Height - 64, 64);

            wocketsList = new WocketSlidingList();                                         
            wocketsList.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);            
            wocketsList.Location = new Point(0, 0);        
            this.panels[ControlID.WOCKETS_PANEL].Controls.Add(wocketsList);
            wocketsList.BringToFront();                     


            //Wockets Configuration Panel

            AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_BLUETOOTH_BUTTON, "Buttons\\BluetoothUnpressed-64.png", "Buttons\\BluetoothPressed-64.png", 0, this.Height - 64, 64);
            AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_COMMAND_BUTTON, "Buttons\\CommandPressed-64.png", "Buttons\\CommandUnpressed-64.png", 80, this.Height - 64, 64);
            AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_TIMERS_BUTTON, "Buttons\\TimerPressed-64.png", "Buttons\\TimerUnpressed-64.png", 160, this.Height - 64, 64);
            AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_STATUS_BUTTON, "Buttons\\StatusPressed-64.png", "Buttons\\StatusUnpressed-64.png", 240, this.Height - 64, 64);
            AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_INFORMATION_BUTTON, "Buttons\\InformationPressed-64.png", "Buttons\\InformationUnpressed-64.png", 320, this.Height - 64, 64);
            AddButton(ControlID.WOCKETS_CONFIGURATION_PANEL, ControlID.WOCKETS_CONFIGURATIONS_BACK_BUTTON, "Buttons\\Back64Pressed.png", "Buttons\\Back64Unpressed.png", 400, this.Height - 64, 64);
            bluetoothPanel = new Panel();
            bluetoothPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
            bluetoothPanel.Visible = true;
            bluetoothPanel.BackColor = Color.FromArgb(245, 219, 186);
            bluetoothName = new Label();
            bluetoothName.Location = new Point(10, 10);
            bluetoothName.Size = new Size(250, 40);
            bluetoothName.Font = new Font(FontFamily.GenericSansSerif, 14.0f, FontStyle.Underline|FontStyle.Bold);
            bluetoothPanel.Controls.Add(bluetoothName);
            this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Controls.Add(bluetoothPanel);            

            //Plotter Panel
            AddButton(ControlID.PLOTTER_PANEL, ControlID.WOCKETS_BACK_BUTTON, "Buttons\\Back48Pressed.png", "Buttons\\Back48Unpressed.png", 400, this.Height - 48, 48);
            plotterPanel = new Panel();
            plotterPanel.Size = new Size(Screen.PrimaryScreen.WorkingArea.Width, Screen.PrimaryScreen.WorkingArea.Height);
            plotterPanel.Visible = true;
            plotterPanel.BackColor = Color.FromArgb(245, 219, 186);
            plotterPanel.Paint += new PaintEventHandler(plotterPanel_Paint);
            plotterTimer = new System.Windows.Forms.Timer();
            plotterTimer.Interval = 50;
            plotterTimer.Tick += new EventHandler(plotterTimer_Tick);
           
            this.panels[ControlID.PLOTTER_PANEL].Controls.Add(plotterPanel);            


            
            //this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Controls.Add(
            //add bluetooth panel
            //add timers panel
            //add status panel



            for (int i = 0; (i < NUMBER_PANELS); i++)
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
            
            //this.panels[currentPanel]._Backbuffer = this._backBuffers[currentPanel];                        
            this.panels[currentPanel].Location = new Point(0, 0);
            this.panels[currentPanel].Update();
            this.panels[currentPanel].Visible = true;

            this.Deactivate += new EventHandler(Form1_Deactivate);
            this.Activated += new EventHandler(Form1_Activated);
          
        }

        bool isPlotting = false;
        void plotterTimer_Tick(object sender, EventArgs e)
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

        private Bitmap backBuffer = null;
        private System.Windows.Forms.Timer plotterTimer=null;

        void plotterPanel_Paint(object sender, PaintEventArgs e)
        {
            if (plotterPanel.Visible)
            {
                if (backBuffer != null)
                    e.Graphics.DrawImage(backBuffer, 0, 0);
            }
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


        void owner_MouseUp(object sender, MouseEventArgs e)
        {

            //if ((pushed)&& (clientArea.Contains(e.X, e.Y)))                   
            //    timeAnimation_Tick();            
            //this.pushed = false;
      
            if (this.panels[currentPanel]._UnpressedButtonControls != null)
            {
                for (int i = 0; (i < this.panels[currentPanel]._UnpressedButtonControls.Length); i++)
                {
                    if (this.panels[currentPanel]._ButtonPressed[i])
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

            if ((!pushed)  && (this.slidingPanels.Contains(currentPanel)))
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
                    this.clientArea = new Rectangle(0, e.Y - (Screen.PrimaryScreen.WorkingArea.Height / 5), (Screen.PrimaryScreen.WorkingArea.Width  / 2), (Screen.PrimaryScreen.WorkingArea.Height / 5) * 2);
                }
            }


            if (this.panels[currentPanel]._UnpressedButtonControls != null)
            {
                for (int i = 0; (i < this.panels[currentPanel]._UnpressedButtonControls.Length); i++)
                {

                    if (this.panels[currentPanel]._UnpressedButtonControls[i].HitTest(e.X, e.Y))
                    {
                        if (!this.panels[currentPanel]._ButtonPressed[i])
                        {
                                this.panels[currentPanel]._PressedButtonControls[i].Visible = true;
                                this.panels[currentPanel]._UnpressedButtonControls[i].Visible = false;
                                this.panels[currentPanel]._ButtonPressed[i] = true;
                                this.panels[currentPanel]._PressedButtonControls[i].Refresh();
                        }
                    }
                    else if (this.panels[currentPanel]._ButtonPressed[i])
                    {
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
            if ( (wi.AddHitTest(wi.LastX, wi.LastY)) && !selectedWockets.Contains(wi))
            {
                selectedWockets.Add(wi);
                wi.BackColor = Color.FromArgb(205,183,158);
            }
            else if (wi.RemoveHitTest(wi.LastX, wi.LastY) && selectedWockets.Contains(wi))
            {
                selectedWockets.Remove(wi);
                wi.BackColor = Color.FromArgb(245, 219, 186);
            }
            else                        
            {
                bluetoothName.Text = wi._Name;                
                this.panels[ControlID.WOCKETS_CONFIGURATION_PANEL].Visible = true;
                this.panels[ControlID.WOCKETS_PANEL].Visible = false;
                currentPanel = ControlID.WOCKETS_CONFIGURATION_PANEL;
            }
        }
        public delegate void ClickHandler(object sender, EventArgs e);        
        private void clickHandler(object sender, EventArgs e)
        {
            AlphaPictureBox p = (AlphaPictureBox)sender;


            int name = Convert.ToInt32(p.Name);
            if (currentPanel == ControlID.WOCKETS_PANEL)
            {
                if (name == ControlID.WOCKETS_BACK_BUTTON)
                {                    
                    this.panels[ControlID.SETTINGS_PANEL].Visible = true;
                    this.panels[ControlID.WOCKETS_PANEL].Visible = false;
                    currentPanel = ControlID.SETTINGS_PANEL;
                    ArrayList s = new ArrayList();
                    for (int i = 0; (i < selectedWockets.Count); i++)
                    {
                        s.Add(((WocketListItem)selectedWockets[i])._MacAddress);
                    }
                    Core.SetSensors(wocketsKernelGuid,s);
                }
                else if (name == ControlID.WOCKETS_UP_BUTTON)
                    wocketsList.MoveDown();
                else if (name == ControlID.WOCKETS_DOWN_BUTTON)
                    wocketsList.MoveUp();
                else if (name == ControlID.WOCKETS_RELOAD_BUTTON)
                {
                    wocketsList._Status = "Searching for Wockets...";
                    wocketsList.Refresh();
                    if (wocketsKernelGuid != null)
                        Core.Send(KernelCommand.DISCOVER, wocketsKernelGuid);
                }
               /* else if (name == ControlID.WOCKETS_SAVE_BUTTON)
                {
                }*/
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

                if (name == ControlID.START_KERNEL_BUTTON)
                {
                    //Process.Start("//Program Files//kernel//Kernel.exe","");
                }
                else if (name == ControlID.STOP_KERNEL_BUTTON)
                {         
                    if (wocketsKernelGuid != null)
                        Core.Send(KernelCommand.TERMINATE, wocketsKernelGuid);
                }
                if (name == ControlID.BATTERY_BUTTON)
                {
                    if (wocketsConnected)
                        Core.SetSniff(wocketsKernelGuid, SleepModes.NoSleep);
                }
                else if (name == ControlID.GREEN_POWER_BUTTON)
                {
                    if (wocketsConnected)
                        Core.SetSniff(wocketsKernelGuid, SleepModes.Sleep1Second);
                }
                else if (name == ControlID.RESET_BUTTON)
                {
                    if (wocketsKernelGuid!=null)
                        Core.Unregister(wocketsKernelGuid);
                    ScreenUtils.ShowTaskBar(true);
                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                    
                }
                else if (name == ControlID.SETTINGS_BUTTON)
                {

                    this.panels[currentPanel].Visible = false;
                    this.panels[ControlID.SETTINGS_PANEL].Location = new Point(0, 0);
                    this.panels[ControlID.SETTINGS_PANEL].BringToFront();
                    this.panels[ControlID.SETTINGS_PANEL].Visible = true;
                    this.panels[ControlID.SETTINGS_PANEL].Dock = DockStyle.None;
                    this.currentPanel = ControlID.SETTINGS_PANEL;
                }
                else if (name == ControlID.CONNECT_BUTTON)
                {
       
                          

                    if (Core._Registered)
                    {
                        if (!wocketsConnected)
                            Core.Connect(wocketsKernelGuid);
                        else
                            MessageBox.Show("Wockets Already Connected!");
                    }else
                        MessageBox.Show("Application not registered!");

                }
                else if (name == ControlID.DISCONNECT_BUTTON)
                {
                    if (wocketsConnected)
                    {
                        Core.Disconnect(wocketsKernelGuid);
                        plotter = null;
                    }
                    else
                        MessageBox.Show("Wockets Already Disconnected!");
                }
                else if (name == ControlID.LINE_CHART_BUTTON)
                {
                    if (wocketsConnected)
                    {                        
                        //plotterTimer.Enabled = true;
                        this.panels[currentPanel].Visible = false;
                        this.panels[ControlID.PLOTTER_PANEL].Location = new Point(0, 0);
                        this.panels[ControlID.PLOTTER_PANEL].BringToFront();
                        this.panels[ControlID.PLOTTER_PANEL].Visible = true;
                        this.panels[ControlID.PLOTTER_PANEL].Dock = DockStyle.None;
                        this.currentPanel = ControlID.PLOTTER_PANEL;

                        UpdatePlotter();

                    }
                    else
                        MessageBox.Show("Cannot plot without connecting wockets!");

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
                    this.panels[ControlID.SETTINGS_PANEL].Visible = false;
                    this.panels[ControlID.WOCKETS_PANEL].Location = new Point(0, 0);
                    //this.panels[ControlID.WOCKETS_PANEL].BringToFront();                   
                    this.panels[ControlID.WOCKETS_PANEL].Visible = true;
                    this.panels[ControlID.WOCKETS_PANEL].Dock = DockStyle.None;
                    this.currentPanel = ControlID.WOCKETS_PANEL;
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
                for (int x = Screen.PrimaryScreen.WorkingArea.Width; (x >=0 ); x -= 100)
                {
                    this.panels[currentPanel].Location = new Point(x, this.panels[currentPanel].Location.Y);
                    //this.panels[currentPanel]._Backbuffer = this._backBuffers[currentPanel];
                    this.panels[currentPanel].Update();
                }

                this.panels[currentPanel].Location = new Point(0, this.panels[currentPanel].Location.Y);
                this.panels[prevPanel].Visible = false;
            }
        }


       /* protected override void OnPaintBackground(PaintEventArgs e)
        {
            // Prevent flicker, we will take care of the background in OnPaint()
        }*/

        protected override void OnPaint(PaintEventArgs e)
        {          
           // this.Invalidate();
            //SHFullScreen(this.Handle, SHFS_HIDETASKBAR | SHFS_HIDESIPBUTTON | SHFS_HIDESTARTICON);
            _alphaManager.OnPaint(e);
         
        }
    }
}