using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.Drawing;
using WocketsApplication.Controls.Alpha;
using Wockets.Kernel.Types;
using Wockets.Kernel;

namespace WocketsApplication.Controls
{
    public class WocketListItem: AlphaPanel
    {
        public Label Title;
        public Label Mac;
        public Label Status;
        public int Index;
        private AlphaPictureBox backBox;
        //private AlphaPictureBox commandButton;
        private AlphaPictureBox addButton;
        private AlphaPictureBox removeButton;

        private Pen borderPen = new Pen(Color.DarkGray,1.0f);



        //Wockets Configuration Information
        //Bluetooth Screen
        public string _MacAddress="";
        public string _Name = "";
        public string _PIN = "";
        public BaudRates _BaudRate = BaudRates.BR38400;
        public TransmissionPowers _TransmissionPower = TransmissionPowers.TP12dBm;
        public SleepModes _SleepMode = SleepModes.NoSleep;

        //Accelerometer
        public Sensitivities _Sensitivity = Sensitivities.Sensitivity4G;
        public Calibration _Calibration = new Calibration();
        public SamplingRates _SR = SamplingRates.SR90Hz;

        //General
        public Placements _Placement = Placements.NotSelected;

        //Timers
        public Timeouts _ConfigurationTimeout = Timeouts.Never;
        public Timeouts _PowerDownTimeout = Timeouts.Minutes30;

        //Status
        public ushort BatteryLevel = 0;
        public ushort PacketCount = 0;

        //MMF Access
        public string _MMF = "";
        public int _MMF_SIZE = 4096;
        
        public WocketListItem(string name,string mac, int index)
        {
            this.Width = Screen.PrimaryScreen.WorkingArea.Width;
            this.Height = Screen.PrimaryScreen.WorkingArea.Height / 4;
            this.BackColor = Color.FromArgb(245, 219, 186);           
            this._ClearCanvas = true;
            _MacAddress = mac;
            _Name = name;
            
            this._Backbuffer = new Bitmap(this.Width, this.Height);
            Title = new Label();
            Mac = new Label();
            Status = new Label();
            Title.Text =  index +". "+ name;
            Title.ForeColor = Color.Black;
            Title.Font = new Font(FontFamily.GenericSansSerif, 10.0f, FontStyle.Bold);
            Title.Location = new Point(10, 10);
            Title.Size = new Size(450,30);
            Mac.Text = mac;
            Mac.ForeColor = Color.Black;
            Mac.Font = new Font(FontFamily.GenericSansSerif, 8.0f, FontStyle.Regular);
            Mac.Location = new Point(10, 40);
            Mac.Size = new Size(250, 30);
            Status.Text = "Ready";
            Status.Font = new Font(FontFamily.GenericSansSerif, 8.0f, FontStyle.Bold | FontStyle.Italic);
            Status.Location = new Point(350, 10);
            Status.Size = new Size(150, 30);
            Status.ForeColor = Color.Black;

            backBox = new AlphaPictureBox();            
            backBox.Size = new Size(400,60);
            backBox.BackColor = Color.FromArgb(250, 237, 221);           
            backBox.Location = new Point(50,75);
            backBox.Visible = true;
            backBox.Alpha = 255;
           

            /*commandButton = new AlphaPictureBox();
            commandButton.Size = new Size(48, 48);
            commandButton.Image = AlphaImage.CreateFromFile(Constants.PATH + "Buttons\\CommandUnpressed.png");
            commandButton.Visible = true;
            commandButton.Location = new Point(200, 80);*/

            addButton = new AlphaPictureBox();
            addButton.Size = new Size(48, 48);           
            addButton.Image = AlphaImage.CreateFromFile(Constants.PATH + "Buttons\\AddUnpressed.png");
            addButton.Visible = true;
            addButton.Location=  new Point(200, 80);


            removeButton = new AlphaPictureBox();
            removeButton.Size = new Size(48, 48);
            removeButton.Image = AlphaImage.CreateFromFile(Constants.PATH + "Buttons\\RemoveUnpressed.png");
            removeButton.Visible = true;
            removeButton.Location = new Point(400, 80);




            this.MouseDown +=new MouseEventHandler(WocketListItem_MouseDown);
            //this.MouseUp += new MouseEventHandler(WocketListItem_MouseUp);

            this.Controls.Add(Title);
            this.Controls.Add(Mac);
            this.Controls.Add(Status);
            //this.Controls.Add(commandButton);
            this.Controls.Add(addButton);
            this.Controls.Add(removeButton);
            this.Controls.Add(backBox);                      

        }

        public bool AddHitTest(int x, int y)
        {
            if ( (x>(addButton.Location.X-10)) && (x<(addButton.Location.X+addButton.Width+10)))
                return true;
            else
                return false;            
        }

        public bool RemoveHitTest(int x, int y)
        {
            if ((x > (removeButton.Location.X - 10)) && (x < (removeButton.Location.X+removeButton.Width + 10)))
                return true;
            else
                return false;            
//            return removeButton.HitTest(x, y);
        }

        void s_SelectedIndexChanging(object sender, System.ComponentModel.CancelEventArgs e)
        {
        }

        void WocketListItem_MouseUp(object sender, MouseEventArgs e)
        {
            //((WocketSlidingList)this.Parent).WocketSlidingList_MouseUp(sender, e);
        }

        public int LastX = 0;
        public int LastY = 0;
        void WocketListItem_MouseDown(object sender, MouseEventArgs e)
        {
            LastX = e.X;
            LastY = e.Y;
            //((WocketSlidingList)this.Parent).WocketSlidingList_MouseDown(sender, e);

        }



        protected override void OnPaint(PaintEventArgs e)
        {
                       
            base.OnPaint(e);
            e.Graphics.DrawLine(borderPen, 0, 0, this.Width, 0);
            e.Graphics.DrawLine(borderPen, 0, this.Height - 1, this.Width, this.Height - 1); 
        }

    }
}
