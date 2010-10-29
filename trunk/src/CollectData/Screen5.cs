using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Utils;
using System.Threading;
using Microsoft.WindowsCE.Forms;
using System.IO;
using System.Diagnostics;
using Wockets.Kernel;
using Wockets.Kernel.Types;
using Wockets;
using System.Runtime.InteropServices;
using Wockets.Utils.IPC;
using Wockets.Receivers;

namespace CollectData
{
    public partial class Screen5 : Panel
    {
        private Thread timerThread;
        private HardwareButton hwb1;
        private static System.Diagnostics.Process _UploaderProcess = null;
        public Screen5()
        {
            InitializeComponent();
            

            this.label25.Text = "Sensor 0";
            this.label24.Text = "Sensor 1";
            this.label8.Text = CurrentPhone._IMEI;
            //Core.SubscribeEvent(KernelResponse.UPLOAD_UPDATED, EventListener);
            // Create event-handler delegate for the KeyUp
            // event for this form. This form is associated
            // with each of the hardware buttons, and the
            // event occurs when a hardware button is pressed.
            // Note that you could also use the KeyDown event
            // instead of the KeyUp event.
            //this.KeyPreview = true;
            //this.KeyUp += new KeyEventHandler(this.OnKeyUp);

            // Call the method to configure
            // the hardware button.
            HBConfig();


            this.label2.Text = Settings._SessionStart.ToString("dddd, MMM. d, yyyy h:mm tt");


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
                        Directory.CreateDirectory(firstCard + "\\writable");
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
            Settings._StorageDirectory = firstCard;




            //Update the storage progress bar
            DiskSpace space1 = Memory.GetDiskSpace(Settings._StorageDirectory);
            int remainingStorage=(int)(space1.TotalNumberOfBytes /  System.Math.Pow(2, 20));
            this.label7.Text = remainingStorage.ToString("00") + " MB";
            this.progressBar1._Value = (int)(((space1.TotalNumberOfBytes - space1.FreeBytesAvailable) / (double)space1.TotalNumberOfBytes)*100);

            //Update the expected remaining time
            double remainingTime = (remainingStorage / 1.5); //in hrs
            if (remainingTime > 48)
                this.label10.Text = "("+(int)(remainingTime/24)+"+ days remaining)";
            else if (remainingTime>2)
                this.label10.Text = "(" + (int)remainingTime + "+ hours remaining)";
            else                
                this.label10.Text = "(" + (int)(remainingTime*60.0) + "+ mins remaining)";
            //Update progress bar color
            if (remainingTime < 48) // 2 days
                this.progressBar1._ForeColor = Color.Red;
            else if (remainingTime < 336) // 1 Week
                this.progressBar1._ForeColor = Color.Yellow;
            else //More than 1 week
                this.progressBar1._ForeColor = Color.Green;

            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
            //Update Battery Percent
            try
            {               
                this.label6.Text = bpower.BatteryLifePercent + "%";                
            }
            catch { }

            //update battery picture
            try
            {
                //update battery picture
                if (bpower.BatteryLifePercent >= 90)
                    this.pictureBox2.Image = System.Drawing.Image.FromHbitmap(BatteryImages.B100.GetHbitmap());
                else if (bpower.BatteryLifePercent >= 70)
                    this.pictureBox2.Image = System.Drawing.Image.FromHbitmap(BatteryImages.B80.GetHbitmap());
                else if (bpower.BatteryLifePercent >= 50)
                    this.pictureBox2.Image = System.Drawing.Image.FromHbitmap(BatteryImages.B60.GetHbitmap());
                else if (bpower.BatteryLifePercent >= 30)
                    this.pictureBox2.Image = System.Drawing.Image.FromHbitmap(BatteryImages.B40.GetHbitmap());
                else if (bpower.BatteryLifePercent >= 20)
                    this.pictureBox2.Image = System.Drawing.Image.FromHbitmap(BatteryImages.B20.GetHbitmap());
                else
                    this.pictureBox2.Image = System.Drawing.Image.FromHbitmap(BatteryImages.B10.GetHbitmap());
            }
            catch { }
        }


        public void Start()
        {
            timerThread = new Thread(new ThreadStart(TimerThread));
            timerThread.Start();
        }

        public void Stop()
        {
            if (timerThread!=null)
                timerThread.Abort();
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
                        case KernelResponse.UPLOAD_UPDATED:

                            break;
                    }
                }
            }
            catch
            {
            }
        }
        delegate void UpdateTimeCallback();
        private bool disposed = false;
        private int counter = 0;
        public void UpdateTime()
        {
            if (!disposed)
            {
                if (label3.InvokeRequired)
                // InvokeRequired required compares the thread ID of the
                // calling thread to the thread ID of the creating thread.
                // If these threads are different, it returns true.
                {
                    UpdateTimeCallback d = new UpdateTimeCallback(UpdateTime);
                    this.Invoke(d, new object[] { });
                }
                else
                {
                    this.label3.Text = _Label3;

                    counter++;

                    if (counter == 5)
                    {
                        Core.READ_LAST_UPLOAD_DURATION();
                        Core.READ_LAST_UPLOAD_FAILEDFILES();
                        Core.READ_LAST_UPLOAD_NEWFILES();
                        Core.READ_LAST_UPLOAD_SUCCESSFILES();
                        Core.READ_LAST_UPLOAD_TIME();
                        this.label17.Text = "(" + CurrentWockets._UploadNewFiles + " new files)";
                        if (CurrentWockets._UploadLastTime.Year != 1961)
                        {
                            TimeSpan duration = DateTime.Now.Subtract(CurrentWockets._UploadLastTime);
                            if (duration.TotalDays >= 2)
                            {
                                this.label15.Text = "(" + (int)duration.TotalDays + " days ago)";
                                this.label15.ForeColor = Color.DarkRed;
                            }
                            else if (duration.TotalHours > 2)
                            {
                                this.label15.Text = "(" + (int)duration.TotalDays + " hours ago)";
                                this.label15.ForeColor = Color.Black;
                            }
                            else
                            {
                                this.label15.Text = "(" + (int)duration.TotalMinutes + " mins ago)";
                                this.label15.ForeColor = Color.Black;
                            }
                        }
                        else
                        {
                            this.label15.Text = "Never";
                            this.label15.ForeColor = Color.Black;
                        }
                        this.label19.Text = CurrentWockets._UploadDuration;
                        this.label18.Text = CurrentWockets._UploadSuccessFiles + " successful";
                        this.label20.Text = CurrentWockets._UploadFailedFiles + " failed";
                        counter = 0;

                        try
                        {
                            ProcessInfo[] processes = ProcessCE.GetProcesses();
                            if (processes != null)
                            {
                                bool found = false;
                                for (int i = 0; (i < processes.Length); i++)
                                {
                                    if (processes[i].FullPath.IndexOf("DataUploader.exe") >= 0)
                                        found = true;                                  
                                }
                                this.button1.Enabled = !found;
                            }
                        }
                        catch { }
                        if ((!this.button1.Enabled)&& (_UploaderProcess!=null) && (_UploaderProcess.HasExited))
                            this.button1.Enabled = true;

                                           
                        try
                        {
                            SYSTEM_POWER_STATUS_EX2 bpower = Battery.GetSystemPowerStatus();
                            this.label6.Text = bpower.BatteryLifePercent + "%";
                        }
                        catch { }
                    }

                    this.Invalidate();
                }
            }
        }

        private string _Label3 = "";
        private void TimerThread()
        {            
            while (true)
            {
                TimeSpan duration=DateTime.Now.Subtract(Settings._SessionStart);
                _Label3 = duration.Hours.ToString("00") + "h:" + duration.Minutes.ToString("00") + "m:" + duration.Seconds.ToString("00") + "s";
                 UpdateTime();
              
                Thread.Sleep(500);

            }
        }

        // Configure hardware buttons
        // 1 and 4 to activate the current form.
        private void HBConfig()
        {
            try
            {
                hwb1 = new HardwareButton();            
                hwb1.AssociatedControl = this;                
                hwb1.HardwareKey = HardwareKeys.ApplicationKey5;                
            }
            catch (Exception exc)
            {
                MessageBox.Show(exc.Message + " Check if the hardware button is physically available on this device.");
            }
        }

        // When a hardware button is pressed and released,
        // this form receives the KeyUp event. The OnKeyUp
        // method is used to determine which hardware
        // button was pressed, because the event data
        // specifies a member of the HardwareKeys enumeration.
        private void OnKeyUp(object sender, KeyEventArgs e)
        {
            switch ((HardwareKeys)e.KeyCode)
            {
                case HardwareKeys.ApplicationKey5:
                    MessageBox.Show("TEST1");
                    break;

                case HardwareKeys.ApplicationKey4:
                    MessageBox.Show("TEST4");
                    break;

                default:
                    break;
            }
        }


        private void label13_ParentChanged(object sender, EventArgs e)
        {

        }
        [DllImport("coredll.dll")]
        static extern int ShowWindow(IntPtr hWnd, int nCmdShow);
        const int SW_MINIMIZED = 6;
        private void pictureBox5_Click(object sender, EventArgs e)
        {
            ShowWindow(Screens.screen.Handle, SW_MINIMIZED);
        }


        private void button1_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Do you want to upload your data now?", "",
                        MessageBoxButtons.YesNo,
                        MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                try
                {
                    //System.Diagnostics.Process po = new System.Diagnostics.Process();
                    ProcessStartInfo startInfo = new ProcessStartInfo();
                    startInfo.WorkingDirectory = Core.KERNEL_PATH;
                    startInfo.FileName = Core.KERNEL_PATH + "DataUploader.exe";
                    startInfo.UseShellExecute = false;                    
                    _UploaderProcess = System.Diagnostics.Process.Start(startInfo.FileName, "");
                    this.button1.Enabled = false;
                }
                catch 
                {
                 
                }
            }
        }


        void pictureBox4_Click(object sender, System.EventArgs e)
        {
            Screens.screen.GoPanel61(1);
           
        }
        private void pictureBox3_Click(object sender, EventArgs e)
        {           
            //this.pictureBox3.Enabled = false;
            Screens.screen.GoPanel61(0);
            
        }
    }
}