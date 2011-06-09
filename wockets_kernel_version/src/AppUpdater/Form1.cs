using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

using System.Threading;
using System.Collections;

using AppUpdater.Logging;
using SMSLib;



namespace AppUpdater
{
    public partial class Form1 : Form
    {
        Thread _threadUpdater, uploadThread;
        bool _isThreadRunning = false;
        Updater _updater = new Updater();
        Settings _settings = new Settings();

        SMSManager smsMgr;
        String sendControlPrefix = "CMK:";

        //should be integrated into the XML file later.
        private const String urlLog = "http://participate.media.mit.edu/WeightControl/local_logs/";

        public Form1(string[] args)
        {
            InitializeComponent();

            smsMgr = new SMSManager(sendControlPrefix);
            //smsMgr.initializeMsgInterceptor("mitsmsmgr@gmail.com / up /", "CITYAppUpdaterID");
            smsMgr.initializeMsgInterceptor(sendControlPrefix, "CITYAppUpdaterID2");


            // event handler for text
            smsMgr.MessageTextAllReceived += new SMSManager.MessageTextReceivedEventHandler(smsMgr_MessageTextAllReceived);

            this.Size = new Size(Screen.PrimaryScreen.Bounds.Width,Screen.PrimaryScreen.Bounds.Height);

            _updater.StatusChanged += new StatusHandler(StatusChanged);
            _updater.LogErrorGenerated +=new LogErrorHandler(LogErrorGenerated);
            _settings.LogErrorGenerated += new LogErrorHandler(LogErrorGenerated);
            _updater.LogItemGenerated += new LogHandler(LogItemGenerated);

            ThreadStart startUpdater = new ThreadStart(RunUpdater);
            _threadUpdater = new Thread(startUpdater);
            _threadUpdater.IsBackground = true;

            if (args.Length > 2)
            {
                AppToUpdate app = new AppToUpdate();
                app.ApplicationFolder = args[1];
                app.ApplicationExe = args[2];
                app.URLs = new string[args.Length - 3];
                for (int i = 3; i < args.Length; i++)
                    app.URLs[i - 3] = args[i];

                _settings.ApplicationsToUpdate.Add(app);
            }
            else
            {
                Logger.LogDebug("Form1", "insufficient command line arguments count " + args.Length);
                
                //if no arguments, check for settings file
                
                if (_settings.Load())
                {
                    Logger.LogDebug("Form1", "get settings from XML files");
                }

            }

        }

        string _statusText = "";
        string _logText = "";

        #region HANDLE EVENTS
        void LogErrorGenerated(string codeLocation, Exception ex)
        {
            Logger.LogError(codeLocation, ex, true);
        }
        void LogItemGenerated(string logevent)
        {
            Logger.LogInfo("App Updater", logevent, false);
            _logText = logevent;
        }
        void StatusChanged(string status)
        {
            _statusText = status;
        }

        void smsMgr_MessageTextAllReceived(string fullMessage)
        {
            if (fullMessage.Equals("appup"))
            {
                //RunUpdater();
                //This log will not always be sent because it 
                Logger.LogInfo("Started App Updater.", false);
            }
            else if (fullMessage.Equals("sendLog"))
            {
                Logger.LogInfo("Upload log file started.", false);

                Thread uploadThread = new Thread(new ThreadStart(uploadFile));
                
            }
            else
            {
                Logger.LogInfo("Command didn't match anything.", true);
            }
        }
        #endregion

        private void uploadFile()
        {
            Uploader.uploadFile(@"\Program Files\cityproject\logs\" +
            String.Format("{0}_{1}_{2}_{3}{4}", "log", DateTime.Now.Year, DateTime.Now.Month.ToString("00"), DateTime.Now.Day.ToString("00"), ".txt"), urlLog);

            Logger.LogInfo("Upload log file finished.", true);
        }

        void RunUpdater()
        {
            for (int i = 0; i < _settings.ApplicationsToUpdate.Count; i++)
            {
                AppToUpdate app = (AppToUpdate)_settings.ApplicationsToUpdate[i];
                Logger.LogInfo("App Updater", app.ToString(), false);
                _updater.ApplicationExe = app.ApplicationExe;
                _updater.ApplicationFolderPath = app.ApplicationFolder;
                _updater.RetrieveUpdates(app.URLs);
                if (_updater.IsReadyToUpdate())
                    _updater.UpdateApplication();

                _updater.LaunchApplication();
            }
            _isThreadRunning = false;
        }

        #region START UPDATER THREAD
        private void Form1_Load(object sender, EventArgs e)
        {
            //TODO: if no settings file, prompt for values
            StartUpdater();
        }

        private void StartUpdater()
        {
            _isThreadRunning = true;
            timer1.Enabled = true;
            _threadUpdater.Start();
        }

        private void timer1_Tick(object sender, EventArgs e)
        {
            //Check of updater thread is complete
            //on complete, close application
            if (!_isThreadRunning)
            {
                this.Close();
            }
            else
            {
                if (_statusText.Length > 0)
                {
                    lbStatus.Text = _statusText;
                    _statusText = "";
                }
                if (_logText.Length > 0)
                {
                    lbLog.Text = _logText;
                    _logText = "";
                }
            }
        }
        #endregion

        private void menuItem1_Click(object sender, EventArgs e)
        {
            //Close from meu
            lbStatus.Text = "Stopping update...";
            Logger.Close();
            this.Close();
        }

        private void Form1_Closed(object sender, EventArgs e)
        {
            // call this on form closed if a message intercepter is used.
            smsMgr.cleanUpInterceptor();
        }



       

    }
}