using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

using System.Threading;
using System.Collections;

using MobiRnD_RDT.Logging;

namespace MobiRnD_RDT.RemoteUpdater
{


    public partial class Form1 : Form
    {
        Thread _threadUpdater;
        bool _isThreadRunning = false;
        Updater _updater = new Updater();
        Settings _settings = new Settings();


        string _statusText = "";
        string _logText = "";


        //Create Form
        public Form1(string[] args)
        {
            InitializeComponent();

            this.Size = new Size(Screen.PrimaryScreen.Bounds.Width,Screen.PrimaryScreen.Bounds.Height);

            //Suscribe to events
            _updater.StatusChanged += new StatusHandler(StatusChanged);
            _updater.LogErrorGenerated +=new LogErrorHandler(LogErrorGenerated);
            _settings.LogErrorGenerated += new LogErrorHandler(LogErrorGenerated);
            _updater.LogItemGenerated += new LogHandler(LogItemGenerated);

            //Launch thread
            ThreadStart startUpdater = new ThreadStart(RunUpdater);
            _threadUpdater = new Thread(startUpdater);
            _threadUpdater.IsBackground = true;


            //Check in the args the app to update
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
            else //if not arguments
            {
                Logger.LogDebug("Form1", "insufficient command line arguments count " + args.Length);
                
                //if no arguments, check for settings file
                if (_settings.Load())
                {
                    Logger.LogDebug("Form1", "get settings from XML files");
                }

            }

        }



        #region HANDLE EVENTS

        void LogErrorGenerated(string codeLocation, Exception ex)
        {
            Logger.LogError(codeLocation, ex);
        }

        void LogItemGenerated(string logevent)
        {
            Logger.LogInfo(logevent);
            _logText = logevent;
        }

        void StatusChanged(string status)
        {
            _statusText = status;
        }

        #endregion




        void RunUpdater()
        {
            //List the apps to update
            for (int i = 0; i < _settings.ApplicationsToUpdate.Count; i++)
            {
                AppToUpdate app = (AppToUpdate)_settings.ApplicationsToUpdate[i];
                Logger.LogInfo(app.ToString());

                //Get the files to update info
                _updater.ApplicationExe = app.ApplicationExe;
                _updater.ApplicationFolderPath = app.ApplicationFolder;
                _updater.RetrieveUpdates(app.URLs);

                // Check ig the app is ready for an update(process not running),
                // If so, update the app
                if (_updater.IsReadyToUpdate())
                    _updater.UpdateApplication();
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
            if (!_isThreadRunning) this.Close();
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




        //Stop Update Button
        private void menuItem1_Click(object sender, EventArgs e)
        {
            //Close from meu
            lbStatus.Text = "Stopping update...";
            Logger.Close();
            this.Close();
        }


    }
}