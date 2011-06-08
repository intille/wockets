using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Diagnostics;
using System.Runtime.InteropServices;

namespace WocketsQuestionsAnswers
{
    public partial class WocketsQAWinnow : Form
    {

        #region INTEROP SERVICES

        [DllImport("coredll")]
        static extern IntPtr GetForegroundWindow();

        [DllImport("coredll")]
        static extern uint GetWindowThreadProcessId(IntPtr hWnd, out int lpdwProcessId);

        #endregion

        #region CONSTRUCTORS

        public WocketsQAWinnow()
        {
            InitializeComponent();
        }

        #endregion

        #region INITIALIZATION METHODS

        public void InitializeWinnowing(string[] activities)
        {
            this.menuRight.Enabled = false;
            winnowListBox.Items.Clear();
            foreach (string s in activities)
                if (!winnowListBox.Items.Contains(s))
                    winnowListBox.Items.Add(s);
        }

        #endregion

        #region DATA METHODS

        private void logWinnowResponse()
        {
            WocketsQA.LogResponse(WocketsQA.PRIMARY_ACTIVITY_COLUMN, winnowListBox.SelectedItem.ToString(), false);
        }

        #endregion

        #region LISTBOX EVENTS

        private void winnowListBox_SelectedIndexChanged(object sender, EventArgs e)
        {
            menuRight.Enabled = true;
        }

        #endregion

        #region MENU EVENTS

        private void menuLeft_Click(object sender, EventArgs e)
        {
            WocketsQA.SelectedActivitiesList.RemoveAt(WocketsQA.SelectedActivitiesList.Count - 1);
            WocketsQA.wqaClarification.InitializeClarification(WocketsQA.SelectedActivitiesList.Count);
            WocketsQA.wqaCategories.Hide();
            WocketsQA.wqaWinnow.Hide();
            WocketsQA.wqaClarification.Show();
        }

        private void menuRight_Click(object sender, EventArgs e)
        {
            logWinnowResponse();
            WocketsQA.HideAllPages();
            WocketsQA.RetryCount = WocketsQA.RETRY_COUNT + 1;   // cancel retry scheduling on timeout
        }

        #endregion

        #region FORM METHODS

        private void WocketsQAWinnow_Activated(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
            WocketsQA.RetryTimeCounter = 0;
        }

        private void WocketsQAWinnow_MouseDown(object sender, MouseEventArgs e)
        {
            WocketsQA.RetryTimeCounter = 0;
        }

        #endregion

        #region OVERRIDES
            
        protected override void OnDeactivate(EventArgs e)
        {
            base.OnDeactivate(e);

            //if the foreground window was not created by this application, exit this application
            IntPtr foregroundWindow = GetForegroundWindow();
            int foregroundProcId;
            GetWindowThreadProcessId(foregroundWindow, out foregroundProcId);
            using (Process currentProc = Process.GetCurrentProcess())
            {
                if (foregroundProcId != currentProc.Id)
                {
                    WocketsQA.ScheduleRetry();
                    WocketsQA.SaveDataLog();
                    Program.PermitWocketsSuspension();
                    Application.Exit();
                }
            }
        }

        #endregion

    }
}