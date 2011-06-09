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

namespace Wockets
{
    public partial class WocketsQAClarification : Form
    {

        #region INTEROP SERVICES

        [DllImport("coredll")]
        static extern IntPtr GetForegroundWindow();

        [DllImport("coredll")]
        static extern uint GetWindowThreadProcessId(IntPtr hWnd, out int lpdwProcessId);

        #endregion

        #region CONSTRUCTOR

        public WocketsQAClarification()
        {
            InitializeComponent();
        }

        #endregion

        #region INITIALIZATION METHODS

        public void InitializeClarification(int index)
        {
            if (WocketsQA.SelectedCategoriesList.Count > 0)
            {
                menuRight.Enabled = false;
                DataRow dr = null;
                string activity = WocketsQA.SelectedCategoriesList[index];
                try
                {
                    dr = WocketsQA.QuestionTable.Select(WocketsQA.CATEGORIES_COLUMN + " = '" + activity + "'")[0];
                    if (dr[WocketsQA.CLARIFICATION_QUESTION_COLUMN].ToString() == "")
                        dr = null;
                }
                catch { }
                if (dr != null)
                {
                    initializeHeader(dr[WocketsQA.CLARIFICATION_QUESTION_COLUMN].ToString(), activity);
                    initializeClarificationListBox(dr);
                }
            }
        }

        private void initializeHeader(string followup, string activity)
        {
            head1.Text = followup;
            head2.Text = activity;
        }

        private void initializeClarificationListBox(DataRow followupDR)
        {
            clarificationListBox.Items.Clear();
            foreach(string s in followupDR[WocketsQA.SOURCE_ACTIVITIES_COLUMN].ToString().Split('|'))
                if (s != "")
                    clarificationListBox.Items.Add(s);
        }

        #endregion

        #region DATA METHODS

        private void logSelectedActivities()
        {
            WocketsQA.LogResponse(WocketsQA.ALTERNATE_ACTIVITIES_COLUMN, "", false);
            if (WocketsQA.SelectedActivitiesList.Count == 1)
                WocketsQA.LogResponse(WocketsQA.PRIMARY_ACTIVITY_COLUMN, WocketsQA.SelectedActivitiesList[0].ToString(), false);
            else
                foreach (string s in WocketsQA.SelectedActivitiesList)
                    WocketsQA.LogResponse(WocketsQA.ALTERNATE_ACTIVITIES_COLUMN, s, true);
        }

        #endregion

        #region MENU EVENT HANDLERS

        private void menuLeft_Click(object sender, EventArgs e)
        {
            if (WocketsQA.SelectedActivitiesList.Count > 0)
            {
                WocketsQA.SelectedActivitiesList.RemoveAt(WocketsQA.SelectedActivitiesList.Count - 1);
                this.InitializeClarification(WocketsQA.SelectedActivitiesList.Count);
                WocketsQA.wqaCategories.Hide();
                WocketsQA.wqaWinnow.Hide();
                WocketsQA.wqaClarification.Show();
            }
            else
            {
                WocketsQA.wqaCategories.Show();
                WocketsQA.wqaWinnow.Hide();
                WocketsQA.wqaClarification.Hide();
            }
        }

        private void menuRight_Click(object sender, EventArgs e)
        {
            WocketsQA.SelectedActivitiesList.Add(clarificationListBox.SelectedItem.ToString());
            if (WocketsQA.SelectedActivitiesList.Count < WocketsQA.SelectedCategoriesList.Count)
            {
                this.InitializeClarification(WocketsQA.SelectedActivitiesList.Count);
            }
            else
            {
                logSelectedActivities();
                if (WocketsQA.SelectedActivitiesList.Count > 1)
                {
                    WocketsQA.wqaWinnow.InitializeWinnowing(WocketsQA.SelectedActivitiesList.ToArray());
                    WocketsQA.wqaWinnow.Show();
                }
                else
                {
                    WocketsQA.HideAllPages();
                }
            }
            WocketsQA.RetryCount = WocketsQA.RETRY_COUNT + 1;   // cancel retry scheduling on timeout
        }

        #endregion

        #region LISTBOX EVENT HANDLERS

        private void clarificationListBox_SelectedIndexChanged(object sender, EventArgs e)
        {
            menuRight.Enabled = true;
        }

        #endregion

        #region FORM EVENT HANDLERS

        private void WocketsQAClarification_Activated(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
            WocketsQA.RetryTimeCounter = 0;
        }

        private void WocketsQAClarification_MouseDown(object sender, MouseEventArgs e)
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