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
    public partial class WocketsQACategories : Form
    {
                        
        public WocketsQACategories()
        {
            InitializeComponent();
        }

        public void initializeListView()
        {
            menuRight.Enabled = false;
            foreach (DataRow dr in WocketsQA.QuestionTable.Rows)
                categoryListView.Items.Add(new ListViewItem(dr[WocketsQA.CATEGORIES_COLUMN].ToString()));
        }

        private void skipQuestion()
        {
            WocketsQA.HideAllPages();
            //WocketsQA.ScheduleNextPrompt();
            WocketsQA.SaveDataLog();
            Program.PermitWocketsSuspension();
            Application.Exit();
        }

        private void showNextForm()
        {
            WocketsQA.LogResponse(WocketsQA.CATEGORIES_COLUMN, "", false);
            WocketsQA.SelectedCategoriesList.Clear();
            WocketsQA.SelectedActivitiesList.Clear();
            foreach (ListViewItem lvi in categoryListView.Items)
            {
                if (lvi.Checked)
                {
                    WocketsQA.SelectedCategoriesList.Add(lvi.Text);
                    WocketsQA.LogResponse(WocketsQA.CATEGORIES_COLUMN, lvi.Text, true);
                }
            }
            WocketsQA.InitializeClarifications();
            this.Hide();
        }

        private void menuLeft_Click(object sender, EventArgs e)
        {
            skipQuestion();
        }

        private void menuRight_Click(object sender, EventArgs e)
        {
            showNextForm();
        }
        
        private void listView_ItemActivate(object sender, EventArgs e)
        {
            if (!categoryListView.FocusedItem.Checked)
            {
                categoryListView.FocusedItem.Checked = true;
                categoryListView.FocusedItem.BackColor = Color.Gray;
                categoryListView.FocusedItem.Selected = false;
                menuRight.Enabled = true;
            }
            else
            {
                categoryListView.FocusedItem.Checked = false;
                categoryListView.FocusedItem.BackColor = Color.Black;
                categoryListView.FocusedItem.Selected = false;
                foreach (ListViewItem lvi in categoryListView.Items)
                    if (lvi.Checked)
                        return;
                menuRight.Enabled = false;
            }
        }

        private void WocketsQACategories_Activated(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
            WocketsQA.RetryTimeCounter = 0;
        }

        [DllImport("coredll")]
        static extern IntPtr GetForegroundWindow();

        [DllImport("coredll")]
        static extern uint GetWindowThreadProcessId(IntPtr hWnd, out int lpdwProcessId);

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

        private void WocketsQACategories_MouseDown(object sender, MouseEventArgs e)
        {
            WocketsQA.RetryTimeCounter = 0;
        }
    }
}