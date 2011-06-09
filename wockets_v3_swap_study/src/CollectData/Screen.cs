using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets.Kernel;
using System.Threading;
using Wockets;
using Wockets.Receivers;

namespace CollectData
{
    public partial class Screen : Form
    {

        private Panel[] wocketPanels = new Panel[2];
        private Rectangle ScreenSize = new Rectangle(0, 0, System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width, System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height);
        private Screen5 mainPanel;
        public Screen()
        {
            InitializeComponent();
            Screens.screen = this;
            Core.WRITE_LAST_UPLOAD_FAILEDFILES(0);
            Core.WRITE_LAST_UPLOAD_SUCCESSFILES(0);
            Core.WRITE_LAST_UPLOAD_NEWFILES(0);

            for (int i = 0; (i < 2); i++)
            {
                Core.WRITE_FULL_RECEIVED_COUNT(i, 0);
                Core.WRITE_PARTIAL_RECEIVED_COUNT(i, 0);
                Core.WRITE_EMPTY_RECEIVED_COUNT(i, 0);
                Core.WRITE_RECEIVED_ACs(i, -1);
                Core.WRITE_SAVED_ACs(i, -1);             
            }

            this.screen51.Start();

        }


        public void EnableMenu()
        {
            this.menuItem1.Enabled = true;
        }
        public void GoPanel51()
        {
            this.screen51.BringToFront();
            this.screen51.Location = new Point(0, 0);
            this.screen51.Visible = true;
            this.screen51.Enabled = true;         
        }
        
        public void GoPanel61(int wocket_id)
        {
            this.screen61._ID = wocket_id;
            Core.READ_MAC();
            Core.READ_EMPTY_RECEIVED_COUNT();
            Core.READ_FULL_RECEIVED_COUNT();
            Core.READ_PARTIAL_RECEIVED_COUNT();



            this.screen61.Start();
            this.screen61.BringToFront();
            this.screen61.Location = new Point(0, 0);
            this.screen61.Visible = true;
            this.screen61.Enabled = true;            
        }
        protected override void OnActivated(EventArgs e)
        {
            base.OnActivated(e);
            this.screen51.Start();
            this.screen61.Stop();           
        }

        protected override void OnDeactivate(EventArgs e)
        {
            base.OnDeactivate(e);
            this.screen51.Stop();
        }
        private void menuItem1_Click(object sender, EventArgs e)
        {
            if (MessageBox.Show("Are you sure you want to exit?", "Confirm", MessageBoxButtons.YesNo, MessageBoxIcon.Question, MessageBoxDefaultButton.Button1) == DialogResult.Yes)
            {
                this.screen51.Stop();
                Core.Unregister();
                Core.Terminate();

                if (!Core._KernalStarted)
                {
                    Application.Exit();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
            }

        }


    }
}