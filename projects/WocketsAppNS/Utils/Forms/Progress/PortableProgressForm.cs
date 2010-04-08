using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace WocketsAppNS.Utils.Forms.Progress
{
    public partial class PortableProgressForm : Form
    {
        public PortableProgressForm()
        {
            InitializeInterface();
        }


        public void UpdateProgressBar(string description)
        {
            this.AppendLog(description);
            this.Update();
            progressBar.MarqueeUpdate();
        }

        public void UpdateProgressBar()
        {
            this.Update();
             progressBar.MarqueeUpdate();
 
        }
        private void marqueeTimer_Tick(object sender, EventArgs e)
        {

            progressBar.MarqueeUpdate();
        }
    }
}