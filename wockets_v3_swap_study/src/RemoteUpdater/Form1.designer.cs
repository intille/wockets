namespace MobiRnD_RDT.RemoteUpdater
{
    partial class Form1
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;
        private System.Windows.Forms.MainMenu mainMenu1;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.mainMenu1 = new System.Windows.Forms.MainMenu();
            this.menuItem1 = new System.Windows.Forms.MenuItem();
            this.lbStatus = new System.Windows.Forms.Label();
            this.lbLog = new System.Windows.Forms.Label();
            this.timer1 = new System.Windows.Forms.Timer();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "Stop";
            this.menuItem1.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // lbStatus
            // 
            this.lbStatus.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.lbStatus.Location = new System.Drawing.Point(13, 14);
            this.lbStatus.Name = "lbStatus";
            this.lbStatus.Size = new System.Drawing.Size(215, 77);
            this.lbStatus.Text = "Status";
            // 
            // lbLog
            // 
            this.lbLog.Font = new System.Drawing.Font("Tahoma", 10F, System.Drawing.FontStyle.Regular);
            this.lbLog.Location = new System.Drawing.Point(13, 91);
            this.lbLog.Name = "lbLog";
            this.lbLog.Size = new System.Drawing.Size(215, 115);
            this.lbLog.Text = "Log";
            // 
            // timer1
            // 
            this.timer1.Tick += new System.EventHandler(this.timer1_Tick);
            // 
            // Form1
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.Controls.Add(this.lbLog);
            this.Controls.Add(this.lbStatus);
            this.Menu = this.mainMenu1;
            this.Name = "Form1";
            this.Text = "Updater";
            this.Load += new System.EventHandler(this.Form1_Load);
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Label lbStatus;
        private System.Windows.Forms.Label lbLog;
        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.Timer timer1;
    }
}

