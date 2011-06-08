namespace Wockets
{
    partial class WocketsPowerTest
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
            this.head1 = new System.Windows.Forms.Label();
            this.head2 = new System.Windows.Forms.Label();
            this.versionLabel = new System.Windows.Forms.Label();
            this.retryTimer = new System.Windows.Forms.Timer();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "Quit";
            this.menuItem1.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // head1
            // 
            this.head1.Font = new System.Drawing.Font("Segoe Condensed", 14F, System.Drawing.FontStyle.Bold);
            this.head1.ForeColor = System.Drawing.Color.White;
            this.head1.Location = new System.Drawing.Point(6, 119);
            this.head1.Name = "head1";
            this.head1.Size = new System.Drawing.Size(228, 42);
            this.head1.Text = "Wockets Power Test";
            this.head1.TextAlign = System.Drawing.ContentAlignment.TopCenter;
            // 
            // head2
            // 
            this.head2.Font = new System.Drawing.Font("Segoe Condensed", 14F, System.Drawing.FontStyle.Regular);
            this.head2.ForeColor = System.Drawing.Color.White;
            this.head2.Location = new System.Drawing.Point(6, 161);
            this.head2.Name = "head2";
            this.head2.Size = new System.Drawing.Size(228, 73);
            this.head2.Text = "Starting Test...";
            this.head2.TextAlign = System.Drawing.ContentAlignment.TopCenter;
            // 
            // versionLabel
            // 
            this.versionLabel.Font = new System.Drawing.Font("Segoe Condensed", 9F, System.Drawing.FontStyle.Regular);
            this.versionLabel.ForeColor = System.Drawing.Color.White;
            this.versionLabel.Location = new System.Drawing.Point(6, 10);
            this.versionLabel.Name = "versionLabel";
            this.versionLabel.Size = new System.Drawing.Size(228, 27);
            this.versionLabel.Text = "Version 0.01";
            // 
            // retryTimer
            // 
            this.retryTimer.Enabled = true;
            this.retryTimer.Interval = 1000;
            this.retryTimer.Tick += new System.EventHandler(this.retryTimer_Tick);
            // 
            // WocketsPowerTest
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.BackColor = System.Drawing.Color.Black;
            this.ClientSize = new System.Drawing.Size(240, 294);
            this.Controls.Add(this.versionLabel);
            this.Controls.Add(this.head2);
            this.Controls.Add(this.head1);
            this.FormBorderStyle = System.Windows.Forms.FormBorderStyle.None;
            this.Location = new System.Drawing.Point(0, 0);
            this.Menu = this.mainMenu1;
            this.MinimizeBox = false;
            this.Name = "WocketsPowerTest";
            this.Text = "Wockets Power Test";
            this.WindowState = System.Windows.Forms.FormWindowState.Maximized;
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Label head1;
        private System.Windows.Forms.Label head2;
        private System.Windows.Forms.Label versionLabel;
        private System.Windows.Forms.Timer retryTimer;
        private System.Windows.Forms.MenuItem menuItem1;

    }
}

