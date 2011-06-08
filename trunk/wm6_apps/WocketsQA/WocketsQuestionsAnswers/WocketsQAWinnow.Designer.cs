namespace WocketsQuestionsAnswers
{
    partial class WocketsQAWinnow
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
            this.menuLeft = new System.Windows.Forms.MenuItem();
            this.menuRight = new System.Windows.Forms.MenuItem();
            this.head2 = new System.Windows.Forms.Label();
            this.head1 = new System.Windows.Forms.Label();
            this.winnowListBox = new System.Windows.Forms.ListBox();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuLeft);
            this.mainMenu1.MenuItems.Add(this.menuRight);
            // 
            // menuLeft
            // 
            this.menuLeft.Text = "Back";
            this.menuLeft.Click += new System.EventHandler(this.menuLeft_Click);
            // 
            // menuRight
            // 
            this.menuRight.Enabled = false;
            this.menuRight.Text = "Next";
            this.menuRight.Click += new System.EventHandler(this.menuRight_Click);
            // 
            // head2
            // 
            this.head2.Font = new System.Drawing.Font("Segoe Condensed", 19F, System.Drawing.FontStyle.Bold);
            this.head2.ForeColor = System.Drawing.Color.White;
            this.head2.Location = new System.Drawing.Point(0, 27);
            this.head2.Name = "head2";
            this.head2.Size = new System.Drawing.Size(240, 37);
            this.head2.Text = "the most time?";
            // 
            // head1
            // 
            this.head1.Font = new System.Drawing.Font("Segoe Condensed", 16F, System.Drawing.FontStyle.Regular);
            this.head1.ForeColor = System.Drawing.Color.White;
            this.head1.Location = new System.Drawing.Point(0, 0);
            this.head1.Name = "head1";
            this.head1.Size = new System.Drawing.Size(240, 29);
            this.head1.Text = "In which did you spend";
            // 
            // winnowListBox
            // 
            this.winnowListBox.Anchor = ((System.Windows.Forms.AnchorStyles)((((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Bottom)
                        | System.Windows.Forms.AnchorStyles.Left)
                        | System.Windows.Forms.AnchorStyles.Right)));
            this.winnowListBox.BackColor = System.Drawing.Color.Black;
            this.winnowListBox.Font = new System.Drawing.Font("Segoe Condensed", 16F, System.Drawing.FontStyle.Regular);
            this.winnowListBox.ForeColor = System.Drawing.Color.White;
            this.winnowListBox.Location = new System.Drawing.Point(3, 75);
            this.winnowListBox.Name = "winnowListBox";
            this.winnowListBox.Size = new System.Drawing.Size(237, 202);
            this.winnowListBox.TabIndex = 10;
            this.winnowListBox.SelectedIndexChanged += new System.EventHandler(this.winnowListBox_SelectedIndexChanged);
            // 
            // WocketsQAWinnow
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.BackColor = System.Drawing.Color.Black;
            this.ClientSize = new System.Drawing.Size(240, 294);
            this.Controls.Add(this.winnowListBox);
            this.Controls.Add(this.head2);
            this.Controls.Add(this.head1);
            this.Location = new System.Drawing.Point(0, 0);
            this.Menu = this.mainMenu1;
            this.Name = "WocketsQAWinnow";
            this.Text = "Wockets Q&A";
            this.WindowState = System.Windows.Forms.FormWindowState.Maximized;
            this.Activated += new System.EventHandler(this.WocketsQAWinnow_Activated);
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.MenuItem menuLeft;
        private System.Windows.Forms.Label head2;
        private System.Windows.Forms.Label head1;
        private System.Windows.Forms.MenuItem menuRight;
        private System.Windows.Forms.ListBox winnowListBox;

    }
}

