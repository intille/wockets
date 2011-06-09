namespace CollectData
{
    partial class Screen2
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
            this.spinningProgress1 = new CircularProgress.SpinningProgress.SpinningProgress();
            this.label1 = new System.Windows.Forms.Label();
            this.label2 = new System.Windows.Forms.Label();
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.SuspendLayout();
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "";
            // 
            // spinningProgress1
            // 
            this.spinningProgress1.ActiveSegmentColour = System.Drawing.Color.FromArgb(((int)(((byte)(35)))), ((int)(((byte)(146)))), ((int)(((byte)(33)))));
            this.spinningProgress1.AutoIncrementFrequency = 100;
            this.spinningProgress1.Location = new System.Drawing.Point(32, 241);
            this.spinningProgress1.Name = "spinningProgress1";
            this.spinningProgress1.Size = new System.Drawing.Size(425, 298);
            this.spinningProgress1.TabIndex = 0;
            this.spinningProgress1.TransistionSegment = 0;
            this.spinningProgress1.TransistionSegmentColour = System.Drawing.Color.FromArgb(((int)(((byte)(129)))), ((int)(((byte)(242)))), ((int)(((byte)(121)))));
            // 
            // label1
            // 
            this.label1.Font = new System.Drawing.Font("Tahoma", 24F, System.Drawing.FontStyle.Regular);
            this.label1.Location = new System.Drawing.Point(32, 86);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(425, 72);
            this.label1.Text = "Please wait...";
            // 
            // label2
            // 
            this.label2.Font = new System.Drawing.Font("Tahoma", 16F, System.Drawing.FontStyle.Regular);
            this.label2.Location = new System.Drawing.Point(163, 340);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(171, 101);
            this.label2.Text = "Starting wockets";
            this.label2.TextAlign = System.Drawing.ContentAlignment.TopCenter;
            // 
            // menuItem2
            // 
            this.menuItem2.Text = "";
            // 
            // Screen2
            // 
            this.Controls.Add(this.label2);
            this.Controls.Add(this.label1);
            this.Controls.Add(this.spinningProgress1);
            this.Location = new System.Drawing.Point(0, 52);
            this.Size = new System.Drawing.Size(480, 696);
            this.ResumeLayout(false);

        }

        #endregion

        private CircularProgress.SpinningProgress.SpinningProgress spinningProgress1;
        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.MenuItem menuItem2;
    }
}