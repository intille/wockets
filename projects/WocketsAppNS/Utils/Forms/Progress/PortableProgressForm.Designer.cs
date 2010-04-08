using WocketsAppNS.Utils;
namespace WocketsAppNS.Utils.Forms.Progress
{
    partial class PortableProgressForm
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;

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

        private void InitializeInterface()
        {
            this.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
            this.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
            if ((this.Width > Constants.MAX_FORM_WIDTH) || (this.Height > Constants.MAX_FORM_HEIGHT))
            {
                this.Width = this.Width / 2;
                this.Height = this.Height / 2;
            }

            int widgetWidth = this.Width - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING;
            int widgetHeight = ((this.Height - Constants.WIDGET_SPACING - Constants.WIDGET_SPACING) / 5);

            System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(PortableProgressForm));
            this.progressLabel = new System.Windows.Forms.Label();
            this.marqueeTimer = new System.Windows.Forms.Timer();
            this.progressBar = new Bornander.UI.BornanderProgressBar.BornanderProgressBar();
            this.SuspendLayout();
            // 
            // progressLabel
            // 
            this.progressLabel.Location = new System.Drawing.Point(22, 18);
            this.progressLabel.Name = "progressLabel";
            this.progressLabel.Size = new System.Drawing.Size(54, 13);
            this.progressLabel.Text = "Loading...";
            // 
            // marqueeTimer
            // 
            this.marqueeTimer.Enabled = true;
            this.marqueeTimer.Interval = 20;
            this.marqueeTimer.Tick += new System.EventHandler(this.marqueeTimer_Tick);
            // 
            // progressBar
            // 

            this.progressBar.BackgroundDrawMethod = Bornander.UI.BornanderProgressBar.BornanderProgressBar.DrawMethod.Stretch;
            this.progressBar.BackgroundLeadingSize = 12;
            this.progressBar.BackgroundPicture = PortableProgressBar.vista_background;

            this.progressBar.BackgroundTrailingSize = 12;
            this.progressBar.ForegroundDrawMethod = Bornander.UI.BornanderProgressBar.BornanderProgressBar.DrawMethod.Stretch;
            this.progressBar.ForegroundLeadingSize = 12;
            this.progressBar.ForegroundPicture = PortableProgressBar.vista_foreground;
            this.progressBar.ForegroundTrailingSize = 12;
            this.progressBar.Location = new System.Drawing.Point(9, 45);
            this.progressBar.Marquee = Bornander.UI.BornanderProgressBar.BornanderProgressBar.MarqueeStyle.BlockWrap;
            this.progressBar.MarqueeWidth = 40;
            this.progressBar.Maximum = 100;
            this.progressBar.Minimum = 0;
            this.progressBar.Name = "progressBar";
            //this.progressBar.OverlayDrawMethod = Bornander.UI.BornanderProgressBar.BornanderProgressBar.DrawMethod.Stretch;
            //this.progressBar.OverlayLeadingSize = 12;
            //this.progressBar.OverlayPicture = PortableProgressBar.vista_overlay;

            this.progressBar.OverlayTrailingSize = 12;
            this.progressBar.Size = new System.Drawing.Size(widgetWidth, 21);
            this.progressBar.Type = Bornander.UI.BornanderProgressBar.BornanderProgressBar.BarType.Marquee;
            this.progressBar.Value = 0;
            // 
            // ProgressForm
            // 
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Inherit;
            this.ClientSize = new System.Drawing.Size(240, 268);
            this.Controls.Add(this.progressBar);
            this.Controls.Add(this.progressLabel);
            this.Name = "PortableProgressBarForm";
            this.Text = "Please Wait ...";
            this.ResumeLayout(false);


            this.progressBar.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING + (int)(this.Height / 5));

            this.progressLabel.Text = "Please wait ...";
            this.progressLabel.Size = new System.Drawing.Size(this.Width, (int)(this.Height / 6));
            this.progressLabel.Location = new System.Drawing.Point(Constants.WIDGET_SPACING, Constants.WIDGET_SPACING);
            this.progressLabel.Font = GUIHelper.CalculateBestFitFont(this.progressLabel.Parent.CreateGraphics(), Constants.MIN_FONT,
                   Constants.MAX_FONT, this.progressLabel.Size, this.progressLabel.Text, this.progressLabel.Font, (float)0.9, (float)0.9);

            this.progressText = new System.Windows.Forms.TextBox();
            this.progressText.Multiline = true;
            this.progressText.Location = new System.Drawing.Point(this.progressBar.Location.X, this.progressBar.Location.Y + this.progressBar.Height + Constants.WIDGET_SPACING);
            this.progressText.Size = new System.Drawing.Size(widgetWidth, ((int)widgetHeight * 3));
            this.progressText.Text = "Loading Wockets Software...\r\n";
            this.progressText.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);

            this.Controls.Add(this.progressText);

            this.Width = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Width;
            this.Height = System.Windows.Forms.Screen.PrimaryScreen.Bounds.Height;
            if ((this.Width > Constants.MAX_FORM_WIDTH) || (this.Height > Constants.MAX_FORM_HEIGHT))
            {
                this.Width = this.Width / 2;
                this.Height = this.Height / 2;
            }

        }

        public void AppendLog(string message)
        {
            this.progressText.Text += message;
            this.progressText.SelectionStart = this.progressText.Text.Length;
            this.progressText.ScrollToCaret();
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.progressLabel = new System.Windows.Forms.Label();
            this.marqueeTimer = new System.Windows.Forms.Timer();
            this.progressBar = new Bornander.UI.BornanderProgressBar.BornanderProgressBar();
            this.SuspendLayout();
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.TextBox progressText;
        private System.Windows.Forms.Label progressLabel;
        private Bornander.UI.BornanderProgressBar.BornanderProgressBar progressBar;
        private System.Windows.Forms.Timer marqueeTimer;

    }
}