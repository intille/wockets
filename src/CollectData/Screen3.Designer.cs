namespace CollectData
{
    partial class Screen3
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
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.panel1 = new System.Windows.Forms.Panel();
            this.button1 = new System.Windows.Forms.Button();
            this.button2 = new System.Windows.Forms.Button();
            this.label1 = new System.Windows.Forms.Label();
            this.timer1 = new System.Windows.Forms.Timer();
            this.button3 = new System.Windows.Forms.Button();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            this.mainMenu1.MenuItems.Add(this.menuItem2);
            // 
            // menuItem1
            // 
            this.menuItem1.Text = "Quit";
            this.menuItem1.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // menuItem2
            // 
            this.menuItem2.Text = "Next";
            this.menuItem2.Click += new System.EventHandler(this.menuItem2_Click);
            // 
            // panel1
            // 
            this.panel1.Location = new System.Drawing.Point(14, 143);
            this.panel1.Name = "panel1";
            this.panel1.Size = new System.Drawing.Size(211, 401);
            this.panel1.Paint += new System.Windows.Forms.PaintEventHandler(this.panel1_Paint);
            // 
            // button1
            // 
            this.button1.Font = new System.Drawing.Font("Tahoma", 24F, System.Drawing.FontStyle.Bold);
            this.button1.Location = new System.Drawing.Point(242, 143);
            this.button1.Name = "button1";
            this.button1.Size = new System.Drawing.Size(219, 129);
            this.button1.TabIndex = 1;
            this.button1.Text = "Wrist";
            this.button1.Enabled = false;
            this.button1.Click += new System.EventHandler(this.button1_Click);
            // 
            // button2
            // 
            this.button2.Font = new System.Drawing.Font("Tahoma", 24F, System.Drawing.FontStyle.Bold);
            this.button2.Location = new System.Drawing.Point(242, 415);
            this.button2.Name = "button2";
            this.button2.Size = new System.Drawing.Size(219, 129);
            this.button2.TabIndex = 2;
            this.button2.Text = "Ankle";
            this.button2.Enabled = false;
            this.button2.Click += new System.EventHandler(this.button2_Click);
            // 
            // label1
            // 
            this.label1.Font = new System.Drawing.Font("Tahoma", 18F, System.Drawing.FontStyle.Regular);
            this.label1.Location = new System.Drawing.Point(14, 0);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(447, 114);
            this.label1.Text = "Select the location of the sensors:";
            // 
            // timer1
            // 
            this.timer1.Tick += new System.EventHandler(this.timer1_Tick);
            // 
            // button3
            // 
            this.button3.Font = new System.Drawing.Font("Tahoma", 16F, System.Drawing.FontStyle.Bold);
            this.button3.Location = new System.Drawing.Point(73, 554);
            this.button3.Name = "button3";
            this.button3.Size = new System.Drawing.Size(388, 115);
            this.button3.TabIndex = 4;
            this.button3.Text = "Collect Data >>";
            this.button3.Click += new System.EventHandler(this.button3_Click);
            // 
            // Screen3
            // 
            this.Controls.Add(this.button3);
            this.Controls.Add(this.label1);
            this.Controls.Add(this.button2);
            this.Controls.Add(this.button1);
            this.Controls.Add(this.panel1);
            this.Location = new System.Drawing.Point(0, 52);
            this.Size = new System.Drawing.Size(480, 696);
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Panel panel1;
        private System.Windows.Forms.Button button1;
        private System.Windows.Forms.Button button2;
        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.MenuItem menuItem2;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Timer timer1;
        private System.Windows.Forms.Button button3;
    }
}