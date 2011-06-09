namespace CollectData
{
    partial class Screen
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
            this.screen51 = new CollectData.Screen5();
            this.screen61 = new CollectData.Screen6();
            this.screen11 = new CollectData.Screen1();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            // 
            // menuItem1
            // 
            this.menuItem1.Enabled = false;
            this.menuItem1.Text = "Quit";
            this.menuItem1.Click += new System.EventHandler(this.menuItem1_Click);
            // 
            // screen51
            // 
            this.screen51.Enabled = false;
            this.screen51.Location = new System.Drawing.Point(0, 0);
            this.screen51.Name = "screen51";
            this.screen51.Size = new System.Drawing.Size(475, 692);
            this.screen51.Visible = false;
            // 
            // screen61
            // 
            this.screen61.Enabled = false;
            this.screen61.Location = new System.Drawing.Point(481, 0);
            this.screen61.Name = "screen61";
            this.screen61.Size = new System.Drawing.Size(477, 692);
            this.screen61.Visible = false;
            // 
            // screen11
            // 
            this.screen11.Location = new System.Drawing.Point(3, 3);
            this.screen11.Name = "screen11";
            this.screen11.Size = new System.Drawing.Size(469, 686);
            // 
            // Screen
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(192F, 192F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.ClientSize = new System.Drawing.Size(480, 696);
            this.Controls.Add(this.screen51);
            this.Controls.Add(this.screen61);
            this.Controls.Add(this.screen11);
            this.Location = new System.Drawing.Point(0, 52);
            this.Menu = this.mainMenu1;
            this.Name = "Screen";
            this.Text = "Wockets";
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.MenuItem menuItem1;
        private Screen5 screen51;
        private Screen6 screen61;
        private Screen1 screen11;


    }
}