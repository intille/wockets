namespace KernelTest
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
            this.menukernel = new System.Windows.Forms.MenuItem();
            this.menukernelstart = new System.Windows.Forms.MenuItem();
            this.menukernelstop = new System.Windows.Forms.MenuItem();
            this.menuItem3 = new System.Windows.Forms.MenuItem();
            this.menuApp = new System.Windows.Forms.MenuItem();
            this.menuAppRegister = new System.Windows.Forms.MenuItem();
            this.menuAppUnregister = new System.Windows.Forms.MenuItem();
            this.menuWocket = new System.Windows.Forms.MenuItem();
            this.menuWocketDiscover = new System.Windows.Forms.MenuItem();
            this.menuWocketConnect = new System.Windows.Forms.MenuItem();
            this.menuWocketDisconnect = new System.Windows.Forms.MenuItem();
            this.menuItem2 = new System.Windows.Forms.MenuItem();
            this.label1 = new System.Windows.Forms.Label();
            this.status = new System.Windows.Forms.Label();
            this.listBox1 = new System.Windows.Forms.ListBox();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuItem1);
            this.mainMenu1.MenuItems.Add(this.menuItem2);
            // 
            // menuItem1
            // 
            this.menuItem1.MenuItems.Add(this.menukernel);
            this.menuItem1.MenuItems.Add(this.menuApp);
            this.menuItem1.MenuItems.Add(this.menuWocket);
            this.menuItem1.Text = "Commands";
            // 
            // menukernel
            // 
            this.menukernel.MenuItems.Add(this.menukernelstart);
            this.menukernel.MenuItems.Add(this.menukernelstop);
            this.menukernel.MenuItems.Add(this.menuItem3);
            this.menukernel.Text = "Kernel";
            // 
            // menukernelstart
            // 
            this.menukernelstart.Text = "Start";
            this.menukernelstart.Click += new System.EventHandler(this.menuItem8_Click);
            // 
            // menukernelstop
            // 
            this.menukernelstop.Enabled = false;
            this.menukernelstop.Text = "Stop";
            this.menukernelstop.Click += new System.EventHandler(this.menuItem9_Click);
            // 
            // menuItem3
            // 
            this.menuItem3.Text = "Ping";
            this.menuItem3.Click += new System.EventHandler(this.menuItem3_Click);
            // 
            // menuApp
            // 
            this.menuApp.Enabled = false;
            this.menuApp.MenuItems.Add(this.menuAppRegister);
            this.menuApp.MenuItems.Add(this.menuAppUnregister);
            this.menuApp.Text = "Application";
            // 
            // menuAppRegister
            // 
            this.menuAppRegister.Enabled = false;
            this.menuAppRegister.Text = "Register";
            this.menuAppRegister.Click += new System.EventHandler(this.menuItem11_Click);
            // 
            // menuAppUnregister
            // 
            this.menuAppUnregister.Enabled = false;
            this.menuAppUnregister.Text = "Unregister";
            this.menuAppUnregister.Click += new System.EventHandler(this.menuAppUnregister_Click);
            // 
            // menuWocket
            // 
            this.menuWocket.Enabled = false;
            this.menuWocket.MenuItems.Add(this.menuWocketDiscover);
            this.menuWocket.MenuItems.Add(this.menuWocketConnect);
            this.menuWocket.MenuItems.Add(this.menuWocketDisconnect);
            this.menuWocket.Text = "Wockets";
            // 
            // menuWocketDiscover
            // 
            this.menuWocketDiscover.Enabled = false;
            this.menuWocketDiscover.Text = "Discover";
            this.menuWocketDiscover.Click += new System.EventHandler(this.menuWocketDiscover_Click);
            // 
            // menuWocketConnect
            // 
            this.menuWocketConnect.Enabled = false;
            this.menuWocketConnect.Text = "Connect";
            this.menuWocketConnect.Click += new System.EventHandler(this.menuWocketConnect_Click);
            // 
            // menuWocketDisconnect
            // 
            this.menuWocketDisconnect.Enabled = false;
            this.menuWocketDisconnect.Text = "Disconnect";
            this.menuWocketDisconnect.Click += new System.EventHandler(this.menuWocketDisconnect_Click);
            // 
            // menuItem2
            // 
            this.menuItem2.Text = "Quit";
            this.menuItem2.Click += new System.EventHandler(this.menuItem2_Click);
            // 
            // label1
            // 
            this.label1.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Bold);
            this.label1.Location = new System.Drawing.Point(5, 10);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(127, 19);
            this.label1.Text = "Wockets List";
            // 
            // status
            // 
            this.status.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.status.Location = new System.Drawing.Point(15, 231);
            this.status.Name = "status";
            this.status.Size = new System.Drawing.Size(198, 72);
            this.status.Text = "Wockets - Version 2.0.0.0";
            // 
            // listBox1
            // 
            this.listBox1.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.listBox1.Location = new System.Drawing.Point(3, 33);
            this.listBox1.Name = "listBox1";
            this.listBox1.Size = new System.Drawing.Size(234, 173);
            this.listBox1.TabIndex = 4;
            this.listBox1.SelectedIndexChanged += new System.EventHandler(this.listBox1_SelectedIndexChanged);
            // 
            // Form1
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 320);
            this.Controls.Add(this.listBox1);
            this.Controls.Add(this.status);
            this.Controls.Add(this.label1);
            this.Menu = this.mainMenu1;
            this.Name = "Form1";
            this.Text = "Kernel Test";
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.MenuItem menuItem1;
        private System.Windows.Forms.MenuItem menuItem2;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Label status;
        private System.Windows.Forms.ListBox listBox1;
        private System.Windows.Forms.MenuItem menukernel;
        private System.Windows.Forms.MenuItem menukernelstart;
        private System.Windows.Forms.MenuItem menukernelstop;
        private System.Windows.Forms.MenuItem menuApp;
        private System.Windows.Forms.MenuItem menuAppRegister;
        private System.Windows.Forms.MenuItem menuAppUnregister;
        private System.Windows.Forms.MenuItem menuWocket;
        private System.Windows.Forms.MenuItem menuWocketDiscover;
        private System.Windows.Forms.MenuItem menuWocketConnect;
        private System.Windows.Forms.MenuItem menuWocketDisconnect;
        private System.Windows.Forms.MenuItem menuItem3;
    }
}

