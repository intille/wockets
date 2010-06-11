namespace WocketConfigurationApp
{
    partial class Form1
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

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.button_search = new System.Windows.Forms.Button();
            this.listBox1 = new System.Windows.Forms.ListBox();
            this.textBox1 = new System.Windows.Forms.TextBox();
            this.button_configure = new System.Windows.Forms.Button();
            this.button_select_wocket = new System.Windows.Forms.Button();
            this.button_unselect_wocket = new System.Windows.Forms.Button();
            this.label_status = new System.Windows.Forms.Label();
            this.SuspendLayout();
            // 
            // button_search
            // 
            this.button_search.BackColor = System.Drawing.Color.DimGray;
            this.button_search.FlatStyle = System.Windows.Forms.FlatStyle.System;
            this.button_search.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_search.ForeColor = System.Drawing.SystemColors.ControlLightLight;
            this.button_search.Location = new System.Drawing.Point(56, 91);
            this.button_search.Name = "button_search";
            this.button_search.Size = new System.Drawing.Size(168, 99);
            this.button_search.TabIndex = 0;
            this.button_search.Text = "Search";
            this.button_search.UseVisualStyleBackColor = false;
            this.button_search.Click += new System.EventHandler(this.button_search_Click);
            // 
            // listBox1
            // 
            this.listBox1.BackColor = System.Drawing.Color.YellowGreen;
            this.listBox1.Font = new System.Drawing.Font("Microsoft Sans Serif", 12F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.listBox1.ForeColor = System.Drawing.Color.White;
            this.listBox1.FormattingEnabled = true;
            this.listBox1.HorizontalScrollbar = true;
            this.listBox1.ItemHeight = 20;
            this.listBox1.Location = new System.Drawing.Point(339, 16);
            this.listBox1.MultiColumn = true;
            this.listBox1.Name = "listBox1";
            this.listBox1.Size = new System.Drawing.Size(410, 224);
            this.listBox1.TabIndex = 1;
            this.listBox1.SelectedIndexChanged += new System.EventHandler(this.listBox1_SelectedIndexChanged);
            // 
            // textBox1
            // 
            this.textBox1.BackColor = System.Drawing.Color.DimGray;
            this.textBox1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox1.Font = new System.Drawing.Font("Microsoft Sans Serif", 14.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox1.ForeColor = System.Drawing.Color.Orange;
            this.textBox1.Location = new System.Drawing.Point(24, 3);
            this.textBox1.Multiline = true;
            this.textBox1.Name = "textBox1";
            this.textBox1.ReadOnly = true;
            this.textBox1.Size = new System.Drawing.Size(280, 60);
            this.textBox1.TabIndex = 2;
            this.textBox1.Text = "Select a wocket to configure or click search to discover devices.";
            // 
            // button_configure
            // 
            this.button_configure.Enabled = false;
            this.button_configure.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_configure.Location = new System.Drawing.Point(581, 246);
            this.button_configure.Name = "button_configure";
            this.button_configure.Size = new System.Drawing.Size(168, 52);
            this.button_configure.TabIndex = 3;
            this.button_configure.Text = "Configure";
            this.button_configure.UseVisualStyleBackColor = true;
            this.button_configure.Click += new System.EventHandler(this.button2_Click);
            // 
            // button_select_wocket
            // 
            this.button_select_wocket.BackgroundImage = global::WocketConfigurationApp.Resources.add_32;
            this.button_select_wocket.BackgroundImageLayout = System.Windows.Forms.ImageLayout.Center;
            this.button_select_wocket.Cursor = System.Windows.Forms.Cursors.Arrow;
            this.button_select_wocket.Location = new System.Drawing.Point(755, 17);
            this.button_select_wocket.Name = "button_select_wocket";
            this.button_select_wocket.Size = new System.Drawing.Size(42, 42);
            this.button_select_wocket.TabIndex = 4;
            this.button_select_wocket.UseVisualStyleBackColor = true;
            this.button_select_wocket.Click += new System.EventHandler(this.button_select_wocket_Click);
            // 
            // button_unselect_wocket
            // 
            this.button_unselect_wocket.BackgroundImage = global::WocketConfigurationApp.Resources.delete32;
            this.button_unselect_wocket.BackgroundImageLayout = System.Windows.Forms.ImageLayout.Center;
            this.button_unselect_wocket.Location = new System.Drawing.Point(755, 78);
            this.button_unselect_wocket.Name = "button_unselect_wocket";
            this.button_unselect_wocket.Size = new System.Drawing.Size(42, 42);
            this.button_unselect_wocket.TabIndex = 5;
            this.button_unselect_wocket.UseVisualStyleBackColor = true;
            this.button_unselect_wocket.Click += new System.EventHandler(this.button_unselect_wocket_Click);
            // 
            // label_status
            // 
            this.label_status.AutoSize = true;
            this.label_status.Font = new System.Drawing.Font("Microsoft Sans Serif", 14.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_status.ForeColor = System.Drawing.Color.White;
            this.label_status.Location = new System.Drawing.Point(149, 262);
            this.label_status.Name = "label_status";
            this.label_status.Size = new System.Drawing.Size(182, 24);
            this.label_status.TabIndex = 8;
            this.label_status.Text = "Waiting for wocket ...";
            // 
            // Form1
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.DimGray;
            this.ClientSize = new System.Drawing.Size(831, 306);
            this.Controls.Add(this.label_status);
            this.Controls.Add(this.button_unselect_wocket);
            this.Controls.Add(this.button_select_wocket);
            this.Controls.Add(this.button_configure);
            this.Controls.Add(this.textBox1);
            this.Controls.Add(this.listBox1);
            this.Controls.Add(this.button_search);
            this.Name = "Form1";
            this.Text = "Wocket Configuration App";
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Button button_search;
        private System.Windows.Forms.ListBox listBox1;
        private System.Windows.Forms.TextBox textBox1;
        private System.Windows.Forms.Button button_configure;
        private System.Windows.Forms.Button button_select_wocket;
        private System.Windows.Forms.Button button_unselect_wocket;

        private System.Windows.Forms.Label label_status;
    }
}

