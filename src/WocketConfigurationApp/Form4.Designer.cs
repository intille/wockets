namespace WocketConfigurationApp
{
    partial class Form4
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
            this.button_configure = new System.Windows.Forms.Button();
            this.button_select_wocket = new System.Windows.Forms.Button();
            this.button_unselect_wocket = new System.Windows.Forms.Button();
            this.label_status = new System.Windows.Forms.Label();
            this.dataGridView1 = new System.Windows.Forms.DataGridView();
            this.Wockets_Column_Name = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.Wockets_Column_Mac = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.Wockets_Column_Status = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.Wockets_Column_Test = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.panel1 = new System.Windows.Forms.Panel();
            this.button_quit = new System.Windows.Forms.Button();
            this.label3 = new System.Windows.Forms.Label();
            this.button_settings = new System.Windows.Forms.Button();
            this.panel2 = new System.Windows.Forms.Panel();
            this.label2 = new System.Windows.Forms.Label();
            this.label1 = new System.Windows.Forms.Label();
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).BeginInit();
            this.panel1.SuspendLayout();
            this.panel2.SuspendLayout();
            this.SuspendLayout();
            // 
            // button_search
            // 
            this.button_search.BackColor = System.Drawing.Color.Orange;
            this.button_search.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_search.ForeColor = System.Drawing.SystemColors.ControlLightLight;
            this.button_search.Location = new System.Drawing.Point(16, 29);
            this.button_search.Name = "button_search";
            this.button_search.Size = new System.Drawing.Size(210, 89);
            this.button_search.TabIndex = 0;
            this.button_search.Text = "Search";
            this.button_search.UseVisualStyleBackColor = false;
            this.button_search.Click += new System.EventHandler(this.button_search_Click);
            // 
            // button_configure
            // 
            this.button_configure.Enabled = false;
            this.button_configure.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_configure.Location = new System.Drawing.Point(504, 445);
            this.button_configure.Name = "button_configure";
            this.button_configure.Size = new System.Drawing.Size(168, 52);
            this.button_configure.TabIndex = 3;
            this.button_configure.Text = "Start Test";
            this.button_configure.UseVisualStyleBackColor = true;
            this.button_configure.Click += new System.EventHandler(this.button2_Click);
            // 
            // button_select_wocket
            // 
            this.button_select_wocket.BackgroundImage = global::WocketConfigurationApp.Resources.add_32;
            this.button_select_wocket.BackgroundImageLayout = System.Windows.Forms.ImageLayout.Center;
            this.button_select_wocket.Cursor = System.Windows.Forms.Cursors.Arrow;
            this.button_select_wocket.Location = new System.Drawing.Point(70, 138);
            this.button_select_wocket.Name = "button_select_wocket";
            this.button_select_wocket.Size = new System.Drawing.Size(103, 50);
            this.button_select_wocket.TabIndex = 4;
            this.button_select_wocket.UseVisualStyleBackColor = true;
            this.button_select_wocket.Click += new System.EventHandler(this.button_add_wocket_Click);
            // 
            // button_unselect_wocket
            // 
            this.button_unselect_wocket.BackgroundImage = global::WocketConfigurationApp.Resources.delete32;
            this.button_unselect_wocket.BackgroundImageLayout = System.Windows.Forms.ImageLayout.Center;
            this.button_unselect_wocket.Location = new System.Drawing.Point(70, 230);
            this.button_unselect_wocket.Name = "button_unselect_wocket";
            this.button_unselect_wocket.Size = new System.Drawing.Size(103, 50);
            this.button_unselect_wocket.TabIndex = 5;
            this.button_unselect_wocket.UseVisualStyleBackColor = true;
            this.button_unselect_wocket.Click += new System.EventHandler(this.button_remove_wocket_Click);
            // 
            // label_status
            // 
            this.label_status.AutoSize = true;
            this.label_status.BackColor = System.Drawing.Color.SlateGray;
            this.label_status.Font = new System.Drawing.Font("Microsoft Sans Serif", 9.75F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_status.ForeColor = System.Drawing.Color.White;
            this.label_status.Location = new System.Drawing.Point(13, 341);
            this.label_status.Name = "label_status";
            this.label_status.Size = new System.Drawing.Size(150, 16);
            this.label_status.TabIndex = 8;
            this.label_status.Text = "Waiting for wocket ...";
            // 
            // dataGridView1
            // 
            this.dataGridView1.AllowUserToAddRows = false;
            this.dataGridView1.AllowUserToDeleteRows = false;
            this.dataGridView1.AllowUserToResizeRows = false;
            this.dataGridView1.ColumnHeadersHeightSizeMode = System.Windows.Forms.DataGridViewColumnHeadersHeightSizeMode.AutoSize;
            this.dataGridView1.Columns.AddRange(new System.Windows.Forms.DataGridViewColumn[] {
            this.Wockets_Column_Name,
            this.Wockets_Column_Mac,
            this.Wockets_Column_Status,
            this.Wockets_Column_Test});
            this.dataGridView1.Location = new System.Drawing.Point(282, 57);
            this.dataGridView1.MultiSelect = false;
            this.dataGridView1.Name = "dataGridView1";
            this.dataGridView1.ReadOnly = true;
            this.dataGridView1.RowHeadersVisible = false;
            this.dataGridView1.RowHeadersWidthSizeMode = System.Windows.Forms.DataGridViewRowHeadersWidthSizeMode.AutoSizeToAllHeaders;
            this.dataGridView1.ScrollBars = System.Windows.Forms.ScrollBars.Vertical;
            this.dataGridView1.SelectionMode = System.Windows.Forms.DataGridViewSelectionMode.FullRowSelect;
            this.dataGridView1.Size = new System.Drawing.Size(593, 373);
            this.dataGridView1.TabIndex = 9;
            // 
            // Wockets_Column_Name
            // 
            this.Wockets_Column_Name.HeaderText = "Name";
            this.Wockets_Column_Name.Name = "Wockets_Column_Name";
            this.Wockets_Column_Name.ReadOnly = true;
            this.Wockets_Column_Name.Width = 200;
            // 
            // Wockets_Column_Mac
            // 
            this.Wockets_Column_Mac.HeaderText = "Mac";
            this.Wockets_Column_Mac.Name = "Wockets_Column_Mac";
            this.Wockets_Column_Mac.ReadOnly = true;
            this.Wockets_Column_Mac.Width = 200;
            // 
            // Wockets_Column_Status
            // 
            this.Wockets_Column_Status.HeaderText = "Status";
            this.Wockets_Column_Status.Name = "Wockets_Column_Status";
            this.Wockets_Column_Status.ReadOnly = true;
            // 
            // Wockets_Column_Test
            // 
            this.Wockets_Column_Test.HeaderText = "Test";
            this.Wockets_Column_Test.Name = "Wockets_Column_Test";
            this.Wockets_Column_Test.ReadOnly = true;
            // 
            // panel1
            // 
            this.panel1.Controls.Add(this.button_quit);
            this.panel1.Controls.Add(this.label3);
            this.panel1.Controls.Add(this.button_settings);
            this.panel1.Controls.Add(this.button_configure);
            this.panel1.Controls.Add(this.dataGridView1);
            this.panel1.Controls.Add(this.panel2);
            this.panel1.Location = new System.Drawing.Point(12, 5);
            this.panel1.Name = "panel1";
            this.panel1.Size = new System.Drawing.Size(889, 519);
            this.panel1.TabIndex = 10;
            // 
            // button_quit
            // 
            this.button_quit.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_quit.Location = new System.Drawing.Point(698, 445);
            this.button_quit.Name = "button_quit";
            this.button_quit.Size = new System.Drawing.Size(168, 52);
            this.button_quit.TabIndex = 13;
            this.button_quit.Text = "Quit";
            this.button_quit.UseVisualStyleBackColor = true;
            this.button_quit.Click += new System.EventHandler(this.button_quit_Click);
            // 
            // label3
            // 
            this.label3.AutoSize = true;
            this.label3.Font = new System.Drawing.Font("Microsoft Sans Serif", 9.75F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label3.ForeColor = System.Drawing.Color.Orange;
            this.label3.Location = new System.Drawing.Point(26, 26);
            this.label3.Name = "label3";
            this.label3.Size = new System.Drawing.Size(381, 16);
            this.label3.TabIndex = 12;
            this.label3.Text = "Select \"Add Wocket\" or click \"Search\" to find wockets.";
            // 
            // button_settings
            // 
            this.button_settings.Enabled = false;
            this.button_settings.Font = new System.Drawing.Font("Microsoft Sans Serif", 18F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.button_settings.Location = new System.Drawing.Point(292, 445);
            this.button_settings.Name = "button_settings";
            this.button_settings.Size = new System.Drawing.Size(168, 52);
            this.button_settings.TabIndex = 11;
            this.button_settings.Text = "Settings";
            this.button_settings.UseVisualStyleBackColor = true;
            this.button_settings.Click += new System.EventHandler(this.button_settings_Click);
            // 
            // panel2
            // 
            this.panel2.BackColor = System.Drawing.Color.SlateGray;
            this.panel2.Controls.Add(this.label2);
            this.panel2.Controls.Add(this.label1);
            this.panel2.Controls.Add(this.button_search);
            this.panel2.Controls.Add(this.button_select_wocket);
            this.panel2.Controls.Add(this.label_status);
            this.panel2.Controls.Add(this.button_unselect_wocket);
            this.panel2.Location = new System.Drawing.Point(24, 57);
            this.panel2.Name = "panel2";
            this.panel2.Size = new System.Drawing.Size(248, 373);
            this.panel2.TabIndex = 10;
            // 
            // label2
            // 
            this.label2.AutoSize = true;
            this.label2.ForeColor = System.Drawing.Color.White;
            this.label2.Location = new System.Drawing.Point(75, 283);
            this.label2.Name = "label2";
            this.label2.Size = new System.Drawing.Size(88, 13);
            this.label2.TabIndex = 10;
            this.label2.Text = "Remove Wocket";
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.ForeColor = System.Drawing.Color.White;
            this.label1.Location = new System.Drawing.Point(87, 191);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(67, 13);
            this.label1.TabIndex = 9;
            this.label1.Text = "Add Wocket";
            // 
            // Form4
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.DimGray;
            this.ClientSize = new System.Drawing.Size(913, 526);
            this.Controls.Add(this.panel1);
            this.Name = "Form4";
            this.Text = "Wocket Configuration App";
            this.FormClosing += new System.Windows.Forms.FormClosingEventHandler(this.Form4_FormClosing);
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).EndInit();
            this.panel1.ResumeLayout(false);
            this.panel1.PerformLayout();
            this.panel2.ResumeLayout(false);
            this.panel2.PerformLayout();
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Button button_search;
        private System.Windows.Forms.Button button_configure;
        private System.Windows.Forms.Button button_select_wocket;
        private System.Windows.Forms.Button button_unselect_wocket;

        private System.Windows.Forms.Label label_status;
        private System.Windows.Forms.DataGridView dataGridView1;
        private System.Windows.Forms.Panel panel1;
        private System.Windows.Forms.Panel panel2;
        private System.Windows.Forms.DataGridViewTextBoxColumn Wockets_Column_Name;
        private System.Windows.Forms.DataGridViewTextBoxColumn Wockets_Column_Mac;
        private System.Windows.Forms.DataGridViewTextBoxColumn Wockets_Column_Status;
        private System.Windows.Forms.DataGridViewTextBoxColumn Wockets_Column_Test;
        private System.Windows.Forms.Label label2;
        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Button button_settings;
        private System.Windows.Forms.Label label3;
        private System.Windows.Forms.Button button_quit;
    }
}

