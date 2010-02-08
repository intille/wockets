namespace AudioAnnotation
{
    partial class PopUp_Result_Window
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
            this.button_continue = new System.Windows.Forms.Button();
            this.DataGridView_Summary = new System.Windows.Forms.DataGridView();
            this.LabelColumn = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.TimeColumn = new System.Windows.Forms.DataGridViewTextBoxColumn();
            ((System.ComponentModel.ISupportInitialize)(this.DataGridView_Summary)).BeginInit();
            this.SuspendLayout();
            // 
            // button_continue
            // 
            this.button_continue.Location = new System.Drawing.Point(489, 489);
            this.button_continue.Name = "button_continue";
            this.button_continue.Size = new System.Drawing.Size(75, 23);
            this.button_continue.TabIndex = 0;
            this.button_continue.Text = "Close";
            this.button_continue.UseVisualStyleBackColor = true;
            this.button_continue.Click += new System.EventHandler(this.button_continue_Click);
            // 
            // DataGridView_Summary
            // 
            this.DataGridView_Summary.AllowUserToAddRows = false;
            this.DataGridView_Summary.AllowUserToDeleteRows = false;
            this.DataGridView_Summary.BackgroundColor = System.Drawing.Color.White;
            this.DataGridView_Summary.ColumnHeadersHeightSizeMode = System.Windows.Forms.DataGridViewColumnHeadersHeightSizeMode.AutoSize;
            this.DataGridView_Summary.Columns.AddRange(new System.Windows.Forms.DataGridViewColumn[] {
            this.LabelColumn,
            this.TimeColumn});
            this.DataGridView_Summary.GridColor = System.Drawing.Color.DarkSeaGreen;
            this.DataGridView_Summary.Location = new System.Drawing.Point(13, 12);
            this.DataGridView_Summary.Name = "DataGridView_Summary";
            this.DataGridView_Summary.ReadOnly = true;
            this.DataGridView_Summary.RowHeadersVisible = false;
            this.DataGridView_Summary.ScrollBars = System.Windows.Forms.ScrollBars.Vertical;
            this.DataGridView_Summary.SelectionMode = System.Windows.Forms.DataGridViewSelectionMode.FullRowSelect;
            this.DataGridView_Summary.ShowEditingIcon = false;
            this.DataGridView_Summary.Size = new System.Drawing.Size(550, 471);
            this.DataGridView_Summary.TabIndex = 2;
            // 
            // LabelColumn
            // 
            this.LabelColumn.AutoSizeMode = System.Windows.Forms.DataGridViewAutoSizeColumnMode.None;
            this.LabelColumn.HeaderText = "Label";
            this.LabelColumn.Name = "LabelColumn";
            this.LabelColumn.ReadOnly = true;
            this.LabelColumn.Width = 400;
            // 
            // TimeColumn
            // 
            this.TimeColumn.AutoSizeMode = System.Windows.Forms.DataGridViewAutoSizeColumnMode.None;
            this.TimeColumn.HeaderText = "Time(hh:mm:ss)";
            this.TimeColumn.Name = "TimeColumn";
            this.TimeColumn.ReadOnly = true;
            this.TimeColumn.Width = 150;
            // 
            // PopUp_Result_Window
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.DarkSeaGreen;
            this.ClientSize = new System.Drawing.Size(576, 524);
            this.Controls.Add(this.DataGridView_Summary);
            this.Controls.Add(this.button_continue);
            this.Name = "PopUp_Result_Window";
            this.Text = "Summary of Results";
            this.FormClosed += new System.Windows.Forms.FormClosedEventHandler(this.PopUp_Result_Window_FormClosed);
            ((System.ComponentModel.ISupportInitialize)(this.DataGridView_Summary)).EndInit();
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Button button_continue;
        private System.Windows.Forms.DataGridView DataGridView_Summary;
        private System.Windows.Forms.DataGridViewTextBoxColumn LabelColumn;
        private System.Windows.Forms.DataGridViewTextBoxColumn TimeColumn;
    }
}