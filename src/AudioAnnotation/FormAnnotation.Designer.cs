namespace TestApplication_Annotation
{
    partial class FormAnnotation
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
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle61 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle62 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle70 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle71 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle72 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle63 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle64 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle65 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle66 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle67 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle68 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle69 = new System.Windows.Forms.DataGridViewCellStyle();
            this.button_1 = new System.Windows.Forms.Button();
            this.textBox_1 = new System.Windows.Forms.TextBox();
            this.label_date = new System.Windows.Forms.Label();
            this.dataGridView1 = new System.Windows.Forms.DataGridView();
            this.CID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CPostureLock = new System.Windows.Forms.DataGridViewCheckBoxColumn();
            this.CPosture = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartEnd = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CListActivity_2 = new System.Windows.Forms.DataGridViewCheckBoxColumn();
            this.CConcurrentActivity = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartEnd_Activity = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CTime = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CTimeLabel = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CNotes = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CStatus = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CEndID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Simple_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Label_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Simple_2 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Label_2 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.label_play = new System.Windows.Forms.Label();
            this.button_add_label = new System.Windows.Forms.Button();
            this.textBox_2 = new System.Windows.Forms.TextBox();
            this.button_remove_label = new System.Windows.Forms.Button();
            this.label_instructions_1 = new System.Windows.Forms.Label();
            this.label_instructions_2 = new System.Windows.Forms.Label();
            this.button_save = new System.Windows.Forms.Button();
            this.button_2 = new System.Windows.Forms.Button();
            this.button_generate = new System.Windows.Forms.Button();
            this.button_exit = new System.Windows.Forms.Button();
            this.textBox_instructions = new System.Windows.Forms.TextBox();
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).BeginInit();
            this.SuspendLayout();
            // 
            // button_1
            // 
            this.button_1.Location = new System.Drawing.Point(735, 6);
            this.button_1.Name = "button_1";
            this.button_1.Size = new System.Drawing.Size(101, 23);
            this.button_1.TabIndex = 0;
            this.button_1.Text = "Browse";
            this.button_1.UseVisualStyleBackColor = true;
            this.button_1.Click += new System.EventHandler(this.button_load_Click);
            // 
            // textBox_1
            // 
            this.textBox_1.Location = new System.Drawing.Point(171, 6);
            this.textBox_1.Name = "textBox_1";
            this.textBox_1.Size = new System.Drawing.Size(558, 20);
            this.textBox_1.TabIndex = 1;
            // 
            // label_date
            // 
            this.label_date.AutoSize = true;
            this.label_date.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_date.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_date.Location = new System.Drawing.Point(903, 11);
            this.label_date.Name = "label_date";
            this.label_date.Size = new System.Drawing.Size(90, 13);
            this.label_date.TabIndex = 5;
            this.label_date.Text = "Session Date: ";
            this.label_date.Visible = false;
            // 
            // dataGridView1
            // 
            this.dataGridView1.AccessibleRole = System.Windows.Forms.AccessibleRole.None;
            dataGridViewCellStyle61.NullValue = null;
            this.dataGridView1.AlternatingRowsDefaultCellStyle = dataGridViewCellStyle61;
            this.dataGridView1.AutoSizeColumnsMode = System.Windows.Forms.DataGridViewAutoSizeColumnsMode.ColumnHeader;
            this.dataGridView1.BackgroundColor = System.Drawing.Color.YellowGreen;
            this.dataGridView1.CellBorderStyle = System.Windows.Forms.DataGridViewCellBorderStyle.Sunken;
            dataGridViewCellStyle62.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle62.BackColor = System.Drawing.SystemColors.Control;
            dataGridViewCellStyle62.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle62.ForeColor = System.Drawing.SystemColors.WindowText;
            dataGridViewCellStyle62.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle62.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle62.WrapMode = System.Windows.Forms.DataGridViewTriState.True;
            this.dataGridView1.ColumnHeadersDefaultCellStyle = dataGridViewCellStyle62;
            this.dataGridView1.Columns.AddRange(new System.Windows.Forms.DataGridViewColumn[] {
            this.CID,
            this.CPostureLock,
            this.CPosture,
            this.CStartEnd,
            this.CListActivity_2,
            this.CConcurrentActivity,
            this.CStartEnd_Activity,
            this.CTime,
            this.CTimeLabel,
            this.CNotes,
            this.CStatus,
            this.CStartID,
            this.CEndID,
            this.CCombo_Simple_1,
            this.CCombo_Label_1,
            this.CCombo_Simple_2,
            this.CCombo_Label_2});
            dataGridViewCellStyle70.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleLeft;
            dataGridViewCellStyle70.BackColor = System.Drawing.SystemColors.Window;
            dataGridViewCellStyle70.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle70.ForeColor = System.Drawing.SystemColors.ControlText;
            dataGridViewCellStyle70.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle70.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle70.WrapMode = System.Windows.Forms.DataGridViewTriState.False;
            this.dataGridView1.DefaultCellStyle = dataGridViewCellStyle70;
            this.dataGridView1.GridColor = System.Drawing.Color.LightGray;
            this.dataGridView1.ImeMode = System.Windows.Forms.ImeMode.NoControl;
            this.dataGridView1.Location = new System.Drawing.Point(0, 148);
            this.dataGridView1.MultiSelect = false;
            this.dataGridView1.Name = "dataGridView1";
            this.dataGridView1.RowHeadersBorderStyle = System.Windows.Forms.DataGridViewHeaderBorderStyle.Single;
            dataGridViewCellStyle71.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleLeft;
            dataGridViewCellStyle71.BackColor = System.Drawing.SystemColors.Control;
            dataGridViewCellStyle71.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle71.ForeColor = System.Drawing.SystemColors.WindowText;
            dataGridViewCellStyle71.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle71.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle71.WrapMode = System.Windows.Forms.DataGridViewTriState.True;
            this.dataGridView1.RowHeadersDefaultCellStyle = dataGridViewCellStyle71;
            this.dataGridView1.RowHeadersWidthSizeMode = System.Windows.Forms.DataGridViewRowHeadersWidthSizeMode.AutoSizeToAllHeaders;
            dataGridViewCellStyle72.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.dataGridView1.RowsDefaultCellStyle = dataGridViewCellStyle72;
            this.dataGridView1.RowTemplate.DefaultCellStyle.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.dataGridView1.RowTemplate.Resizable = System.Windows.Forms.DataGridViewTriState.False;
            this.dataGridView1.SelectionMode = System.Windows.Forms.DataGridViewSelectionMode.FullRowSelect;
            this.dataGridView1.Size = new System.Drawing.Size(1036, 360);
            this.dataGridView1.StandardTab = true;
            this.dataGridView1.TabIndex = 0;
            this.dataGridView1.TabStop = false;
            this.dataGridView1.Visible = false;
            this.dataGridView1.CellValueChanged += new System.Windows.Forms.DataGridViewCellEventHandler(this.dataGridView1_CellValueChanged);
            this.dataGridView1.RowEnter += new System.Windows.Forms.DataGridViewCellEventHandler(this.dataGridView1_RowEnter);
            this.dataGridView1.DataError += new System.Windows.Forms.DataGridViewDataErrorEventHandler(this.dataGridView1_DataError);
            this.dataGridView1.KeyDown += new System.Windows.Forms.KeyEventHandler(this.dataGridView1_KeyDown);
            this.dataGridView1.CellEnter += new System.Windows.Forms.DataGridViewCellEventHandler(this.dataGridView1_CellEnter);
            this.dataGridView1.RowHeaderMouseClick += new System.Windows.Forms.DataGridViewCellMouseEventHandler(this.dataGridView1_RowHeaderMouseDoubleClick_1);
            // 
            // CID
            // 
            dataGridViewCellStyle63.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            dataGridViewCellStyle63.NullValue = null;
            dataGridViewCellStyle63.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            this.CID.DefaultCellStyle = dataGridViewCellStyle63;
            this.CID.FillWeight = 80F;
            this.CID.HeaderText = "Audio ID";
            this.CID.Name = "CID";
            this.CID.ReadOnly = true;
            this.CID.Width = 73;
            // 
            // CPostureLock
            // 
            dataGridViewCellStyle64.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle64.NullValue = "True";
            this.CPostureLock.DefaultCellStyle = dataGridViewCellStyle64;
            this.CPostureLock.FillWeight = 50F;
            this.CPostureLock.HeaderText = "Unlock";
            this.CPostureLock.Name = "CPostureLock";
            this.CPostureLock.Width = 47;
            // 
            // CPosture
            // 
            dataGridViewCellStyle65.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.CPosture.DefaultCellStyle = dataGridViewCellStyle65;
            this.CPosture.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.Nothing;
            this.CPosture.FillWeight = 200F;
            this.CPosture.HeaderText = "Main Activity";
            this.CPosture.MaxDropDownItems = 30;
            this.CPosture.Name = "CPosture";
            this.CPosture.Width = 73;
            // 
            // CStartEnd
            // 
            this.CStartEnd.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.Nothing;
            this.CStartEnd.HeaderText = "Start/End Tag";
            this.CStartEnd.Name = "CStartEnd";
            this.CStartEnd.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CStartEnd.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            // 
            // CListActivity_2
            // 
            this.CListActivity_2.FillWeight = 50F;
            this.CListActivity_2.HeaderText = "Unlock";
            this.CListActivity_2.Name = "CListActivity_2";
            this.CListActivity_2.Width = 47;
            // 
            // CConcurrentActivity
            // 
            this.CConcurrentActivity.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.Nothing;
            this.CConcurrentActivity.FillWeight = 200F;
            this.CConcurrentActivity.HeaderText = "Concurrent Activity";
            this.CConcurrentActivity.Name = "CConcurrentActivity";
            this.CConcurrentActivity.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CConcurrentActivity.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            this.CConcurrentActivity.Width = 121;
            // 
            // CStartEnd_Activity
            // 
            this.CStartEnd_Activity.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.Nothing;
            this.CStartEnd_Activity.HeaderText = "Start/End Tag";
            this.CStartEnd_Activity.Name = "CStartEnd_Activity";
            this.CStartEnd_Activity.Width = 81;
            // 
            // CTime
            // 
            dataGridViewCellStyle66.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle66.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            dataGridViewCellStyle66.Format = "T";
            dataGridViewCellStyle66.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            this.CTime.DefaultCellStyle = dataGridViewCellStyle66;
            this.CTime.HeaderText = "Creation Time";
            this.CTime.Name = "CTime";
            this.CTime.ReadOnly = true;
            this.CTime.Width = 97;
            // 
            // CTimeLabel
            // 
            this.CTimeLabel.HeaderText = "Label Time";
            this.CTimeLabel.Name = "CTimeLabel";
            this.CTimeLabel.Width = 84;
            // 
            // CNotes
            // 
            dataGridViewCellStyle67.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.CNotes.DefaultCellStyle = dataGridViewCellStyle67;
            this.CNotes.FillWeight = 150F;
            this.CNotes.HeaderText = "Notes";
            this.CNotes.Name = "CNotes";
            this.CNotes.Width = 60;
            // 
            // CStatus
            // 
            this.CStatus.HeaderText = "Status";
            this.CStatus.Name = "CStatus";
            this.CStatus.ReadOnly = true;
            this.CStatus.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CStatus.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            this.CStatus.Visible = false;
            this.CStatus.Width = 62;
            // 
            // CStartID
            // 
            dataGridViewCellStyle68.Format = "N0";
            dataGridViewCellStyle68.NullValue = null;
            this.CStartID.DefaultCellStyle = dataGridViewCellStyle68;
            this.CStartID.HeaderText = "StartID";
            this.CStartID.Name = "CStartID";
            this.CStartID.ReadOnly = true;
            this.CStartID.Visible = false;
            this.CStartID.Width = 65;
            // 
            // CEndID
            // 
            dataGridViewCellStyle69.Format = "N0";
            dataGridViewCellStyle69.NullValue = null;
            this.CEndID.DefaultCellStyle = dataGridViewCellStyle69;
            this.CEndID.HeaderText = "EndID";
            this.CEndID.Name = "CEndID";
            this.CEndID.ReadOnly = true;
            this.CEndID.Visible = false;
            this.CEndID.Width = 62;
            // 
            // CCombo_Simple_1
            // 
            this.CCombo_Simple_1.HeaderText = "Combo_Simple_1";
            this.CCombo_Simple_1.Name = "CCombo_Simple_1";
            this.CCombo_Simple_1.ReadOnly = true;
            this.CCombo_Simple_1.Visible = false;
            this.CCombo_Simple_1.Width = 114;
            // 
            // CCombo_Label_1
            // 
            this.CCombo_Label_1.HeaderText = "Combo_Label_1";
            this.CCombo_Label_1.Name = "CCombo_Label_1";
            this.CCombo_Label_1.ReadOnly = true;
            this.CCombo_Label_1.Visible = false;
            this.CCombo_Label_1.Width = 109;
            // 
            // CCombo_Simple_2
            // 
            this.CCombo_Simple_2.HeaderText = "Combo_Simple_2";
            this.CCombo_Simple_2.Name = "CCombo_Simple_2";
            this.CCombo_Simple_2.ReadOnly = true;
            this.CCombo_Simple_2.Visible = false;
            this.CCombo_Simple_2.Width = 114;
            // 
            // CCombo_Label_2
            // 
            this.CCombo_Label_2.HeaderText = "Combo_Label_2";
            this.CCombo_Label_2.Name = "CCombo_Label_2";
            this.CCombo_Label_2.ReadOnly = true;
            this.CCombo_Label_2.Visible = false;
            this.CCombo_Label_2.Width = 109;
            // 
            // label_play
            // 
            this.label_play.BackColor = System.Drawing.Color.White;
            this.label_play.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_play.ForeColor = System.Drawing.Color.DarkSeaGreen;
            this.label_play.Location = new System.Drawing.Point(171, 40);
            this.label_play.Name = "label_play";
            this.label_play.Size = new System.Drawing.Size(865, 23);
            this.label_play.TabIndex = 9;
            this.label_play.Text = "waiting for status ...";
            this.label_play.Visible = false;
            // 
            // button_add_label
            // 
            this.button_add_label.Location = new System.Drawing.Point(40, 99);
            this.button_add_label.Name = "button_add_label";
            this.button_add_label.Size = new System.Drawing.Size(101, 29);
            this.button_add_label.TabIndex = 11;
            this.button_add_label.Text = "Add Row";
            this.button_add_label.UseVisualStyleBackColor = true;
            this.button_add_label.Visible = false;
            this.button_add_label.Click += new System.EventHandler(this.button_add_label_Click);
            // 
            // textBox_2
            // 
            this.textBox_2.Location = new System.Drawing.Point(171, 43);
            this.textBox_2.Name = "textBox_2";
            this.textBox_2.Size = new System.Drawing.Size(558, 20);
            this.textBox_2.TabIndex = 13;
            // 
            // button_remove_label
            // 
            this.button_remove_label.Location = new System.Drawing.Point(466, 99);
            this.button_remove_label.Name = "button_remove_label";
            this.button_remove_label.Size = new System.Drawing.Size(101, 29);
            this.button_remove_label.TabIndex = 14;
            this.button_remove_label.Text = "Remove Row";
            this.button_remove_label.UseVisualStyleBackColor = true;
            this.button_remove_label.Visible = false;
            this.button_remove_label.Click += new System.EventHandler(this.button_remove_label_Click);
            // 
            // label_instructions_1
            // 
            this.label_instructions_1.AutoSize = true;
            this.label_instructions_1.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_instructions_1.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_instructions_1.Location = new System.Drawing.Point(37, 13);
            this.label_instructions_1.Name = "label_instructions_1";
            this.label_instructions_1.Size = new System.Drawing.Size(111, 15);
            this.label_instructions_1.TabIndex = 15;
            this.label_instructions_1.Text = "Audio Files Path";
            // 
            // label_instructions_2
            // 
            this.label_instructions_2.AutoSize = true;
            this.label_instructions_2.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_instructions_2.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_instructions_2.Location = new System.Drawing.Point(37, 44);
            this.label_instructions_2.Name = "label_instructions_2";
            this.label_instructions_2.Size = new System.Drawing.Size(100, 15);
            this.label_instructions_2.TabIndex = 16;
            this.label_instructions_2.Text = "Session Name";
            // 
            // button_save
            // 
            this.button_save.Location = new System.Drawing.Point(253, 99);
            this.button_save.Name = "button_save";
            this.button_save.Size = new System.Drawing.Size(101, 29);
            this.button_save.TabIndex = 17;
            this.button_save.Text = "Save Session";
            this.button_save.UseVisualStyleBackColor = true;
            this.button_save.Visible = false;
            this.button_save.Click += new System.EventHandler(this.button_save_Click);
            // 
            // button_2
            // 
            this.button_2.Location = new System.Drawing.Point(735, 40);
            this.button_2.Name = "button_2";
            this.button_2.Size = new System.Drawing.Size(101, 23);
            this.button_2.TabIndex = 18;
            this.button_2.Text = "Start";
            this.button_2.UseVisualStyleBackColor = true;
            this.button_2.Click += new System.EventHandler(this.button_2_Click);
            // 
            // button_generate
            // 
            this.button_generate.Location = new System.Drawing.Point(679, 99);
            this.button_generate.Name = "button_generate";
            this.button_generate.Size = new System.Drawing.Size(101, 29);
            this.button_generate.TabIndex = 19;
            this.button_generate.Text = "Generate Xml";
            this.button_generate.UseVisualStyleBackColor = true;
            this.button_generate.Visible = false;
            this.button_generate.Click += new System.EventHandler(this.button_generate_Click);
            // 
            // button_exit
            // 
            this.button_exit.Location = new System.Drawing.Point(892, 99);
            this.button_exit.Name = "button_exit";
            this.button_exit.Size = new System.Drawing.Size(101, 29);
            this.button_exit.TabIndex = 20;
            this.button_exit.Text = "Exit Session";
            this.button_exit.UseVisualStyleBackColor = true;
            this.button_exit.Visible = false;
            this.button_exit.Click += new System.EventHandler(this.button_exit_Click);
            // 
            // textBox_instructions
            // 
            this.textBox_instructions.BackColor = System.Drawing.Color.YellowGreen;
            this.textBox_instructions.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_instructions.ForeColor = System.Drawing.Color.White;
            this.textBox_instructions.Location = new System.Drawing.Point(35, 148);
            this.textBox_instructions.Multiline = true;
            this.textBox_instructions.Name = "textBox_instructions";
            this.textBox_instructions.Size = new System.Drawing.Size(1001, 35);
            this.textBox_instructions.TabIndex = 21;
            this.textBox_instructions.Text = " ";
            // 
            // FormAnnotation
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.DimGray;
            this.ClientSize = new System.Drawing.Size(1075, 529);
            this.Controls.Add(this.textBox_instructions);
            this.Controls.Add(this.button_exit);
            this.Controls.Add(this.button_generate);
            this.Controls.Add(this.button_2);
            this.Controls.Add(this.button_save);
            this.Controls.Add(this.label_instructions_2);
            this.Controls.Add(this.label_instructions_1);
            this.Controls.Add(this.button_remove_label);
            this.Controls.Add(this.button_add_label);
            this.Controls.Add(this.label_play);
            this.Controls.Add(this.dataGridView1);
            this.Controls.Add(this.label_date);
            this.Controls.Add(this.textBox_1);
            this.Controls.Add(this.button_1);
            this.Controls.Add(this.textBox_2);
            this.Name = "FormAnnotation";
            this.Text = "Wockets Annotation";
            this.Load += new System.EventHandler(this.FormAnnotation_Load);
            this.Resize += new System.EventHandler(this.FormAnnotation_Resize);
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).EndInit();
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Button button_1;
        private System.Windows.Forms.TextBox textBox_1;
        private System.Windows.Forms.Label label_date;
        private System.Windows.Forms.DataGridView dataGridView1;
        private System.Windows.Forms.Label label_play;
        private System.Windows.Forms.Button button_add_label;
        private System.Windows.Forms.TextBox textBox_2;
        private System.Windows.Forms.Button button_remove_label;
        private System.Windows.Forms.Label label_instructions_1;
        private System.Windows.Forms.Label label_instructions_2;
        private System.Windows.Forms.Button button_save;
        private System.Windows.Forms.Button button_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CID;
        private System.Windows.Forms.DataGridViewCheckBoxColumn CPostureLock;
        private System.Windows.Forms.DataGridViewComboBoxColumn CPosture;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStartEnd;
        private System.Windows.Forms.DataGridViewCheckBoxColumn CListActivity_2;
        private System.Windows.Forms.DataGridViewComboBoxColumn CConcurrentActivity;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStartEnd_Activity;
        private System.Windows.Forms.DataGridViewTextBoxColumn CTime;
        private System.Windows.Forms.DataGridViewTextBoxColumn CTimeLabel;
        private System.Windows.Forms.DataGridViewTextBoxColumn CNotes;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStatus;
        private System.Windows.Forms.DataGridViewTextBoxColumn CStartID;
        private System.Windows.Forms.DataGridViewTextBoxColumn CEndID;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Simple_1;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Label_1;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Simple_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Label_2;
        private System.Windows.Forms.Button button_generate;
        private System.Windows.Forms.Button button_exit;
        private System.Windows.Forms.TextBox textBox_instructions;
    }
}

