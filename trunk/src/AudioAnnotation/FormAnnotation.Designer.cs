namespace AudioAnnotation
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
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle25 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle26 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle34 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle35 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle36 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle27 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle28 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle29 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle30 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle31 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle32 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle33 = new System.Windows.Forms.DataGridViewCellStyle();
            this.button_1 = new System.Windows.Forms.Button();
            this.textBox_1 = new System.Windows.Forms.TextBox();
            this.label_date = new System.Windows.Forms.Label();
            this.dataGridView1 = new System.Windows.Forms.DataGridView();
            this.CID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CPostureLock = new System.Windows.Forms.DataGridViewCheckBoxColumn();
            this.CPosture = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartEnd = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CTime = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CTimeLabel = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CNotes = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CStatus = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CEndID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Type = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Label_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
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
            this.button_session_part = new System.Windows.Forms.Button();
            this.label_files_path = new System.Windows.Forms.Label();
            this.label_protocol_path = new System.Windows.Forms.Label();
            this.button_3 = new System.Windows.Forms.Button();
            this.folderBrowserDialog = new System.Windows.Forms.FolderBrowserDialog();
            this.openFileDialog = new System.Windows.Forms.OpenFileDialog();
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).BeginInit();
            this.SuspendLayout();
            // 
            // button_1
            // 
            this.button_1.Location = new System.Drawing.Point(935, 120);
            this.button_1.Name = "button_1";
            this.button_1.Size = new System.Drawing.Size(101, 23);
            this.button_1.TabIndex = 0;
            this.button_1.Text = "Browse";
            this.button_1.UseVisualStyleBackColor = true;
            this.button_1.Click += new System.EventHandler(this.button_load_Click);
            // 
            // textBox_1
            // 
            this.textBox_1.Location = new System.Drawing.Point(157, 122);
            this.textBox_1.Name = "textBox_1";
            this.textBox_1.Size = new System.Drawing.Size(758, 20);
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
            dataGridViewCellStyle25.NullValue = null;
            this.dataGridView1.AlternatingRowsDefaultCellStyle = dataGridViewCellStyle25;
            this.dataGridView1.AutoSizeColumnsMode = System.Windows.Forms.DataGridViewAutoSizeColumnsMode.ColumnHeader;
            this.dataGridView1.BackgroundColor = System.Drawing.Color.YellowGreen;
            this.dataGridView1.CellBorderStyle = System.Windows.Forms.DataGridViewCellBorderStyle.Sunken;
            dataGridViewCellStyle26.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle26.BackColor = System.Drawing.SystemColors.Control;
            dataGridViewCellStyle26.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle26.ForeColor = System.Drawing.SystemColors.WindowText;
            dataGridViewCellStyle26.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle26.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle26.WrapMode = System.Windows.Forms.DataGridViewTriState.True;
            this.dataGridView1.ColumnHeadersDefaultCellStyle = dataGridViewCellStyle26;
            this.dataGridView1.Columns.AddRange(new System.Windows.Forms.DataGridViewColumn[] {
            this.CID,
            this.CPostureLock,
            this.CPosture,
            this.CStartEnd,
            this.CTime,
            this.CTimeLabel,
            this.CNotes,
            this.CStatus,
            this.CStartID,
            this.CEndID,
            this.CCombo_Type,
            this.CCombo_Label_1});
            dataGridViewCellStyle34.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleLeft;
            dataGridViewCellStyle34.BackColor = System.Drawing.SystemColors.Window;
            dataGridViewCellStyle34.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle34.ForeColor = System.Drawing.SystemColors.ControlText;
            dataGridViewCellStyle34.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle34.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle34.WrapMode = System.Windows.Forms.DataGridViewTriState.False;
            this.dataGridView1.DefaultCellStyle = dataGridViewCellStyle34;
            this.dataGridView1.GridColor = System.Drawing.Color.LightGray;
            this.dataGridView1.ImeMode = System.Windows.Forms.ImeMode.NoControl;
            this.dataGridView1.Location = new System.Drawing.Point(3, 148);
            this.dataGridView1.MultiSelect = false;
            this.dataGridView1.Name = "dataGridView1";
            this.dataGridView1.RowHeadersBorderStyle = System.Windows.Forms.DataGridViewHeaderBorderStyle.Single;
            dataGridViewCellStyle35.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleLeft;
            dataGridViewCellStyle35.BackColor = System.Drawing.SystemColors.Control;
            dataGridViewCellStyle35.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle35.ForeColor = System.Drawing.SystemColors.WindowText;
            dataGridViewCellStyle35.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle35.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle35.WrapMode = System.Windows.Forms.DataGridViewTriState.True;
            this.dataGridView1.RowHeadersDefaultCellStyle = dataGridViewCellStyle35;
            this.dataGridView1.RowHeadersWidthSizeMode = System.Windows.Forms.DataGridViewRowHeadersWidthSizeMode.AutoSizeToAllHeaders;
            dataGridViewCellStyle36.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.dataGridView1.RowsDefaultCellStyle = dataGridViewCellStyle36;
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
            dataGridViewCellStyle27.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            dataGridViewCellStyle27.NullValue = null;
            dataGridViewCellStyle27.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            this.CID.DefaultCellStyle = dataGridViewCellStyle27;
            this.CID.FillWeight = 80F;
            this.CID.HeaderText = "Audio ID";
            this.CID.Name = "CID";
            this.CID.ReadOnly = true;
            this.CID.Width = 73;
            // 
            // CPostureLock
            // 
            dataGridViewCellStyle28.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle28.NullValue = "False";
            this.CPostureLock.DefaultCellStyle = dataGridViewCellStyle28;
            this.CPostureLock.FillWeight = 50F;
            this.CPostureLock.HeaderText = "Auto Stop";
            this.CPostureLock.Name = "CPostureLock";
            this.CPostureLock.Visible = false;
            this.CPostureLock.Width = 60;
            // 
            // CPosture
            // 
            dataGridViewCellStyle29.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.CPosture.DefaultCellStyle = dataGridViewCellStyle29;
            this.CPosture.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.ComboBox;
            this.CPosture.DisplayStyleForCurrentCellOnly = true;
            this.CPosture.FillWeight = 200F;
            this.CPosture.HeaderText = "Category";
            this.CPosture.MaxDropDownItems = 30;
            this.CPosture.Name = "CPosture";
            this.CPosture.Width = 55;
            // 
            // CStartEnd
            // 
            this.CStartEnd.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.ComboBox;
            this.CStartEnd.DisplayStyleForCurrentCellOnly = true;
            this.CStartEnd.HeaderText = "Start/End Tag";
            this.CStartEnd.Name = "CStartEnd";
            this.CStartEnd.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CStartEnd.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            // 
            // CTime
            // 
            dataGridViewCellStyle30.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle30.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            dataGridViewCellStyle30.Format = "T";
            dataGridViewCellStyle30.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            this.CTime.DefaultCellStyle = dataGridViewCellStyle30;
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
            dataGridViewCellStyle31.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.CNotes.DefaultCellStyle = dataGridViewCellStyle31;
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
            dataGridViewCellStyle32.Format = "N0";
            dataGridViewCellStyle32.NullValue = null;
            this.CStartID.DefaultCellStyle = dataGridViewCellStyle32;
            this.CStartID.HeaderText = "StartID";
            this.CStartID.Name = "CStartID";
            this.CStartID.ReadOnly = true;
            this.CStartID.Visible = false;
            this.CStartID.Width = 65;
            // 
            // CEndID
            // 
            dataGridViewCellStyle33.Format = "N0";
            dataGridViewCellStyle33.NullValue = null;
            this.CEndID.DefaultCellStyle = dataGridViewCellStyle33;
            this.CEndID.HeaderText = "EndID";
            this.CEndID.Name = "CEndID";
            this.CEndID.ReadOnly = true;
            this.CEndID.Visible = false;
            this.CEndID.Width = 62;
            // 
            // CCombo_Type
            // 
            this.CCombo_Type.HeaderText = "Combo_Simple";
            this.CCombo_Type.Name = "CCombo_Type";
            this.CCombo_Type.ReadOnly = true;
            this.CCombo_Type.Visible = false;
            this.CCombo_Type.Width = 102;
            // 
            // CCombo_Label_1
            // 
            this.CCombo_Label_1.HeaderText = "Combo_Label";
            this.CCombo_Label_1.Name = "CCombo_Label_1";
            this.CCombo_Label_1.ReadOnly = true;
            this.CCombo_Label_1.Visible = false;
            this.CCombo_Label_1.Width = 97;
            // 
            // label_play
            // 
            this.label_play.BackColor = System.Drawing.Color.White;
            this.label_play.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_play.ForeColor = System.Drawing.Color.DarkSeaGreen;
            this.label_play.Location = new System.Drawing.Point(154, 41);
            this.label_play.Name = "label_play";
            this.label_play.Size = new System.Drawing.Size(882, 23);
            this.label_play.TabIndex = 9;
            this.label_play.Text = "OK ...";
            this.label_play.TextAlign = System.Drawing.ContentAlignment.MiddleLeft;
            this.label_play.Visible = false;
            // 
            // button_add_label
            // 
            this.button_add_label.Location = new System.Drawing.Point(219, 99);
            this.button_add_label.Name = "button_add_label";
            this.button_add_label.Size = new System.Drawing.Size(101, 28);
            this.button_add_label.TabIndex = 11;
            this.button_add_label.Text = "Add Row";
            this.button_add_label.UseVisualStyleBackColor = true;
            this.button_add_label.Visible = false;
            this.button_add_label.Click += new System.EventHandler(this.button_add_label_Click);
            // 
            // textBox_2
            // 
            this.textBox_2.Location = new System.Drawing.Point(157, 159);
            this.textBox_2.Name = "textBox_2";
            this.textBox_2.Size = new System.Drawing.Size(758, 20);
            this.textBox_2.TabIndex = 13;
            // 
            // button_remove_label
            // 
            this.button_remove_label.Location = new System.Drawing.Point(37, 99);
            this.button_remove_label.Name = "button_remove_label";
            this.button_remove_label.Size = new System.Drawing.Size(101, 28);
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
            this.label_instructions_1.Visible = false;
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
            this.label_instructions_2.Visible = false;
            // 
            // button_save
            // 
            this.button_save.Location = new System.Drawing.Point(577, 99);
            this.button_save.Name = "button_save";
            this.button_save.Size = new System.Drawing.Size(101, 28);
            this.button_save.TabIndex = 17;
            this.button_save.Text = "Save Category";
            this.button_save.UseVisualStyleBackColor = true;
            this.button_save.Visible = false;
            this.button_save.Click += new System.EventHandler(this.button_save_Click);
            // 
            // button_2
            // 
            this.button_2.Location = new System.Drawing.Point(397, 295);
            this.button_2.Name = "button_2";
            this.button_2.Size = new System.Drawing.Size(281, 52);
            this.button_2.TabIndex = 18;
            this.button_2.Text = "Start";
            this.button_2.UseVisualStyleBackColor = true;
            this.button_2.Click += new System.EventHandler(this.button_2_Click);
            // 
            // button_generate
            // 
            this.button_generate.Location = new System.Drawing.Point(756, 99);
            this.button_generate.Name = "button_generate";
            this.button_generate.Size = new System.Drawing.Size(101, 28);
            this.button_generate.TabIndex = 19;
            this.button_generate.Text = "Generate Xml";
            this.button_generate.UseVisualStyleBackColor = true;
            this.button_generate.Visible = false;
            this.button_generate.Click += new System.EventHandler(this.button_generate_Click);
            // 
            // button_exit
            // 
            this.button_exit.Location = new System.Drawing.Point(935, 99);
            this.button_exit.Name = "button_exit";
            this.button_exit.Size = new System.Drawing.Size(101, 28);
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
            this.textBox_instructions.Location = new System.Drawing.Point(37, 201);
            this.textBox_instructions.Multiline = true;
            this.textBox_instructions.Name = "textBox_instructions";
            this.textBox_instructions.Size = new System.Drawing.Size(1002, 35);
            this.textBox_instructions.TabIndex = 21;
            this.textBox_instructions.Text = " ";
            // 
            // button_session_part
            // 
            this.button_session_part.Location = new System.Drawing.Point(398, 99);
            this.button_session_part.Name = "button_session_part";
            this.button_session_part.Size = new System.Drawing.Size(101, 28);
            this.button_session_part.TabIndex = 22;
            this.button_session_part.Text = "Next Category";
            this.button_session_part.UseVisualStyleBackColor = true;
            this.button_session_part.Visible = false;
            this.button_session_part.Click += new System.EventHandler(this.button_session_part_Click);
            // 
            // label_files_path
            // 
            this.label_files_path.AutoSize = true;
            this.label_files_path.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_files_path.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_files_path.Location = new System.Drawing.Point(37, 123);
            this.label_files_path.Name = "label_files_path";
            this.label_files_path.Size = new System.Drawing.Size(111, 15);
            this.label_files_path.TabIndex = 23;
            this.label_files_path.Text = "Audio Files Path";
            // 
            // label_protocol_path
            // 
            this.label_protocol_path.AutoSize = true;
            this.label_protocol_path.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_protocol_path.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_protocol_path.Location = new System.Drawing.Point(37, 160);
            this.label_protocol_path.Name = "label_protocol_path";
            this.label_protocol_path.Size = new System.Drawing.Size(93, 15);
            this.label_protocol_path.TabIndex = 24;
            this.label_protocol_path.Text = "Protocol Path";
            // 
            // button_3
            // 
            this.button_3.Location = new System.Drawing.Point(935, 159);
            this.button_3.Name = "button_3";
            this.button_3.Size = new System.Drawing.Size(101, 23);
            this.button_3.TabIndex = 25;
            this.button_3.Text = "Browse";
            this.button_3.UseVisualStyleBackColor = true;
            this.button_3.Click += new System.EventHandler(this.button_3_Click);
            // 
            // FormAnnotation
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.DimGray;
            this.ClientSize = new System.Drawing.Size(1075, 529);
            this.Controls.Add(this.button_3);
            this.Controls.Add(this.label_protocol_path);
            this.Controls.Add(this.label_files_path);
            this.Controls.Add(this.button_session_part);
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
            this.Controls.Add(this.label_date);
            this.Controls.Add(this.textBox_1);
            this.Controls.Add(this.button_1);
            this.Controls.Add(this.textBox_2);
            this.Controls.Add(this.dataGridView1);
            this.Name = "FormAnnotation";
            this.Text = "Audio Annotation";
            this.Load += new System.EventHandler(this.FormAnnotation_Load);
            this.FormClosing += new System.Windows.Forms.FormClosingEventHandler(this.FormAnnotation_FormClosing);
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
        private System.Windows.Forms.Button button_generate;
        private System.Windows.Forms.Button button_exit;
        private System.Windows.Forms.TextBox textBox_instructions;
        private System.Windows.Forms.DataGridViewTextBoxColumn CID;
        private System.Windows.Forms.DataGridViewCheckBoxColumn CPostureLock;
        private System.Windows.Forms.DataGridViewComboBoxColumn CPosture;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStartEnd;
        private System.Windows.Forms.DataGridViewTextBoxColumn CTime;
        private System.Windows.Forms.DataGridViewTextBoxColumn CTimeLabel;
        private System.Windows.Forms.DataGridViewTextBoxColumn CNotes;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStatus;
        private System.Windows.Forms.DataGridViewTextBoxColumn CStartID;
        private System.Windows.Forms.DataGridViewTextBoxColumn CEndID;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Type;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Label_1;
        private System.Windows.Forms.Button button_session_part;
        private System.Windows.Forms.Label label_files_path;
        private System.Windows.Forms.Label label_protocol_path;
        private System.Windows.Forms.Button button_3;
        private System.Windows.Forms.FolderBrowserDialog folderBrowserDialog;
        private System.Windows.Forms.OpenFileDialog openFileDialog;
    }
}

