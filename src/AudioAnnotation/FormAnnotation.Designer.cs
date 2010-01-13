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
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle1 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle2 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle10 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle11 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle12 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle3 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle4 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle5 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle6 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle7 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle8 = new System.Windows.Forms.DataGridViewCellStyle();
            System.Windows.Forms.DataGridViewCellStyle dataGridViewCellStyle9 = new System.Windows.Forms.DataGridViewCellStyle();
            System.ComponentModel.ComponentResourceManager resources = new System.ComponentModel.ComponentResourceManager(typeof(FormAnnotation));
            this.button_1 = new System.Windows.Forms.Button();
            this.textBox_1 = new System.Windows.Forms.TextBox();
            this.label_date = new System.Windows.Forms.Label();
            this.dataGridView1 = new System.Windows.Forms.DataGridView();
            this.CID = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CAutoStop_1 = new System.Windows.Forms.DataGridViewCheckBoxColumn();
            this.CCategory_1 = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartEnd_1 = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CAutoStop_2 = new System.Windows.Forms.DataGridViewCheckBoxColumn();
            this.CCategory_2 = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartEnd_2 = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CTime = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CTimeLabel = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CNotes = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CStatus_1 = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartID_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CEndID_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Type_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Label_1 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CStatus_2 = new System.Windows.Forms.DataGridViewComboBoxColumn();
            this.CStartID_2 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CEndID_2 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Type_2 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.CCombo_Label_2 = new System.Windows.Forms.DataGridViewTextBoxColumn();
            this.label_play = new System.Windows.Forms.Label();
            this.button_add = new System.Windows.Forms.Button();
            this.button_remove = new System.Windows.Forms.Button();
            this.label_instructions_1 = new System.Windows.Forms.Label();
            this.label_instructions_2 = new System.Windows.Forms.Label();
            this.button_save = new System.Windows.Forms.Button();
            this.button_2 = new System.Windows.Forms.Button();
            this.button_generate = new System.Windows.Forms.Button();
            this.button_exit = new System.Windows.Forms.Button();
            this.textBox_instructions_1 = new System.Windows.Forms.TextBox();
            this.button_category_select = new System.Windows.Forms.Button();
            this.label_files_path = new System.Windows.Forms.Label();
            this.folderBrowserDialog = new System.Windows.Forms.FolderBrowserDialog();
            this.openFileDialog = new System.Windows.Forms.OpenFileDialog();
            this.checkBox_SiglePassMode = new System.Windows.Forms.CheckBox();
            this.panel_controls_2 = new System.Windows.Forms.Panel();
            this.label_exit_button = new System.Windows.Forms.Label();
            this.label_generate_button = new System.Windows.Forms.Label();
            this.label_save_button = new System.Windows.Forms.Label();
            this.label_category_button = new System.Windows.Forms.Label();
            this.label_add_button = new System.Windows.Forms.Label();
            this.label_remove_button = new System.Windows.Forms.Label();
            this.label_instructions_3 = new System.Windows.Forms.Label();
            this.checkBox_ExitWithoutSaving = new System.Windows.Forms.CheckBox();
            this.panel_controls_1 = new System.Windows.Forms.Panel();
            this.label_panel1_2 = new System.Windows.Forms.Label();
            this.label_panel1_1 = new System.Windows.Forms.Label();
            this.textBox_instructions_2 = new System.Windows.Forms.TextBox();
            this.openFileDialog_Session = new System.Windows.Forms.OpenFileDialog();
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).BeginInit();
            this.panel_controls_2.SuspendLayout();
            this.panel_controls_1.SuspendLayout();
            this.SuspendLayout();
            // 
            // button_1
            // 
            this.button_1.Location = new System.Drawing.Point(891, 294);
            this.button_1.Name = "button_1";
            this.button_1.Size = new System.Drawing.Size(101, 23);
            this.button_1.TabIndex = 0;
            this.button_1.Text = "Browse";
            this.button_1.UseVisualStyleBackColor = true;
            this.button_1.Click += new System.EventHandler(this.button_load_Click);
            // 
            // textBox_1
            // 
            this.textBox_1.Location = new System.Drawing.Point(127, 295);
            this.textBox_1.Name = "textBox_1";
            this.textBox_1.Size = new System.Drawing.Size(758, 20);
            this.textBox_1.TabIndex = 1;
            // 
            // label_date
            // 
            this.label_date.AutoSize = true;
            this.label_date.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_date.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_date.Location = new System.Drawing.Point(6, 0);
            this.label_date.Name = "label_date";
            this.label_date.Size = new System.Drawing.Size(152, 13);
            this.label_date.TabIndex = 5;
            this.label_date.Text = "Experiment Date:  10/12/2009";
            this.label_date.Visible = false;
            // 
            // dataGridView1
            // 
            this.dataGridView1.AccessibleRole = System.Windows.Forms.AccessibleRole.None;
            dataGridViewCellStyle1.NullValue = null;
            this.dataGridView1.AlternatingRowsDefaultCellStyle = dataGridViewCellStyle1;
            this.dataGridView1.AutoSizeColumnsMode = System.Windows.Forms.DataGridViewAutoSizeColumnsMode.ColumnHeader;
            this.dataGridView1.BackgroundColor = System.Drawing.Color.YellowGreen;
            this.dataGridView1.BorderStyle = System.Windows.Forms.BorderStyle.Fixed3D;
            this.dataGridView1.CellBorderStyle = System.Windows.Forms.DataGridViewCellBorderStyle.Sunken;
            this.dataGridView1.ColumnHeadersBorderStyle = System.Windows.Forms.DataGridViewHeaderBorderStyle.Sunken;
            dataGridViewCellStyle2.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle2.BackColor = System.Drawing.SystemColors.Control;
            dataGridViewCellStyle2.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle2.ForeColor = System.Drawing.Color.Black;
            dataGridViewCellStyle2.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle2.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle2.WrapMode = System.Windows.Forms.DataGridViewTriState.True;
            this.dataGridView1.ColumnHeadersDefaultCellStyle = dataGridViewCellStyle2;
            this.dataGridView1.Columns.AddRange(new System.Windows.Forms.DataGridViewColumn[] {
            this.CID,
            this.CAutoStop_1,
            this.CCategory_1,
            this.CStartEnd_1,
            this.CAutoStop_2,
            this.CCategory_2,
            this.CStartEnd_2,
            this.CTime,
            this.CTimeLabel,
            this.CNotes,
            this.CStatus_1,
            this.CStartID_1,
            this.CEndID_1,
            this.CCombo_Type_1,
            this.CCombo_Label_1,
            this.CStatus_2,
            this.CStartID_2,
            this.CEndID_2,
            this.CCombo_Type_2,
            this.CCombo_Label_2});
            dataGridViewCellStyle10.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleLeft;
            dataGridViewCellStyle10.BackColor = System.Drawing.SystemColors.Window;
            dataGridViewCellStyle10.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle10.ForeColor = System.Drawing.SystemColors.ControlText;
            dataGridViewCellStyle10.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle10.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle10.WrapMode = System.Windows.Forms.DataGridViewTriState.False;
            this.dataGridView1.DefaultCellStyle = dataGridViewCellStyle10;
            this.dataGridView1.EnableHeadersVisualStyles = false;
            this.dataGridView1.GridColor = System.Drawing.Color.LightGray;
            this.dataGridView1.ImeMode = System.Windows.Forms.ImeMode.NoControl;
            this.dataGridView1.Location = new System.Drawing.Point(3, 233);
            this.dataGridView1.MultiSelect = false;
            this.dataGridView1.Name = "dataGridView1";
            this.dataGridView1.RowHeadersBorderStyle = System.Windows.Forms.DataGridViewHeaderBorderStyle.Single;
            dataGridViewCellStyle11.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleLeft;
            dataGridViewCellStyle11.BackColor = System.Drawing.SystemColors.Control;
            dataGridViewCellStyle11.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            dataGridViewCellStyle11.ForeColor = System.Drawing.Color.White;
            dataGridViewCellStyle11.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            dataGridViewCellStyle11.SelectionForeColor = System.Drawing.SystemColors.HighlightText;
            dataGridViewCellStyle11.WrapMode = System.Windows.Forms.DataGridViewTriState.True;
            this.dataGridView1.RowHeadersDefaultCellStyle = dataGridViewCellStyle11;
            this.dataGridView1.RowHeadersWidthSizeMode = System.Windows.Forms.DataGridViewRowHeadersWidthSizeMode.AutoSizeToAllHeaders;
            dataGridViewCellStyle12.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.dataGridView1.RowsDefaultCellStyle = dataGridViewCellStyle12;
            this.dataGridView1.RowTemplate.DefaultCellStyle.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.dataGridView1.RowTemplate.Resizable = System.Windows.Forms.DataGridViewTriState.False;
            this.dataGridView1.SelectionMode = System.Windows.Forms.DataGridViewSelectionMode.FullRowSelect;
            this.dataGridView1.Size = new System.Drawing.Size(1036, 310);
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
            dataGridViewCellStyle3.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            dataGridViewCellStyle3.NullValue = null;
            dataGridViewCellStyle3.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            this.CID.DefaultCellStyle = dataGridViewCellStyle3;
            this.CID.FillWeight = 80F;
            this.CID.HeaderText = "Audio ID";
            this.CID.Name = "CID";
            this.CID.ReadOnly = true;
            this.CID.Width = 73;
            // 
            // CAutoStop_1
            // 
            dataGridViewCellStyle4.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle4.NullValue = "False";
            this.CAutoStop_1.DefaultCellStyle = dataGridViewCellStyle4;
            this.CAutoStop_1.FillWeight = 50F;
            this.CAutoStop_1.HeaderText = "Auto Stop";
            this.CAutoStop_1.Name = "CAutoStop_1";
            this.CAutoStop_1.Visible = false;
            this.CAutoStop_1.Width = 60;
            // 
            // CCategory_1
            // 
            this.CCategory_1.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.ComboBox;
            this.CCategory_1.DisplayStyleForCurrentCellOnly = true;
            this.CCategory_1.FillWeight = 200F;
            this.CCategory_1.HeaderText = "Category";
            this.CCategory_1.Name = "CCategory_1";
            this.CCategory_1.Width = 55;
            // 
            // CStartEnd_1
            // 
            dataGridViewCellStyle5.BackColor = System.Drawing.Color.White;
            this.CStartEnd_1.DefaultCellStyle = dataGridViewCellStyle5;
            this.CStartEnd_1.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.ComboBox;
            this.CStartEnd_1.DisplayStyleForCurrentCellOnly = true;
            this.CStartEnd_1.HeaderText = "Start/End Tag";
            this.CStartEnd_1.Name = "CStartEnd_1";
            this.CStartEnd_1.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CStartEnd_1.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            // 
            // CAutoStop_2
            // 
            this.CAutoStop_2.FillWeight = 50F;
            this.CAutoStop_2.HeaderText = "Auto Stop 2";
            this.CAutoStop_2.Name = "CAutoStop_2";
            this.CAutoStop_2.Visible = false;
            this.CAutoStop_2.Width = 69;
            // 
            // CCategory_2
            // 
            this.CCategory_2.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.ComboBox;
            this.CCategory_2.DisplayStyleForCurrentCellOnly = true;
            this.CCategory_2.FillWeight = 200F;
            this.CCategory_2.HeaderText = "Category II";
            this.CCategory_2.Name = "CCategory_2";
            this.CCategory_2.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CCategory_2.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            this.CCategory_2.Width = 83;
            // 
            // CStartEnd_2
            // 
            this.CStartEnd_2.DisplayStyle = System.Windows.Forms.DataGridViewComboBoxDisplayStyle.ComboBox;
            this.CStartEnd_2.DisplayStyleForCurrentCellOnly = true;
            this.CStartEnd_2.HeaderText = "Start/End Tag";
            this.CStartEnd_2.Name = "CStartEnd_2";
            this.CStartEnd_2.Width = 81;
            // 
            // CTime
            // 
            dataGridViewCellStyle6.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            dataGridViewCellStyle6.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            dataGridViewCellStyle6.Format = "T";
            dataGridViewCellStyle6.SelectionBackColor = System.Drawing.Color.DarkSeaGreen;
            this.CTime.DefaultCellStyle = dataGridViewCellStyle6;
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
            dataGridViewCellStyle7.Alignment = System.Windows.Forms.DataGridViewContentAlignment.MiddleCenter;
            this.CNotes.DefaultCellStyle = dataGridViewCellStyle7;
            this.CNotes.FillWeight = 150F;
            this.CNotes.HeaderText = "Notes";
            this.CNotes.Name = "CNotes";
            this.CNotes.Width = 60;
            // 
            // CStatus_1
            // 
            this.CStatus_1.HeaderText = "Status";
            this.CStatus_1.Name = "CStatus_1";
            this.CStatus_1.ReadOnly = true;
            this.CStatus_1.Resizable = System.Windows.Forms.DataGridViewTriState.True;
            this.CStatus_1.SortMode = System.Windows.Forms.DataGridViewColumnSortMode.Automatic;
            this.CStatus_1.Visible = false;
            this.CStatus_1.Width = 62;
            // 
            // CStartID_1
            // 
            dataGridViewCellStyle8.Format = "N0";
            dataGridViewCellStyle8.NullValue = null;
            this.CStartID_1.DefaultCellStyle = dataGridViewCellStyle8;
            this.CStartID_1.HeaderText = "StartID";
            this.CStartID_1.Name = "CStartID_1";
            this.CStartID_1.ReadOnly = true;
            this.CStartID_1.Visible = false;
            this.CStartID_1.Width = 65;
            // 
            // CEndID_1
            // 
            dataGridViewCellStyle9.Format = "N0";
            dataGridViewCellStyle9.NullValue = null;
            this.CEndID_1.DefaultCellStyle = dataGridViewCellStyle9;
            this.CEndID_1.HeaderText = "EndID";
            this.CEndID_1.Name = "CEndID_1";
            this.CEndID_1.ReadOnly = true;
            this.CEndID_1.Visible = false;
            this.CEndID_1.Width = 62;
            // 
            // CCombo_Type_1
            // 
            this.CCombo_Type_1.HeaderText = "Combo Type I";
            this.CCombo_Type_1.Name = "CCombo_Type_1";
            this.CCombo_Type_1.ReadOnly = true;
            this.CCombo_Type_1.Visible = false;
            this.CCombo_Type_1.Width = 98;
            // 
            // CCombo_Label_1
            // 
            this.CCombo_Label_1.HeaderText = "Combo Label I";
            this.CCombo_Label_1.Name = "CCombo_Label_1";
            this.CCombo_Label_1.ReadOnly = true;
            this.CCombo_Label_1.Visible = false;
            // 
            // CStatus_2
            // 
            this.CStatus_2.HeaderText = "Status II";
            this.CStatus_2.Name = "CStatus_2";
            this.CStatus_2.Visible = false;
            this.CStatus_2.Width = 52;
            // 
            // CStartID_2
            // 
            this.CStartID_2.HeaderText = "StartID II";
            this.CStartID_2.Name = "CStartID_2";
            this.CStartID_2.Visible = false;
            this.CStartID_2.Width = 74;
            // 
            // CEndID_2
            // 
            this.CEndID_2.HeaderText = "EndID II";
            this.CEndID_2.Name = "CEndID_2";
            this.CEndID_2.Visible = false;
            this.CEndID_2.Width = 71;
            // 
            // CCombo_Type_2
            // 
            this.CCombo_Type_2.HeaderText = "Combo Type II";
            this.CCombo_Type_2.Name = "CCombo_Type_2";
            this.CCombo_Type_2.Visible = false;
            this.CCombo_Type_2.Width = 101;
            // 
            // CCombo_Label_2
            // 
            this.CCombo_Label_2.HeaderText = "Combo_Label II";
            this.CCombo_Label_2.Name = "CCombo_Label_2";
            this.CCombo_Label_2.Visible = false;
            this.CCombo_Label_2.Width = 106;
            // 
            // label_play
            // 
            this.label_play.BackColor = System.Drawing.Color.White;
            this.label_play.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_play.ForeColor = System.Drawing.Color.DarkSeaGreen;
            this.label_play.Location = new System.Drawing.Point(54, 85);
            this.label_play.Name = "label_play";
            this.label_play.Size = new System.Drawing.Size(938, 23);
            this.label_play.TabIndex = 9;
            this.label_play.Text = "OK ...";
            this.label_play.TextAlign = System.Drawing.ContentAlignment.MiddleLeft;
            this.label_play.Visible = false;
            // 
            // button_add
            // 
            this.button_add.BackColor = System.Drawing.Color.Transparent;
            this.button_add.FlatAppearance.BorderColor = System.Drawing.Color.White;
            this.button_add.FlatAppearance.BorderSize = 0;
            this.button_add.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.button_add.ForeColor = System.Drawing.Color.Transparent;
            this.button_add.Location = new System.Drawing.Point(204, 138);
            this.button_add.Name = "button_add";
            this.button_add.Size = new System.Drawing.Size(48, 48);
            this.button_add.TabIndex = 11;
            this.button_add.UseVisualStyleBackColor = false;
            this.button_add.Visible = false;
            this.button_add.Click += new System.EventHandler(this.button_add_label_Click);
            // 
            // button_remove
            // 
            this.button_remove.AutoEllipsis = true;
            this.button_remove.BackColor = System.Drawing.Color.Transparent;
            this.button_remove.BackgroundImageLayout = System.Windows.Forms.ImageLayout.Zoom;
            this.button_remove.FlatAppearance.BorderColor = System.Drawing.Color.White;
            this.button_remove.FlatAppearance.BorderSize = 0;
            this.button_remove.FlatAppearance.MouseOverBackColor = System.Drawing.Color.Gainsboro;
            this.button_remove.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.button_remove.ForeColor = System.Drawing.Color.Transparent;
            this.button_remove.Location = new System.Drawing.Point(19, 138);
            this.button_remove.Name = "button_remove";
            this.button_remove.Size = new System.Drawing.Size(48, 48);
            this.button_remove.TabIndex = 14;
            this.button_remove.TextAlign = System.Drawing.ContentAlignment.BottomCenter;
            this.button_remove.UseVisualStyleBackColor = false;
            this.button_remove.Visible = false;
            this.button_remove.Click += new System.EventHandler(this.button_remove_label_Click);
            // 
            // label_instructions_1
            // 
            this.label_instructions_1.AutoSize = true;
            this.label_instructions_1.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_instructions_1.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_instructions_1.Location = new System.Drawing.Point(736, 54);
            this.label_instructions_1.Name = "label_instructions_1";
            this.label_instructions_1.Size = new System.Drawing.Size(237, 13);
            this.label_instructions_1.TabIndex = 15;
            this.label_instructions_1.Text = "Press F1 to play audio file.   Press F2 to edit field.";
            this.label_instructions_1.Visible = false;
            // 
            // label_instructions_2
            // 
            this.label_instructions_2.AutoSize = true;
            this.label_instructions_2.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_instructions_2.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_instructions_2.Location = new System.Drawing.Point(7, 88);
            this.label_instructions_2.Name = "label_instructions_2";
            this.label_instructions_2.Size = new System.Drawing.Size(41, 15);
            this.label_instructions_2.TabIndex = 16;
            this.label_instructions_2.Text = "Status";
            this.label_instructions_2.Visible = false;
            // 
            // button_save
            // 
            this.button_save.BackColor = System.Drawing.Color.Transparent;
            this.button_save.FlatAppearance.BorderSize = 0;
            this.button_save.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.button_save.ForeColor = System.Drawing.Color.Transparent;
            this.button_save.Location = new System.Drawing.Point(574, 138);
            this.button_save.Name = "button_save";
            this.button_save.Size = new System.Drawing.Size(48, 48);
            this.button_save.TabIndex = 17;
            this.button_save.UseVisualStyleBackColor = false;
            this.button_save.Visible = false;
            this.button_save.Click += new System.EventHandler(this.button_save_Click);
            // 
            // button_2
            // 
            this.button_2.BackColor = System.Drawing.SystemColors.ButtonFace;
            this.button_2.Location = new System.Drawing.Point(356, 453);
            this.button_2.Name = "button_2";
            this.button_2.Size = new System.Drawing.Size(281, 52);
            this.button_2.TabIndex = 18;
            this.button_2.Text = "Start";
            this.button_2.UseVisualStyleBackColor = true;
            this.button_2.Click += new System.EventHandler(this.button_2_Click);
            // 
            // button_generate
            // 
            this.button_generate.BackColor = System.Drawing.Color.Transparent;
            this.button_generate.FlatAppearance.BorderSize = 0;
            this.button_generate.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.button_generate.ForeColor = System.Drawing.Color.Transparent;
            this.button_generate.Location = new System.Drawing.Point(759, 138);
            this.button_generate.Name = "button_generate";
            this.button_generate.Size = new System.Drawing.Size(48, 48);
            this.button_generate.TabIndex = 19;
            this.button_generate.UseVisualStyleBackColor = false;
            this.button_generate.Visible = false;
            this.button_generate.Click += new System.EventHandler(this.button_generate_Click);
            // 
            // button_exit
            // 
            this.button_exit.BackColor = System.Drawing.Color.Transparent;
            this.button_exit.FlatAppearance.BorderSize = 0;
            this.button_exit.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.button_exit.ForeColor = System.Drawing.Color.Transparent;
            this.button_exit.Location = new System.Drawing.Point(944, 138);
            this.button_exit.Name = "button_exit";
            this.button_exit.Size = new System.Drawing.Size(48, 48);
            this.button_exit.TabIndex = 20;
            this.button_exit.UseVisualStyleBackColor = false;
            this.button_exit.Visible = false;
            this.button_exit.Click += new System.EventHandler(this.button_exit_Click);
            // 
            // textBox_instructions_1
            // 
            this.textBox_instructions_1.BackColor = System.Drawing.Color.DimGray;
            this.textBox_instructions_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_instructions_1.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_instructions_1.ForeColor = System.Drawing.Color.White;
            this.textBox_instructions_1.Location = new System.Drawing.Point(13, 256);
            this.textBox_instructions_1.Multiline = true;
            this.textBox_instructions_1.Name = "textBox_instructions_1";
            this.textBox_instructions_1.Size = new System.Drawing.Size(982, 35);
            this.textBox_instructions_1.TabIndex = 21;
            this.textBox_instructions_1.Text = " ";
            // 
            // button_category_select
            // 
            this.button_category_select.BackColor = System.Drawing.Color.Transparent;
            this.button_category_select.FlatAppearance.BorderSize = 0;
            this.button_category_select.FlatAppearance.MouseOverBackColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.button_category_select.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.button_category_select.ForeColor = System.Drawing.Color.Transparent;
            this.button_category_select.Location = new System.Drawing.Point(389, 138);
            this.button_category_select.Name = "button_category_select";
            this.button_category_select.Size = new System.Drawing.Size(48, 48);
            this.button_category_select.TabIndex = 22;
            this.button_category_select.UseVisualStyleBackColor = false;
            this.button_category_select.Visible = false;
            this.button_category_select.Click += new System.EventHandler(this.button_session_part_Click);
            // 
            // label_files_path
            // 
            this.label_files_path.AutoSize = true;
            this.label_files_path.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_files_path.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_files_path.Location = new System.Drawing.Point(7, 294);
            this.label_files_path.Name = "label_files_path";
            this.label_files_path.Size = new System.Drawing.Size(91, 15);
            this.label_files_path.TabIndex = 23;
            this.label_files_path.Text = "Session Path";
            // 
            // checkBox_SiglePassMode
            // 
            this.checkBox_SiglePassMode.AutoSize = true;
            this.checkBox_SiglePassMode.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.checkBox_SiglePassMode.Location = new System.Drawing.Point(9, 65);
            this.checkBox_SiglePassMode.Name = "checkBox_SiglePassMode";
            this.checkBox_SiglePassMode.Size = new System.Drawing.Size(111, 17);
            this.checkBox_SiglePassMode.TabIndex = 26;
            this.checkBox_SiglePassMode.Text = "Single Pass Mode";
            this.checkBox_SiglePassMode.UseVisualStyleBackColor = true;
            this.checkBox_SiglePassMode.Visible = false;
            this.checkBox_SiglePassMode.CheckedChanged += new System.EventHandler(this.checkBox_SiglePassMode_CheckedChanged);
            // 
            // panel_controls_2
            // 
            this.panel_controls_2.BackColor = System.Drawing.Color.Transparent;
            this.panel_controls_2.Controls.Add(this.label_exit_button);
            this.panel_controls_2.Controls.Add(this.label_generate_button);
            this.panel_controls_2.Controls.Add(this.label_save_button);
            this.panel_controls_2.Controls.Add(this.label_category_button);
            this.panel_controls_2.Controls.Add(this.label_add_button);
            this.panel_controls_2.Controls.Add(this.label_remove_button);
            this.panel_controls_2.Controls.Add(this.label_instructions_3);
            this.panel_controls_2.Controls.Add(this.checkBox_ExitWithoutSaving);
            this.panel_controls_2.Controls.Add(this.label_date);
            this.panel_controls_2.Controls.Add(this.button_exit);
            this.panel_controls_2.Controls.Add(this.checkBox_SiglePassMode);
            this.panel_controls_2.Controls.Add(this.button_add);
            this.panel_controls_2.Controls.Add(this.button_remove);
            this.panel_controls_2.Controls.Add(this.button_save);
            this.panel_controls_2.Controls.Add(this.button_generate);
            this.panel_controls_2.Controls.Add(this.button_category_select);
            this.panel_controls_2.Controls.Add(this.label_play);
            this.panel_controls_2.Controls.Add(this.label_instructions_1);
            this.panel_controls_2.Controls.Add(this.label_instructions_2);
            this.panel_controls_2.Location = new System.Drawing.Point(15, 12);
            this.panel_controls_2.Name = "panel_controls_2";
            this.panel_controls_2.Size = new System.Drawing.Size(1006, 215);
            this.panel_controls_2.TabIndex = 27;
            this.panel_controls_2.Visible = false;
            // 
            // label_exit_button
            // 
            this.label_exit_button.AutoSize = true;
            this.label_exit_button.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_exit_button.Location = new System.Drawing.Point(936, 189);
            this.label_exit_button.Name = "label_exit_button";
            this.label_exit_button.Size = new System.Drawing.Size(64, 13);
            this.label_exit_button.TabIndex = 34;
            this.label_exit_button.Text = "Exit Session";
            this.label_exit_button.Visible = false;
            // 
            // label_generate_button
            // 
            this.label_generate_button.AutoSize = true;
            this.label_generate_button.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_generate_button.Location = new System.Drawing.Point(748, 189);
            this.label_generate_button.Name = "label_generate_button";
            this.label_generate_button.Size = new System.Drawing.Size(71, 13);
            this.label_generate_button.TabIndex = 33;
            this.label_generate_button.Text = "Generate Xml";
            this.label_generate_button.Visible = false;
            // 
            // label_save_button
            // 
            this.label_save_button.AutoSize = true;
            this.label_save_button.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_save_button.Location = new System.Drawing.Point(562, 189);
            this.label_save_button.Name = "label_save_button";
            this.label_save_button.Size = new System.Drawing.Size(72, 13);
            this.label_save_button.TabIndex = 32;
            this.label_save_button.Text = "Save Session";
            this.label_save_button.Visible = false;
            // 
            // label_category_button
            // 
            this.label_category_button.AutoSize = true;
            this.label_category_button.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_category_button.Location = new System.Drawing.Point(369, 189);
            this.label_category_button.Name = "label_category_button";
            this.label_category_button.Size = new System.Drawing.Size(89, 13);
            this.label_category_button.TabIndex = 31;
            this.label_category_button.Text = "Change Category";
            this.label_category_button.Visible = false;
            // 
            // label_add_button
            // 
            this.label_add_button.AutoSize = true;
            this.label_add_button.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_add_button.Location = new System.Drawing.Point(203, 189);
            this.label_add_button.Name = "label_add_button";
            this.label_add_button.Size = new System.Drawing.Size(51, 13);
            this.label_add_button.TabIndex = 30;
            this.label_add_button.Text = "Add Row";
            this.label_add_button.Visible = false;
            // 
            // label_remove_button
            // 
            this.label_remove_button.AutoSize = true;
            this.label_remove_button.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_remove_button.Location = new System.Drawing.Point(5, 189);
            this.label_remove_button.Name = "label_remove_button";
            this.label_remove_button.Size = new System.Drawing.Size(72, 13);
            this.label_remove_button.TabIndex = 29;
            this.label_remove_button.Text = "Remove Row";
            this.label_remove_button.Visible = false;
            // 
            // label_instructions_3
            // 
            this.label_instructions_3.AutoSize = true;
            this.label_instructions_3.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_instructions_3.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.label_instructions_3.Location = new System.Drawing.Point(736, 70);
            this.label_instructions_3.Name = "label_instructions_3";
            this.label_instructions_3.Size = new System.Drawing.Size(256, 13);
            this.label_instructions_3.TabIndex = 28;
            this.label_instructions_3.Text = "Fields cannot be edited while the audio file is playing.";
            this.label_instructions_3.Visible = false;
            // 
            // checkBox_ExitWithoutSaving
            // 
            this.checkBox_ExitWithoutSaving.AutoSize = true;
            this.checkBox_ExitWithoutSaving.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(224)))), ((int)(((byte)(224)))), ((int)(((byte)(224)))));
            this.checkBox_ExitWithoutSaving.Location = new System.Drawing.Point(9, 36);
            this.checkBox_ExitWithoutSaving.Name = "checkBox_ExitWithoutSaving";
            this.checkBox_ExitWithoutSaving.Size = new System.Drawing.Size(119, 17);
            this.checkBox_ExitWithoutSaving.TabIndex = 27;
            this.checkBox_ExitWithoutSaving.Text = "Exit Without Saving";
            this.checkBox_ExitWithoutSaving.UseVisualStyleBackColor = true;
            this.checkBox_ExitWithoutSaving.Visible = false;
            // 
            // panel_controls_1
            // 
            this.panel_controls_1.BackColor = System.Drawing.Color.Transparent;
            this.panel_controls_1.Controls.Add(this.label_panel1_2);
            this.panel_controls_1.Controls.Add(this.label_panel1_1);
            this.panel_controls_1.Controls.Add(this.button_2);
            this.panel_controls_1.Controls.Add(this.button_1);
            this.panel_controls_1.Controls.Add(this.textBox_instructions_1);
            this.panel_controls_1.Controls.Add(this.textBox_1);
            this.panel_controls_1.Controls.Add(this.label_files_path);
            this.panel_controls_1.Controls.Add(this.textBox_instructions_2);
            this.panel_controls_1.Location = new System.Drawing.Point(12, 12);
            this.panel_controls_1.Name = "panel_controls_1";
            this.panel_controls_1.Size = new System.Drawing.Size(1009, 534);
            this.panel_controls_1.TabIndex = 28;
            // 
            // label_panel1_2
            // 
            this.label_panel1_2.AutoSize = true;
            this.label_panel1_2.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_panel1_2.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_panel1_2.Location = new System.Drawing.Point(888, 0);
            this.label_panel1_2.Name = "label_panel1_2";
            this.label_panel1_2.Size = new System.Drawing.Size(109, 15);
            this.label_panel1_2.TabIndex = 31;
            this.label_panel1_2.Text = "MIT   HOUSE_N";
            // 
            // label_panel1_1
            // 
            this.label_panel1_1.AutoSize = true;
            this.label_panel1_1.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label_panel1_1.ForeColor = System.Drawing.Color.Gainsboro;
            this.label_panel1_1.Location = new System.Drawing.Point(124, 26);
            this.label_panel1_1.Name = "label_panel1_1";
            this.label_panel1_1.Size = new System.Drawing.Size(108, 15);
            this.label_panel1_1.TabIndex = 30;
            this.label_panel1_1.Text = "INSTRUCTIONS";
            // 
            // textBox_instructions_2
            // 
            this.textBox_instructions_2.BackColor = System.Drawing.Color.DarkSeaGreen;
            this.textBox_instructions_2.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.textBox_instructions_2.Font = new System.Drawing.Font("Arial", 9F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.textBox_instructions_2.ForeColor = System.Drawing.Color.White;
            this.textBox_instructions_2.Location = new System.Drawing.Point(127, 44);
            this.textBox_instructions_2.Multiline = true;
            this.textBox_instructions_2.Name = "textBox_instructions_2";
            this.textBox_instructions_2.ReadOnly = true;
            this.textBox_instructions_2.Size = new System.Drawing.Size(758, 194);
            this.textBox_instructions_2.TabIndex = 29;
            this.textBox_instructions_2.Text = resources.GetString("textBox_instructions_2.Text");
            // 
            // FormAnnotation
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.DimGray;
            this.ClientSize = new System.Drawing.Size(1075, 609);
            this.Controls.Add(this.panel_controls_2);
            this.Controls.Add(this.dataGridView1);
            this.Controls.Add(this.panel_controls_1);
            this.Name = "FormAnnotation";

            this.Text = "Wockets Annotator - Version 1.20 January 12,2010";
            this.Load += new System.EventHandler(this.FormAnnotation_Load);
            this.SizeChanged += new System.EventHandler(this.FormAnnotation_SizeChanged);
            this.FormClosing += new System.Windows.Forms.FormClosingEventHandler(this.FormAnnotation_FormClosing);
            ((System.ComponentModel.ISupportInitialize)(this.dataGridView1)).EndInit();
            this.panel_controls_2.ResumeLayout(false);
            this.panel_controls_2.PerformLayout();
            this.panel_controls_1.ResumeLayout(false);
            this.panel_controls_1.PerformLayout();
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Button button_1;
        private System.Windows.Forms.TextBox textBox_1;
        private System.Windows.Forms.Label label_date;
        private System.Windows.Forms.DataGridView dataGridView1;
        private System.Windows.Forms.Label label_play;
        private System.Windows.Forms.Button button_add;
        private System.Windows.Forms.Button button_remove;
        private System.Windows.Forms.Label label_instructions_1;
        private System.Windows.Forms.Label label_instructions_2;
        private System.Windows.Forms.Button button_save;
        private System.Windows.Forms.Button button_2;
        private System.Windows.Forms.Button button_generate;
        private System.Windows.Forms.Button button_exit;
        private System.Windows.Forms.TextBox textBox_instructions_1;
        private System.Windows.Forms.Button button_category_select;
        private System.Windows.Forms.Label label_files_path;
        private System.Windows.Forms.FolderBrowserDialog folderBrowserDialog;
        private System.Windows.Forms.OpenFileDialog openFileDialog;
        private System.Windows.Forms.CheckBox checkBox_SiglePassMode;
        private System.Windows.Forms.Panel panel_controls_2;
        private System.Windows.Forms.Panel panel_controls_1;
        private System.Windows.Forms.TextBox textBox_instructions_2;
        private System.Windows.Forms.OpenFileDialog openFileDialog_Session;
        private System.Windows.Forms.Label label_panel1_1;
        private System.Windows.Forms.Label label_panel1_2;
        private System.Windows.Forms.CheckBox checkBox_ExitWithoutSaving;
        private System.Windows.Forms.Label label_instructions_3;
        private System.Windows.Forms.Label label_remove_button;
        private System.Windows.Forms.Label label_add_button;
        private System.Windows.Forms.Label label_category_button;
        private System.Windows.Forms.Label label_save_button;
        private System.Windows.Forms.Label label_exit_button;
        private System.Windows.Forms.Label label_generate_button;
        private System.Windows.Forms.DataGridViewTextBoxColumn CID;
        private System.Windows.Forms.DataGridViewCheckBoxColumn CAutoStop_1;
        private System.Windows.Forms.DataGridViewComboBoxColumn CCategory_1;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStartEnd_1;
        private System.Windows.Forms.DataGridViewCheckBoxColumn CAutoStop_2;
        private System.Windows.Forms.DataGridViewComboBoxColumn CCategory_2;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStartEnd_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CTime;
        private System.Windows.Forms.DataGridViewTextBoxColumn CTimeLabel;
        private System.Windows.Forms.DataGridViewTextBoxColumn CNotes;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStatus_1;
        private System.Windows.Forms.DataGridViewTextBoxColumn CStartID_1;
        private System.Windows.Forms.DataGridViewTextBoxColumn CEndID_1;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Type_1;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Label_1;
        private System.Windows.Forms.DataGridViewComboBoxColumn CStatus_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CStartID_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CEndID_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Type_2;
        private System.Windows.Forms.DataGridViewTextBoxColumn CCombo_Label_2;
    }
}

