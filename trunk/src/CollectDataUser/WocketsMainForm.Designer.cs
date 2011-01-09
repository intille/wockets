namespace CollectDataUser
{
    partial class WocketsMainForm
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
            this.menuMainAppActions = new System.Windows.Forms.MenuItem();
            this.menuQuitApp = new System.Windows.Forms.MenuItem();
            this.textBox_elapsed_time = new System.Windows.Forms.TextBox();
            this.label_software_version = new System.Windows.Forms.Label();
            this.SwapPanel = new System.Windows.Forms.Panel();
            this.button_reboot_phone = new System.Windows.Forms.Button();
            this.textBox_sensors_status_1 = new System.Windows.Forms.TextBox();
            this.textBox_sensors_status_0 = new System.Windows.Forms.TextBox();
            this.textBox_sensor_location_1 = new System.Windows.Forms.TextBox();
            this.textBox_sensor_location_0 = new System.Windows.Forms.TextBox();
            this.SwapSensorsButton = new System.Windows.Forms.Button();
            this.textBox1 = new System.Windows.Forms.TextBox();
            this.textBox_sensors_status = new System.Windows.Forms.TextBox();
            this.textBox_sensor_set_ID = new System.Windows.Forms.TextBox();
            this.button_reboot_phone = new System.Windows.Forms.Button();
            this.SensorStatusPanel = new System.Windows.Forms.Panel();
            this.textBox_spanel_ac_full_1 = new System.Windows.Forms.TextBox();
            this.textBox19 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_last_1 = new System.Windows.Forms.TextBox();
            this.textBox21 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_new_1 = new System.Windows.Forms.TextBox();
            this.textBox23 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_empty_1 = new System.Windows.Forms.TextBox();
            this.textBox25 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_partial_1 = new System.Windows.Forms.TextBox();
            this.textBox27 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_full_0 = new System.Windows.Forms.TextBox();
            this.textBox8 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_last_0 = new System.Windows.Forms.TextBox();
            this.textBox11 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_new_0 = new System.Windows.Forms.TextBox();
            this.textBox13 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_empty_0 = new System.Windows.Forms.TextBox();
            this.textBox15 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_ac_partial_0 = new System.Windows.Forms.TextBox();
            this.textBox17 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_sensors_location_1 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_sensors_location_0 = new System.Windows.Forms.TextBox();
            this.textBox_spanel_sensors_status = new System.Windows.Forms.TextBox();
            this.textBox_spanel_sensors_ID = new System.Windows.Forms.TextBox();
            this.ConnectPanel = new System.Windows.Forms.Panel();
            this.label_kernel_status = new System.Windows.Forms.Label();
            this.UploadDataPanel = new System.Windows.Forms.Panel();
            this.textBox_updater_last_update = new System.Windows.Forms.TextBox();
            this.textBox6 = new System.Windows.Forms.TextBox();
            this.textBox3 = new System.Windows.Forms.TextBox();
            this.textBox_uploader_failed_files = new System.Windows.Forms.TextBox();
            this.textBox9 = new System.Windows.Forms.TextBox();
            this.textBox_uploader_successful_files = new System.Windows.Forms.TextBox();
            this.textBox7 = new System.Windows.Forms.TextBox();
            this.textBox_uploader_duration = new System.Windows.Forms.TextBox();
            this.textBox5 = new System.Windows.Forms.TextBox();
            this.textBox_uploader_new_files = new System.Windows.Forms.TextBox();
            this.textBox2 = new System.Windows.Forms.TextBox();
            this.UploadButton = new System.Windows.Forms.Button();
            this.label_upload_data_status = new System.Windows.Forms.Label();
            this.ElapsedTimePanel = new System.Windows.Forms.Panel();
            this.label_phone_IMEI = new System.Windows.Forms.Label();
            this.MainActionsPanel = new System.Windows.Forms.Panel();
            this.textBox_main_sensor_set_ID = new System.Windows.Forms.TextBox();
            this.textBox_main_sensor_status = new System.Windows.Forms.TextBox();
            this.SensorsStatusButton = new System.Windows.Forms.Button();
            this.UploadDataActionButton = new System.Windows.Forms.Button();
            this.SelectSensorsButton = new System.Windows.Forms.Button();
            this.SwapPanel.SuspendLayout();
            this.SensorStatusPanel.SuspendLayout();
            this.ConnectPanel.SuspendLayout();
            this.UploadDataPanel.SuspendLayout();
            this.ElapsedTimePanel.SuspendLayout();
            this.MainActionsPanel.SuspendLayout();
            this.SuspendLayout();
            // 
            // mainMenu1
            // 
            this.mainMenu1.MenuItems.Add(this.menuMainAppActions);
            this.mainMenu1.MenuItems.Add(this.menuQuitApp);
            // 
            // menuMainAppActions
            // 
            this.menuMainAppActions.Text = "Minimize";
            this.menuMainAppActions.Click += new System.EventHandler(this.menuMainAppActions_Click);
            // 
            // menuQuitApp
            // 
            this.menuQuitApp.Text = "Quit";
            this.menuQuitApp.Click += new System.EventHandler(this.menuQuitApp_Click);
            // 
            // textBox_elapsed_time
            // 
            this.textBox_elapsed_time.BackColor = System.Drawing.Color.White;
            this.textBox_elapsed_time.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_elapsed_time.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_elapsed_time.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_elapsed_time.Location = new System.Drawing.Point(5, 23);
            this.textBox_elapsed_time.Multiline = true;
            this.textBox_elapsed_time.Name = "textBox_elapsed_time";
            this.textBox_elapsed_time.ReadOnly = true;
            this.textBox_elapsed_time.Size = new System.Drawing.Size(215, 20);
            this.textBox_elapsed_time.TabIndex = 1;
            this.textBox_elapsed_time.TabStop = false;
            this.textBox_elapsed_time.Text = "00h:00m:00s";
            this.textBox_elapsed_time.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            this.textBox_elapsed_time.WordWrap = false;
            // 
            // label_software_version
            // 
            this.label_software_version.Font = new System.Drawing.Font("Tahoma", 8F, System.Drawing.FontStyle.Regular);
            this.label_software_version.ForeColor = System.Drawing.SystemColors.ControlDark;
            this.label_software_version.Location = new System.Drawing.Point(11, 5);
            this.label_software_version.Name = "label_software_version";
            this.label_software_version.Size = new System.Drawing.Size(101, 15);
            this.label_software_version.Text = "Version:";
            // 
            // SwapPanel
            // 
            this.SwapPanel.Controls.Add(this.button_reboot_phone);
            this.SwapPanel.Controls.Add(this.textBox_sensors_status_1);
            this.SwapPanel.Controls.Add(this.textBox_sensors_status_0);
            this.SwapPanel.Controls.Add(this.textBox_sensor_location_1);
            this.SwapPanel.Controls.Add(this.textBox_sensor_location_0);
            this.SwapPanel.Controls.Add(this.SwapSensorsButton);
            this.SwapPanel.Controls.Add(this.textBox1);
            this.SwapPanel.Controls.Add(this.textBox_sensors_status);
            this.SwapPanel.Controls.Add(this.textBox_sensor_set_ID);
            this.SwapPanel.Location = new System.Drawing.Point(0, 50);
            this.SwapPanel.Name = "SwapPanel";
            this.SwapPanel.Size = new System.Drawing.Size(230, 304);
            // 
            // button_reboot_phone
            // 
            this.button_reboot_phone.BackColor = System.Drawing.Color.LightSlateGray;
            this.button_reboot_phone.ForeColor = System.Drawing.Color.White;
            this.button_reboot_phone.Location = new System.Drawing.Point(45, 243);
            this.button_reboot_phone.Name = "button_reboot_phone";
            this.button_reboot_phone.Size = new System.Drawing.Size(137, 52);
            this.button_reboot_phone.TabIndex = 9;
            this.button_reboot_phone.Text = "Reboot Phone";
            this.button_reboot_phone.Click += new System.EventHandler(this.button_reboot_phone_Click);
            // 
            // textBox_sensors_status_1
            // 
            this.textBox_sensors_status_1.BackColor = System.Drawing.Color.White;
            this.textBox_sensors_status_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_sensors_status_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_sensors_status_1.Location = new System.Drawing.Point(107, 109);
            this.textBox_sensors_status_1.Multiline = true;
            this.textBox_sensors_status_1.Name = "textBox_sensors_status_1";
            this.textBox_sensors_status_1.ReadOnly = true;
            this.textBox_sensors_status_1.Size = new System.Drawing.Size(118, 21);
            this.textBox_sensors_status_1.TabIndex = 8;
            this.textBox_sensors_status_1.Text = "---";
            this.textBox_sensors_status_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_sensors_status_0
            // 
            this.textBox_sensors_status_0.BackColor = System.Drawing.Color.White;
            this.textBox_sensors_status_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_sensors_status_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_sensors_status_0.Location = new System.Drawing.Point(107, 84);
            this.textBox_sensors_status_0.Multiline = true;
            this.textBox_sensors_status_0.Name = "textBox_sensors_status_0";
            this.textBox_sensors_status_0.ReadOnly = true;
            this.textBox_sensors_status_0.Size = new System.Drawing.Size(118, 21);
            this.textBox_sensors_status_0.TabIndex = 7;
            this.textBox_sensors_status_0.Text = "---";
            this.textBox_sensors_status_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_sensor_location_1
            // 
            this.textBox_sensor_location_1.BackColor = System.Drawing.Color.White;
            this.textBox_sensor_location_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_sensor_location_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_sensor_location_1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_sensor_location_1.Location = new System.Drawing.Point(5, 109);
            this.textBox_sensor_location_1.Multiline = true;
            this.textBox_sensor_location_1.Name = "textBox_sensor_location_1";
            this.textBox_sensor_location_1.ReadOnly = true;
            this.textBox_sensor_location_1.Size = new System.Drawing.Size(105, 21);
            this.textBox_sensor_location_1.TabIndex = 6;
            this.textBox_sensor_location_1.Text = "2FFFF At Ankle";
            // 
            // textBox_sensor_location_0
            // 
            this.textBox_sensor_location_0.BackColor = System.Drawing.Color.White;
            this.textBox_sensor_location_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_sensor_location_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_sensor_location_0.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_sensor_location_0.Location = new System.Drawing.Point(5, 84);
            this.textBox_sensor_location_0.Multiline = true;
            this.textBox_sensor_location_0.Name = "textBox_sensor_location_0";
            this.textBox_sensor_location_0.ReadOnly = true;
            this.textBox_sensor_location_0.Size = new System.Drawing.Size(105, 21);
            this.textBox_sensor_location_0.TabIndex = 5;
            this.textBox_sensor_location_0.Text = "2FF34 At Wrist";
            // 
            // SwapSensorsButton
            // 
            this.SwapSensorsButton.BackColor = System.Drawing.Color.LightSlateGray;
            this.SwapSensorsButton.ForeColor = System.Drawing.Color.White;
            this.SwapSensorsButton.Location = new System.Drawing.Point(45, 161);
            this.SwapSensorsButton.Name = "SwapSensorsButton";
            this.SwapSensorsButton.Size = new System.Drawing.Size(137, 52);
            this.SwapSensorsButton.TabIndex = 4;
            this.SwapSensorsButton.Text = "Swap";
            this.SwapSensorsButton.Click += new System.EventHandler(this.SwapSensorsButton_Click);
            // 
            // textBox1
            // 
            this.textBox1.BackColor = System.Drawing.Color.White;
            this.textBox1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox1.Location = new System.Drawing.Point(7, 31);
            this.textBox1.Multiline = true;
            this.textBox1.Name = "textBox1";
            this.textBox1.ReadOnly = true;
            this.textBox1.Size = new System.Drawing.Size(62, 23);
            this.textBox1.TabIndex = 2;
            this.textBox1.Text = "Status:";
            // 
            // textBox_sensors_status
            // 
            this.textBox_sensors_status.BackColor = System.Drawing.Color.White;
            this.textBox_sensors_status.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_sensors_status.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_sensors_status.ForeColor = System.Drawing.Color.Tomato;
            this.textBox_sensors_status.Location = new System.Drawing.Point(75, 31);
            this.textBox_sensors_status.Multiline = true;
            this.textBox_sensors_status.Name = "textBox_sensors_status";
            this.textBox_sensors_status.ReadOnly = true;
            this.textBox_sensors_status.Size = new System.Drawing.Size(150, 23);
            this.textBox_sensors_status.TabIndex = 0;
            this.textBox_sensors_status.Text = "Disconnected";
            // 
            // textBox_sensor_set_ID
            // 
            this.textBox_sensor_set_ID.BackColor = System.Drawing.Color.Tomato;
            this.textBox_sensor_set_ID.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_sensor_set_ID.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_sensor_set_ID.ForeColor = System.Drawing.Color.White;
            this.textBox_sensor_set_ID.Location = new System.Drawing.Point(1, 1);
            this.textBox_sensor_set_ID.Multiline = true;
            this.textBox_sensor_set_ID.Name = "textBox_sensor_set_ID";
            this.textBox_sensor_set_ID.ReadOnly = true;
            this.textBox_sensor_set_ID.Size = new System.Drawing.Size(228, 27);
            this.textBox_sensor_set_ID.TabIndex = 1;
            this.textBox_sensor_set_ID.Text = "RED SET";
            this.textBox_sensor_set_ID.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // button_reboot_phone
            // 
            this.button_reboot_phone.BackColor = System.Drawing.Color.LightSlateGray;
            this.button_reboot_phone.ForeColor = System.Drawing.Color.White;
            this.button_reboot_phone.Location = new System.Drawing.Point(45, 243);
            this.button_reboot_phone.Name = "button_reboot_phone";
            this.button_reboot_phone.Size = new System.Drawing.Size(137, 52);
            this.button_reboot_phone.TabIndex = 9;
            this.button_reboot_phone.Text = "Reboot Phone";
            // 
            // SensorStatusPanel
            // 
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_full_1);
            this.SensorStatusPanel.Controls.Add(this.textBox19);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_last_1);
            this.SensorStatusPanel.Controls.Add(this.textBox21);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_new_1);
            this.SensorStatusPanel.Controls.Add(this.textBox23);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_empty_1);
            this.SensorStatusPanel.Controls.Add(this.textBox25);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_partial_1);
            this.SensorStatusPanel.Controls.Add(this.textBox27);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_full_0);
            this.SensorStatusPanel.Controls.Add(this.textBox8);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_last_0);
            this.SensorStatusPanel.Controls.Add(this.textBox11);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_new_0);
            this.SensorStatusPanel.Controls.Add(this.textBox13);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_empty_0);
            this.SensorStatusPanel.Controls.Add(this.textBox15);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_ac_partial_0);
            this.SensorStatusPanel.Controls.Add(this.textBox17);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_sensors_location_1);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_sensors_location_0);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_sensors_status);
            this.SensorStatusPanel.Controls.Add(this.textBox_spanel_sensors_ID);
            this.SensorStatusPanel.Location = new System.Drawing.Point(0, 50);
            this.SensorStatusPanel.Name = "SensorStatusPanel";
            this.SensorStatusPanel.Size = new System.Drawing.Size(230, 304);
            // 
            // textBox_spanel_ac_full_1
            // 
            this.textBox_spanel_ac_full_1.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_full_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_full_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_full_1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_full_1.Location = new System.Drawing.Point(116, 205);
            this.textBox_spanel_ac_full_1.Multiline = true;
            this.textBox_spanel_ac_full_1.Name = "textBox_spanel_ac_full_1";
            this.textBox_spanel_ac_full_1.ReadOnly = true;
            this.textBox_spanel_ac_full_1.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_full_1.TabIndex = 35;
            this.textBox_spanel_ac_full_1.Text = "0";
            this.textBox_spanel_ac_full_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox19
            // 
            this.textBox19.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox19.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox19.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox19.ForeColor = System.Drawing.Color.DimGray;
            this.textBox19.Location = new System.Drawing.Point(14, 205);
            this.textBox19.Multiline = true;
            this.textBox19.Name = "textBox19";
            this.textBox19.ReadOnly = true;
            this.textBox19.Size = new System.Drawing.Size(100, 18);
            this.textBox19.TabIndex = 34;
            this.textBox19.Text = "Full";
            // 
            // textBox_spanel_ac_last_1
            // 
            this.textBox_spanel_ac_last_1.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_last_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_last_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_last_1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_last_1.Location = new System.Drawing.Point(116, 277);
            this.textBox_spanel_ac_last_1.Multiline = true;
            this.textBox_spanel_ac_last_1.Name = "textBox_spanel_ac_last_1";
            this.textBox_spanel_ac_last_1.ReadOnly = true;
            this.textBox_spanel_ac_last_1.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_last_1.TabIndex = 33;
            this.textBox_spanel_ac_last_1.Text = "0";
            this.textBox_spanel_ac_last_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox21
            // 
            this.textBox21.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox21.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox21.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox21.ForeColor = System.Drawing.Color.DimGray;
            this.textBox21.Location = new System.Drawing.Point(14, 277);
            this.textBox21.Multiline = true;
            this.textBox21.Name = "textBox21";
            this.textBox21.ReadOnly = true;
            this.textBox21.Size = new System.Drawing.Size(100, 18);
            this.textBox21.TabIndex = 32;
            this.textBox21.Text = "Last";
            // 
            // textBox_spanel_ac_new_1
            // 
            this.textBox_spanel_ac_new_1.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_new_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_new_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_new_1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_new_1.Location = new System.Drawing.Point(116, 259);
            this.textBox_spanel_ac_new_1.Multiline = true;
            this.textBox_spanel_ac_new_1.Name = "textBox_spanel_ac_new_1";
            this.textBox_spanel_ac_new_1.ReadOnly = true;
            this.textBox_spanel_ac_new_1.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_new_1.TabIndex = 31;
            this.textBox_spanel_ac_new_1.Text = "0";
            this.textBox_spanel_ac_new_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox23
            // 
            this.textBox23.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox23.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox23.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox23.ForeColor = System.Drawing.Color.DimGray;
            this.textBox23.Location = new System.Drawing.Point(14, 259);
            this.textBox23.Multiline = true;
            this.textBox23.Name = "textBox23";
            this.textBox23.ReadOnly = true;
            this.textBox23.Size = new System.Drawing.Size(100, 18);
            this.textBox23.TabIndex = 30;
            this.textBox23.Text = "New";
            // 
            // textBox_spanel_ac_empty_1
            // 
            this.textBox_spanel_ac_empty_1.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_empty_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_empty_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_empty_1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_empty_1.Location = new System.Drawing.Point(116, 241);
            this.textBox_spanel_ac_empty_1.Multiline = true;
            this.textBox_spanel_ac_empty_1.Name = "textBox_spanel_ac_empty_1";
            this.textBox_spanel_ac_empty_1.ReadOnly = true;
            this.textBox_spanel_ac_empty_1.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_empty_1.TabIndex = 29;
            this.textBox_spanel_ac_empty_1.Text = "0";
            this.textBox_spanel_ac_empty_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox25
            // 
            this.textBox25.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox25.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox25.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox25.ForeColor = System.Drawing.Color.DimGray;
            this.textBox25.Location = new System.Drawing.Point(14, 241);
            this.textBox25.Multiline = true;
            this.textBox25.Name = "textBox25";
            this.textBox25.ReadOnly = true;
            this.textBox25.Size = new System.Drawing.Size(100, 18);
            this.textBox25.TabIndex = 28;
            this.textBox25.Text = "Lost";
            // 
            // textBox_spanel_ac_partial_1
            // 
            this.textBox_spanel_ac_partial_1.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_partial_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_partial_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_partial_1.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_partial_1.Location = new System.Drawing.Point(116, 223);
            this.textBox_spanel_ac_partial_1.Multiline = true;
            this.textBox_spanel_ac_partial_1.Name = "textBox_spanel_ac_partial_1";
            this.textBox_spanel_ac_partial_1.ReadOnly = true;
            this.textBox_spanel_ac_partial_1.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_partial_1.TabIndex = 27;
            this.textBox_spanel_ac_partial_1.Text = "0";
            this.textBox_spanel_ac_partial_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox27
            // 
            this.textBox27.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox27.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox27.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox27.ForeColor = System.Drawing.Color.DimGray;
            this.textBox27.Location = new System.Drawing.Point(14, 223);
            this.textBox27.Multiline = true;
            this.textBox27.Name = "textBox27";
            this.textBox27.ReadOnly = true;
            this.textBox27.Size = new System.Drawing.Size(100, 18);
            this.textBox27.TabIndex = 26;
            this.textBox27.Text = "Partial";
            // 
            // textBox_spanel_ac_full_0
            // 
            this.textBox_spanel_ac_full_0.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_full_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_full_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_full_0.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_full_0.Location = new System.Drawing.Point(116, 80);
            this.textBox_spanel_ac_full_0.Multiline = true;
            this.textBox_spanel_ac_full_0.Name = "textBox_spanel_ac_full_0";
            this.textBox_spanel_ac_full_0.ReadOnly = true;
            this.textBox_spanel_ac_full_0.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_full_0.TabIndex = 25;
            this.textBox_spanel_ac_full_0.Text = "0";
            this.textBox_spanel_ac_full_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox8
            // 
            this.textBox8.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox8.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox8.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox8.ForeColor = System.Drawing.Color.DimGray;
            this.textBox8.Location = new System.Drawing.Point(14, 80);
            this.textBox8.Multiline = true;
            this.textBox8.Name = "textBox8";
            this.textBox8.ReadOnly = true;
            this.textBox8.Size = new System.Drawing.Size(100, 18);
            this.textBox8.TabIndex = 24;
            this.textBox8.Text = "Full";
            // 
            // textBox_spanel_ac_last_0
            // 
            this.textBox_spanel_ac_last_0.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_last_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_last_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_last_0.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_last_0.Location = new System.Drawing.Point(116, 152);
            this.textBox_spanel_ac_last_0.Multiline = true;
            this.textBox_spanel_ac_last_0.Name = "textBox_spanel_ac_last_0";
            this.textBox_spanel_ac_last_0.ReadOnly = true;
            this.textBox_spanel_ac_last_0.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_last_0.TabIndex = 23;
            this.textBox_spanel_ac_last_0.Text = "0";
            this.textBox_spanel_ac_last_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox11
            // 
            this.textBox11.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox11.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox11.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox11.ForeColor = System.Drawing.Color.DimGray;
            this.textBox11.Location = new System.Drawing.Point(14, 152);
            this.textBox11.Multiline = true;
            this.textBox11.Name = "textBox11";
            this.textBox11.ReadOnly = true;
            this.textBox11.Size = new System.Drawing.Size(100, 18);
            this.textBox11.TabIndex = 22;
            this.textBox11.Text = "Last";
            // 
            // textBox_spanel_ac_new_0
            // 
            this.textBox_spanel_ac_new_0.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_new_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_new_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_new_0.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_new_0.Location = new System.Drawing.Point(116, 134);
            this.textBox_spanel_ac_new_0.Multiline = true;
            this.textBox_spanel_ac_new_0.Name = "textBox_spanel_ac_new_0";
            this.textBox_spanel_ac_new_0.ReadOnly = true;
            this.textBox_spanel_ac_new_0.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_new_0.TabIndex = 21;
            this.textBox_spanel_ac_new_0.Text = "0";
            this.textBox_spanel_ac_new_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox13
            // 
            this.textBox13.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox13.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox13.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox13.ForeColor = System.Drawing.Color.DimGray;
            this.textBox13.Location = new System.Drawing.Point(14, 134);
            this.textBox13.Multiline = true;
            this.textBox13.Name = "textBox13";
            this.textBox13.ReadOnly = true;
            this.textBox13.Size = new System.Drawing.Size(100, 18);
            this.textBox13.TabIndex = 20;
            this.textBox13.Text = "New";
            // 
            // textBox_spanel_ac_empty_0
            // 
            this.textBox_spanel_ac_empty_0.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_empty_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_empty_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_empty_0.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_empty_0.Location = new System.Drawing.Point(116, 116);
            this.textBox_spanel_ac_empty_0.Multiline = true;
            this.textBox_spanel_ac_empty_0.Name = "textBox_spanel_ac_empty_0";
            this.textBox_spanel_ac_empty_0.ReadOnly = true;
            this.textBox_spanel_ac_empty_0.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_empty_0.TabIndex = 19;
            this.textBox_spanel_ac_empty_0.Text = "0";
            this.textBox_spanel_ac_empty_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox15
            // 
            this.textBox15.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox15.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox15.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox15.ForeColor = System.Drawing.Color.DimGray;
            this.textBox15.Location = new System.Drawing.Point(14, 116);
            this.textBox15.Multiline = true;
            this.textBox15.Name = "textBox15";
            this.textBox15.ReadOnly = true;
            this.textBox15.Size = new System.Drawing.Size(100, 18);
            this.textBox15.TabIndex = 18;
            this.textBox15.Text = "Lost";
            // 
            // textBox_spanel_ac_partial_0
            // 
            this.textBox_spanel_ac_partial_0.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_spanel_ac_partial_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_ac_partial_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_ac_partial_0.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_spanel_ac_partial_0.Location = new System.Drawing.Point(116, 98);
            this.textBox_spanel_ac_partial_0.Multiline = true;
            this.textBox_spanel_ac_partial_0.Name = "textBox_spanel_ac_partial_0";
            this.textBox_spanel_ac_partial_0.ReadOnly = true;
            this.textBox_spanel_ac_partial_0.Size = new System.Drawing.Size(100, 18);
            this.textBox_spanel_ac_partial_0.TabIndex = 17;
            this.textBox_spanel_ac_partial_0.Text = "0";
            this.textBox_spanel_ac_partial_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox17
            // 
            this.textBox17.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox17.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox17.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox17.ForeColor = System.Drawing.Color.DimGray;
            this.textBox17.Location = new System.Drawing.Point(14, 98);
            this.textBox17.Multiline = true;
            this.textBox17.Name = "textBox17";
            this.textBox17.ReadOnly = true;
            this.textBox17.Size = new System.Drawing.Size(100, 18);
            this.textBox17.TabIndex = 16;
            this.textBox17.Text = "Partial";
            // 
            // textBox_spanel_sensors_location_1
            // 
            this.textBox_spanel_sensors_location_1.BackColor = System.Drawing.Color.White;
            this.textBox_spanel_sensors_location_1.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_sensors_location_1.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_sensors_location_1.Location = new System.Drawing.Point(15, 186);
            this.textBox_spanel_sensors_location_1.Multiline = true;
            this.textBox_spanel_sensors_location_1.Name = "textBox_spanel_sensors_location_1";
            this.textBox_spanel_sensors_location_1.ReadOnly = true;
            this.textBox_spanel_sensors_location_1.Size = new System.Drawing.Size(201, 21);
            this.textBox_spanel_sensors_location_1.TabIndex = 6;
            this.textBox_spanel_sensors_location_1.Text = "Sensor 2FFFF At Ankle";
            this.textBox_spanel_sensors_location_1.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_spanel_sensors_location_0
            // 
            this.textBox_spanel_sensors_location_0.BackColor = System.Drawing.Color.White;
            this.textBox_spanel_sensors_location_0.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_sensors_location_0.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_sensors_location_0.Location = new System.Drawing.Point(14, 60);
            this.textBox_spanel_sensors_location_0.Multiline = true;
            this.textBox_spanel_sensors_location_0.Name = "textBox_spanel_sensors_location_0";
            this.textBox_spanel_sensors_location_0.ReadOnly = true;
            this.textBox_spanel_sensors_location_0.Size = new System.Drawing.Size(202, 21);
            this.textBox_spanel_sensors_location_0.TabIndex = 5;
            this.textBox_spanel_sensors_location_0.Text = "Sensor 2FF34 At Wrist";
            this.textBox_spanel_sensors_location_0.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_spanel_sensors_status
            // 
            this.textBox_spanel_sensors_status.BackColor = System.Drawing.Color.White;
            this.textBox_spanel_sensors_status.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_sensors_status.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_sensors_status.ForeColor = System.Drawing.Color.Tomato;
            this.textBox_spanel_sensors_status.Location = new System.Drawing.Point(1, 31);
            this.textBox_spanel_sensors_status.Multiline = true;
            this.textBox_spanel_sensors_status.Name = "textBox_spanel_sensors_status";
            this.textBox_spanel_sensors_status.ReadOnly = true;
            this.textBox_spanel_sensors_status.Size = new System.Drawing.Size(228, 23);
            this.textBox_spanel_sensors_status.TabIndex = 0;
            this.textBox_spanel_sensors_status.Text = "Disconnected";
            this.textBox_spanel_sensors_status.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_spanel_sensors_ID
            // 
            this.textBox_spanel_sensors_ID.BackColor = System.Drawing.Color.Tomato;
            this.textBox_spanel_sensors_ID.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_spanel_sensors_ID.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_spanel_sensors_ID.ForeColor = System.Drawing.Color.White;
            this.textBox_spanel_sensors_ID.Location = new System.Drawing.Point(1, 1);
            this.textBox_spanel_sensors_ID.Multiline = true;
            this.textBox_spanel_sensors_ID.Name = "textBox_spanel_sensors_ID";
            this.textBox_spanel_sensors_ID.ReadOnly = true;
            this.textBox_spanel_sensors_ID.Size = new System.Drawing.Size(228, 27);
            this.textBox_spanel_sensors_ID.TabIndex = 1;
            this.textBox_spanel_sensors_ID.Text = "RED SET";
            this.textBox_spanel_sensors_ID.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // ConnectPanel
            // 
            this.ConnectPanel.Controls.Add(this.label_kernel_status);
            this.ConnectPanel.Location = new System.Drawing.Point(0, 50);
            this.ConnectPanel.Name = "ConnectPanel";
            this.ConnectPanel.Size = new System.Drawing.Size(230, 304);
            // 
            // label_kernel_status
            // 
            this.label_kernel_status.Font = new System.Drawing.Font("Tahoma", 12F, System.Drawing.FontStyle.Regular);
            this.label_kernel_status.Location = new System.Drawing.Point(25, 86);
            this.label_kernel_status.Name = "label_kernel_status";
            this.label_kernel_status.Size = new System.Drawing.Size(176, 36);
            this.label_kernel_status.Text = "...";
            this.label_kernel_status.TextAlign = System.Drawing.ContentAlignment.TopCenter;
            // 
            // UploadDataPanel
            // 
            this.UploadDataPanel.Controls.Add(this.textBox_updater_last_update);
            this.UploadDataPanel.Controls.Add(this.textBox6);
            this.UploadDataPanel.Controls.Add(this.textBox3);
            this.UploadDataPanel.Controls.Add(this.textBox_uploader_failed_files);
            this.UploadDataPanel.Controls.Add(this.textBox9);
            this.UploadDataPanel.Controls.Add(this.textBox_uploader_successful_files);
            this.UploadDataPanel.Controls.Add(this.textBox7);
            this.UploadDataPanel.Controls.Add(this.textBox_uploader_duration);
            this.UploadDataPanel.Controls.Add(this.textBox5);
            this.UploadDataPanel.Controls.Add(this.textBox_uploader_new_files);
            this.UploadDataPanel.Controls.Add(this.textBox2);
            this.UploadDataPanel.Controls.Add(this.UploadButton);
            this.UploadDataPanel.Controls.Add(this.label_upload_data_status);
            this.UploadDataPanel.Location = new System.Drawing.Point(0, 50);
            this.UploadDataPanel.Name = "UploadDataPanel";
            this.UploadDataPanel.Size = new System.Drawing.Size(230, 304);
            // 
            // textBox_updater_last_update
            // 
            this.textBox_updater_last_update.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_updater_last_update.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_updater_last_update.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_updater_last_update.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_updater_last_update.Location = new System.Drawing.Point(117, 163);
            this.textBox_updater_last_update.Multiline = true;
            this.textBox_updater_last_update.Name = "textBox_updater_last_update";
            this.textBox_updater_last_update.ReadOnly = true;
            this.textBox_updater_last_update.Size = new System.Drawing.Size(100, 21);
            this.textBox_updater_last_update.TabIndex = 15;
            this.textBox_updater_last_update.Text = "...";
            this.textBox_updater_last_update.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox6
            // 
            this.textBox6.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox6.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox6.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox6.ForeColor = System.Drawing.Color.DimGray;
            this.textBox6.Location = new System.Drawing.Point(13, 163);
            this.textBox6.Multiline = true;
            this.textBox6.Name = "textBox6";
            this.textBox6.ReadOnly = true;
            this.textBox6.Size = new System.Drawing.Size(100, 21);
            this.textBox6.TabIndex = 14;
            this.textBox6.Text = "Last Upload";
            this.textBox6.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox3
            // 
            this.textBox3.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox3.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox3.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox3.ForeColor = System.Drawing.Color.Black;
            this.textBox3.Location = new System.Drawing.Point(12, 134);
            this.textBox3.Multiline = true;
            this.textBox3.Name = "textBox3";
            this.textBox3.ReadOnly = true;
            this.textBox3.Size = new System.Drawing.Size(204, 21);
            this.textBox3.TabIndex = 12;
            this.textBox3.Text = "Upload Status";
            this.textBox3.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_uploader_failed_files
            // 
            this.textBox_uploader_failed_files.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_uploader_failed_files.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_uploader_failed_files.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_uploader_failed_files.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_uploader_failed_files.Location = new System.Drawing.Point(117, 275);
            this.textBox_uploader_failed_files.Multiline = true;
            this.textBox_uploader_failed_files.Name = "textBox_uploader_failed_files";
            this.textBox_uploader_failed_files.ReadOnly = true;
            this.textBox_uploader_failed_files.Size = new System.Drawing.Size(100, 21);
            this.textBox_uploader_failed_files.TabIndex = 10;
            this.textBox_uploader_failed_files.Text = "0";
            this.textBox_uploader_failed_files.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox9
            // 
            this.textBox9.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox9.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox9.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox9.ForeColor = System.Drawing.Color.DimGray;
            this.textBox9.Location = new System.Drawing.Point(13, 275);
            this.textBox9.Multiline = true;
            this.textBox9.Name = "textBox9";
            this.textBox9.ReadOnly = true;
            this.textBox9.Size = new System.Drawing.Size(100, 21);
            this.textBox9.TabIndex = 9;
            this.textBox9.Text = "Failed";
            this.textBox9.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_uploader_successful_files
            // 
            this.textBox_uploader_successful_files.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_uploader_successful_files.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_uploader_successful_files.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_uploader_successful_files.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_uploader_successful_files.Location = new System.Drawing.Point(117, 246);
            this.textBox_uploader_successful_files.Multiline = true;
            this.textBox_uploader_successful_files.Name = "textBox_uploader_successful_files";
            this.textBox_uploader_successful_files.ReadOnly = true;
            this.textBox_uploader_successful_files.Size = new System.Drawing.Size(100, 21);
            this.textBox_uploader_successful_files.TabIndex = 8;
            this.textBox_uploader_successful_files.Text = "0";
            this.textBox_uploader_successful_files.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox7
            // 
            this.textBox7.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox7.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox7.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox7.ForeColor = System.Drawing.Color.DimGray;
            this.textBox7.Location = new System.Drawing.Point(13, 246);
            this.textBox7.Multiline = true;
            this.textBox7.Name = "textBox7";
            this.textBox7.ReadOnly = true;
            this.textBox7.Size = new System.Drawing.Size(100, 21);
            this.textBox7.TabIndex = 7;
            this.textBox7.Text = "Successful";
            this.textBox7.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_uploader_duration
            // 
            this.textBox_uploader_duration.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_uploader_duration.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_uploader_duration.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_uploader_duration.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_uploader_duration.Location = new System.Drawing.Point(117, 217);
            this.textBox_uploader_duration.Multiline = true;
            this.textBox_uploader_duration.Name = "textBox_uploader_duration";
            this.textBox_uploader_duration.ReadOnly = true;
            this.textBox_uploader_duration.Size = new System.Drawing.Size(100, 21);
            this.textBox_uploader_duration.TabIndex = 6;
            this.textBox_uploader_duration.Text = "0";
            this.textBox_uploader_duration.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox5
            // 
            this.textBox5.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox5.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox5.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox5.ForeColor = System.Drawing.Color.DimGray;
            this.textBox5.Location = new System.Drawing.Point(13, 217);
            this.textBox5.Multiline = true;
            this.textBox5.Name = "textBox5";
            this.textBox5.ReadOnly = true;
            this.textBox5.Size = new System.Drawing.Size(100, 21);
            this.textBox5.TabIndex = 5;
            this.textBox5.Text = "Duration";
            this.textBox5.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_uploader_new_files
            // 
            this.textBox_uploader_new_files.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox_uploader_new_files.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_uploader_new_files.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_uploader_new_files.ForeColor = System.Drawing.Color.DimGray;
            this.textBox_uploader_new_files.Location = new System.Drawing.Point(117, 190);
            this.textBox_uploader_new_files.Multiline = true;
            this.textBox_uploader_new_files.Name = "textBox_uploader_new_files";
            this.textBox_uploader_new_files.ReadOnly = true;
            this.textBox_uploader_new_files.Size = new System.Drawing.Size(100, 21);
            this.textBox_uploader_new_files.TabIndex = 4;
            this.textBox_uploader_new_files.Text = "0";
            this.textBox_uploader_new_files.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox2
            // 
            this.textBox2.BackColor = System.Drawing.Color.Gainsboro;
            this.textBox2.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox2.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox2.ForeColor = System.Drawing.Color.DimGray;
            this.textBox2.Location = new System.Drawing.Point(13, 190);
            this.textBox2.Multiline = true;
            this.textBox2.Name = "textBox2";
            this.textBox2.ReadOnly = true;
            this.textBox2.Size = new System.Drawing.Size(100, 21);
            this.textBox2.TabIndex = 3;
            this.textBox2.Text = "New Files";
            this.textBox2.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // UploadButton
            // 
            this.UploadButton.BackColor = System.Drawing.Color.LightSlateGray;
            this.UploadButton.ForeColor = System.Drawing.Color.White;
            this.UploadButton.Location = new System.Drawing.Point(54, 63);
            this.UploadButton.Name = "UploadButton";
            this.UploadButton.Size = new System.Drawing.Size(120, 43);
            this.UploadButton.TabIndex = 1;
            this.UploadButton.Text = "Upload";
            this.UploadButton.Click += new System.EventHandler(this.UploadButton_Click);
            // 
            // label_upload_data_status
            // 
            this.label_upload_data_status.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.label_upload_data_status.Location = new System.Drawing.Point(13, 17);
            this.label_upload_data_status.Name = "label_upload_data_status";
            this.label_upload_data_status.Size = new System.Drawing.Size(203, 36);
            this.label_upload_data_status.Text = "...";
            this.label_upload_data_status.TextAlign = System.Drawing.ContentAlignment.TopCenter;
            // 
            // ElapsedTimePanel
            // 
            this.ElapsedTimePanel.Controls.Add(this.label_phone_IMEI);
            this.ElapsedTimePanel.Controls.Add(this.label_software_version);
            this.ElapsedTimePanel.Controls.Add(this.textBox_elapsed_time);
            this.ElapsedTimePanel.Location = new System.Drawing.Point(0, 3);
            this.ElapsedTimePanel.Name = "ElapsedTimePanel";
            this.ElapsedTimePanel.Size = new System.Drawing.Size(230, 46);
            // 
            // label_phone_IMEI
            // 
            this.label_phone_IMEI.Font = new System.Drawing.Font("Tahoma", 8F, System.Drawing.FontStyle.Regular);
            this.label_phone_IMEI.ForeColor = System.Drawing.SystemColors.ControlDark;
            this.label_phone_IMEI.Location = new System.Drawing.Point(116, 5);
            this.label_phone_IMEI.Name = "label_phone_IMEI";
            this.label_phone_IMEI.Size = new System.Drawing.Size(118, 15);
            this.label_phone_IMEI.Text = "IMEI:";
            // 
            // MainActionsPanel
            // 
            this.MainActionsPanel.Controls.Add(this.textBox_main_sensor_set_ID);
            this.MainActionsPanel.Controls.Add(this.textBox_main_sensor_status);
            this.MainActionsPanel.Controls.Add(this.SensorsStatusButton);
            this.MainActionsPanel.Controls.Add(this.UploadDataActionButton);
            this.MainActionsPanel.Controls.Add(this.SelectSensorsButton);
            this.MainActionsPanel.Location = new System.Drawing.Point(0, 50);
            this.MainActionsPanel.Name = "MainActionsPanel";
            this.MainActionsPanel.Size = new System.Drawing.Size(230, 304);
            // 
            // textBox_main_sensor_set_ID
            // 
            this.textBox_main_sensor_set_ID.BackColor = System.Drawing.Color.Tomato;
            this.textBox_main_sensor_set_ID.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_main_sensor_set_ID.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_main_sensor_set_ID.ForeColor = System.Drawing.Color.White;
            this.textBox_main_sensor_set_ID.Location = new System.Drawing.Point(1, 1);
            this.textBox_main_sensor_set_ID.Multiline = true;
            this.textBox_main_sensor_set_ID.Name = "textBox_main_sensor_set_ID";
            this.textBox_main_sensor_set_ID.ReadOnly = true;
            this.textBox_main_sensor_set_ID.Size = new System.Drawing.Size(228, 27);
            this.textBox_main_sensor_set_ID.TabIndex = 4;
            this.textBox_main_sensor_set_ID.Text = "RED SET";
            this.textBox_main_sensor_set_ID.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // textBox_main_sensor_status
            // 
            this.textBox_main_sensor_status.BackColor = System.Drawing.Color.White;
            this.textBox_main_sensor_status.BorderStyle = System.Windows.Forms.BorderStyle.None;
            this.textBox_main_sensor_status.Font = new System.Drawing.Font("Tahoma", 9F, System.Drawing.FontStyle.Bold);
            this.textBox_main_sensor_status.ForeColor = System.Drawing.Color.Tomato;
            this.textBox_main_sensor_status.Location = new System.Drawing.Point(1, 31);
            this.textBox_main_sensor_status.Multiline = true;
            this.textBox_main_sensor_status.Name = "textBox_main_sensor_status";
            this.textBox_main_sensor_status.ReadOnly = true;
            this.textBox_main_sensor_status.Size = new System.Drawing.Size(228, 23);
            this.textBox_main_sensor_status.TabIndex = 3;
            this.textBox_main_sensor_status.Text = "Disconnected";
            this.textBox_main_sensor_status.TextAlign = System.Windows.Forms.HorizontalAlignment.Center;
            // 
            // SensorsStatusButton
            // 
            this.SensorsStatusButton.BackColor = System.Drawing.Color.LightSlateGray;
            this.SensorsStatusButton.ForeColor = System.Drawing.Color.White;
            this.SensorsStatusButton.Location = new System.Drawing.Point(56, 219);
            this.SensorsStatusButton.Name = "SensorsStatusButton";
            this.SensorsStatusButton.Size = new System.Drawing.Size(120, 43);
            this.SensorsStatusButton.TabIndex = 2;
            this.SensorsStatusButton.Text = "Wockets Status";
            this.SensorsStatusButton.Click += new System.EventHandler(this.SensorsStatusButton_Click);
            // 
            // UploadDataActionButton
            // 
            this.UploadDataActionButton.BackColor = System.Drawing.Color.LightSlateGray;
            this.UploadDataActionButton.ForeColor = System.Drawing.Color.White;
            this.UploadDataActionButton.Location = new System.Drawing.Point(56, 141);
            this.UploadDataActionButton.Name = "UploadDataActionButton";
            this.UploadDataActionButton.Size = new System.Drawing.Size(120, 43);
            this.UploadDataActionButton.TabIndex = 1;
            this.UploadDataActionButton.Text = "Upload Data";
            this.UploadDataActionButton.Click += new System.EventHandler(this.UploadDataActionButton_Click);
            // 
            // SelectSensorsButton
            // 
            this.SelectSensorsButton.BackColor = System.Drawing.Color.LightSlateGray;
            this.SelectSensorsButton.ForeColor = System.Drawing.Color.White;
            this.SelectSensorsButton.Location = new System.Drawing.Point(56, 63);
            this.SelectSensorsButton.Name = "SelectSensorsButton";
            this.SelectSensorsButton.Size = new System.Drawing.Size(120, 43);
            this.SelectSensorsButton.TabIndex = 0;
            this.SelectSensorsButton.Text = "Swap Wockets";
            this.SelectSensorsButton.Click += new System.EventHandler(this.SelectSensorsButton_Click);
            // 
            // WocketsMainForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(96F, 96F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Dpi;
            this.AutoScroll = true;
            this.ClientSize = new System.Drawing.Size(240, 294);
            this.Controls.Add(this.ElapsedTimePanel);
            this.Controls.Add(this.SwapPanel);
            this.Controls.Add(this.ConnectPanel);
            this.Controls.Add(this.UploadDataPanel);
            this.Controls.Add(this.MainActionsPanel);
            this.Controls.Add(this.SensorStatusPanel);
            this.Location = new System.Drawing.Point(0, 0);
            this.Menu = this.mainMenu1;
            this.MinimizeBox = false;
            this.Name = "WocketsMainForm";
            this.Text = "Wockets";
            this.WindowState = System.Windows.Forms.FormWindowState.Maximized;
<<<<<<< .mine
            this.Closed += new System.EventHandler(this.WocketsMainForm_Closed);
            this.Closing += new System.ComponentModel.CancelEventHandler(this.WocketsMainForm_Closing);
=======
            this.Closing += new System.ComponentModel.CancelEventHandler(this.WocketsMainForm_Closing);
>>>>>>> .r575
            this.SwapPanel.ResumeLayout(false);
            this.SensorStatusPanel.ResumeLayout(false);
            this.ConnectPanel.ResumeLayout(false);
            this.UploadDataPanel.ResumeLayout(false);
            this.ElapsedTimePanel.ResumeLayout(false);
            this.MainActionsPanel.ResumeLayout(false);
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.MenuItem menuMainAppActions;
        private System.Windows.Forms.TextBox textBox_elapsed_time;
        private System.Windows.Forms.Label label_software_version;
        private System.Windows.Forms.Panel SwapPanel;
        private System.Windows.Forms.TextBox textBox_sensors_status;
        private System.Windows.Forms.TextBox textBox_sensor_set_ID;
        private System.Windows.Forms.TextBox textBox1;
        private System.Windows.Forms.Button SwapSensorsButton;
        private System.Windows.Forms.MenuItem menuQuitApp;
        private System.Windows.Forms.TextBox textBox_sensor_location_1;
        private System.Windows.Forms.TextBox textBox_sensor_location_0;
        private System.Windows.Forms.Panel ConnectPanel;
        private System.Windows.Forms.Panel ElapsedTimePanel;
        private System.Windows.Forms.Label label_kernel_status;
        private System.Windows.Forms.Panel MainActionsPanel;
        private System.Windows.Forms.Button SensorsStatusButton;
        private System.Windows.Forms.Button UploadDataActionButton;
        private System.Windows.Forms.Button SelectSensorsButton;
        private System.Windows.Forms.TextBox textBox_main_sensor_set_ID;
        private System.Windows.Forms.TextBox textBox_main_sensor_status;
        private System.Windows.Forms.Panel UploadDataPanel;
        private System.Windows.Forms.Label label_upload_data_status;
        private System.Windows.Forms.Button UploadButton;
        private System.Windows.Forms.TextBox textBox2;
        private System.Windows.Forms.TextBox textBox_uploader_successful_files;
        private System.Windows.Forms.TextBox textBox7;
        private System.Windows.Forms.TextBox textBox_uploader_duration;
        private System.Windows.Forms.TextBox textBox5;
        private System.Windows.Forms.TextBox textBox_uploader_new_files;
        private System.Windows.Forms.TextBox textBox_uploader_failed_files;
        private System.Windows.Forms.TextBox textBox9;
        private System.Windows.Forms.TextBox textBox3;
        private System.Windows.Forms.TextBox textBox_updater_last_update;
        private System.Windows.Forms.TextBox textBox6;
        private System.Windows.Forms.Panel SensorStatusPanel;
        private System.Windows.Forms.TextBox textBox_spanel_sensors_location_1;
        private System.Windows.Forms.TextBox textBox_spanel_sensors_location_0;
        private System.Windows.Forms.TextBox textBox_spanel_sensors_status;
        private System.Windows.Forms.TextBox textBox_spanel_sensors_ID;
        private System.Windows.Forms.TextBox textBox_spanel_ac_full_0;
        private System.Windows.Forms.TextBox textBox8;
        private System.Windows.Forms.TextBox textBox_spanel_ac_last_0;
        private System.Windows.Forms.TextBox textBox11;
        private System.Windows.Forms.TextBox textBox_spanel_ac_new_0;
        private System.Windows.Forms.TextBox textBox13;
        private System.Windows.Forms.TextBox textBox_spanel_ac_empty_0;
        private System.Windows.Forms.TextBox textBox15;
        private System.Windows.Forms.TextBox textBox_spanel_ac_partial_0;
        private System.Windows.Forms.TextBox textBox17;
        private System.Windows.Forms.TextBox textBox_spanel_ac_full_1;
        private System.Windows.Forms.TextBox textBox19;
        private System.Windows.Forms.TextBox textBox_spanel_ac_last_1;
        private System.Windows.Forms.TextBox textBox21;
        private System.Windows.Forms.TextBox textBox_spanel_ac_new_1;
        private System.Windows.Forms.TextBox textBox23;
        private System.Windows.Forms.TextBox textBox_spanel_ac_empty_1;
        private System.Windows.Forms.TextBox textBox25;
        private System.Windows.Forms.TextBox textBox_spanel_ac_partial_1;
        private System.Windows.Forms.TextBox textBox27;
        private System.Windows.Forms.Label label_phone_IMEI;
        private System.Windows.Forms.TextBox textBox_sensors_status_1;
        private System.Windows.Forms.TextBox textBox_sensors_status_0;
        private System.Windows.Forms.Button button_reboot_phone;
    }
}

