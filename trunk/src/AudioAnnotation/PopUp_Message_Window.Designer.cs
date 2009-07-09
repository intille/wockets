namespace AudioAnnotation
{
    partial class PopUp_Message_Window
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
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
            this.label1 = new System.Windows.Forms.Label();
            this.button_popup_load = new System.Windows.Forms.Button();
            this.button_popup_create = new System.Windows.Forms.Button();
            this.SuspendLayout();
            // 
            // label1
            // 
            this.label1.AutoSize = true;
            this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.label1.ForeColor = System.Drawing.Color.White;
            this.label1.Location = new System.Drawing.Point(25, 13);
            this.label1.Name = "label1";
            this.label1.Size = new System.Drawing.Size(564, 15);
            this.label1.TabIndex = 0;
            this.label1.Text = "The program has found a previous annotation session. Please indicate how to proce" +
                "ed.";
            // 
            // button_popup_load
            // 
            this.button_popup_load.Location = new System.Drawing.Point(486, 51);
            this.button_popup_load.Name = "button_popup_load";
            this.button_popup_load.Size = new System.Drawing.Size(131, 23);
            this.button_popup_load.TabIndex = 1;
            this.button_popup_load.Text = "Load Previous Session";
            this.button_popup_load.UseVisualStyleBackColor = true;
            this.button_popup_load.Click += new System.EventHandler(this.button_popup_load_Click);
            // 
            // button_popup_create
            // 
            this.button_popup_create.Location = new System.Drawing.Point(28, 51);
            this.button_popup_create.Name = "button_popup_create";
            this.button_popup_create.Size = new System.Drawing.Size(131, 23);
            this.button_popup_create.TabIndex = 2;
            this.button_popup_create.Text = "Create New Session";
            this.button_popup_create.UseVisualStyleBackColor = true;
            this.button_popup_create.Click += new System.EventHandler(this.button_popup_create_Click);
            // 
            // PopUp_Message_Window
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.YellowGreen;
            this.ClientSize = new System.Drawing.Size(668, 93);
            this.Controls.Add(this.button_popup_create);
            this.Controls.Add(this.button_popup_load);
            this.Controls.Add(this.label1);
            this.FormBorderStyle = System.Windows.Forms.FormBorderStyle.FixedDialog;
            this.MaximizeBox = false;
            this.MinimizeBox = false;
            this.Name = "PopUp_Message_Window";
            this.Padding = new System.Windows.Forms.Padding(9);
            this.ShowIcon = false;
            this.ShowInTaskbar = false;
            this.StartPosition = System.Windows.Forms.FormStartPosition.CenterParent;
            this.Text = "Audio Annotation:  Start Session";
            this.Load += new System.EventHandler(this.PopUp_Message_Window_Load);
            this.ResumeLayout(false);
            this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.Label label1;
        private System.Windows.Forms.Button button_popup_load;
        private System.Windows.Forms.Button button_popup_create;

    }
}
