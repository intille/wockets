using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

//using WocketsApp.Properties;


namespace KernelApp.GUI
{
    class MainControlPanel:Panel
    {

        public ImageButtonClick MainMenuButton;
        public ImageButtonClick RightButton;
        public ImageButtonClick LeftButton;

        private int panel_width;
        private int panel_height;
        private Color panel_bgcolor = Color.Gainsboro;


        //Labels
        private Label label_left = new Label();
        private Label label_center = new Label();
        private Label label_right = new Label();


        public MainControlPanel(int width, int height,
                                 Bitmap leftImage, Bitmap leftImagePressed,
                                 Bitmap centerImage, Bitmap centerImagePressed,
                                 Bitmap rightImage, Bitmap rightImagePressed,
                                 String sleft, String scenter, String sright)
         {
         
            int upper_gap = 15;

            //Wall parameters
            panel_width = width;
            panel_height = height;

            this.Size = new Size(panel_width, panel_height);
            this.Location = new Point(0, 0);
            this.Visible = true;
            this.BackColor = panel_bgcolor;


            //labels parameters
            Color label_color = Color.DimGray;
            Font panel_labels_font = new Font("Tahoma", 8, FontStyle.Regular);
            int labels_width = 90;
            int labels_height = 30;


            //buttons
            int button_width = rightImage.Width;
            int button_height = rightImage.Height;
            int pos_y = upper_gap + button_height;

            ////Button Prev Button
            LeftButton = new ImageButtonClick(leftImage, leftImagePressed);
            LeftButton.Size = new Size(button_width, button_height);
            LeftButton.Location = new Point(45, upper_gap);
            LeftButton.Visible = true;
            this.Controls.Add(LeftButton);

            //Previous Label
            label_left.Text = sleft;
            label_left.Font = panel_labels_font;
            label_left.TextAlign = ContentAlignment.TopCenter;
            label_left.ForeColor = label_color;
            label_left.Size = new Size(labels_width, labels_height);
            label_left.Location = new Point(30, pos_y);
            this.Controls.Add(label_left);



            ////Button Main Menu
            MainMenuButton = new ImageButtonClick( centerImage, centerImagePressed);
            MainMenuButton.Size = new Size(button_width, button_height);
            MainMenuButton.Location = new Point(205, upper_gap);
            MainMenuButton.Visible = true;
            this.Controls.Add(MainMenuButton);
            
            //Main Menu Label
            label_center.Text = scenter;
            label_center.Font = panel_labels_font;
            label_center.TextAlign = ContentAlignment.TopCenter;
            label_center.ForeColor = label_color;
            label_center.Size = new Size(labels_width, labels_height);
            label_center.Location = new Point(190, pos_y);
            this.Controls.Add(label_center);


            ////Button Next Button
            RightButton = new ImageButtonClick(rightImage, rightImagePressed);
            RightButton.Size = new Size(button_width, button_height);
            RightButton.Location = new Point(365, upper_gap);
            RightButton.Visible = true;
            this.Controls.Add(RightButton);

            //Next Label
            label_right.Text = sright;
            label_right.Font = panel_labels_font;
            label_right.TextAlign = ContentAlignment.TopCenter;
            label_right.ForeColor = label_color;
            label_right.Size= new Size(labels_width, labels_height);
            label_right.Location = new Point(350, pos_y);
            this.Controls.Add(label_right);


           

        }


        
    }
}
