using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.Drawing;
using Wockets.Kernel.Types;
using Wockets.Kernel;


namespace KernelApp.GUI
{
    public class WocketListItem : Panel, IComparable
    {
        //public Label Title;
        public Label Mac;
        public int Index;
        //public Label Status;

        
        
        //public CheckBox checkButton;

        //private PictureBox backBox;
        //private PictureBox addButton;
        //private PictureBox removeButton;

        //private CheckBox WocketCheckBox;
        //private Pen borderPen = new Pen(Color.DarkGray, 1.0f);
        //private Color bg_color = Color.FromArgb(245, 219, 186);
        //public Color PictureBox_color = Color.White;
        
        

        public Color bg_color = Color.LightGray;
        public Color label_bg_unselected_color = Color.White;
        public Color label_unselected_color = Color.DimGray;

        public Color selected_color = Color.YellowGreen;
        public Color label_bg_selected_color = Color.White;
        public Color label_selected_color = Color.Black;


        //Wockets Configuration Information
        //Bluetooth Screen
       public string _MacAddress = "";
       public string _Name = "";
       public bool selected = false;


       public void SetBackgroundColor(Color bg)
       {
           this.BackColor = bg;
       }


       public void SetSelection(bool value)
       {
          
           if (value == false)
           {
               this.BackColor = bg_color;
               Mac.BackColor = label_bg_unselected_color;
               Mac.ForeColor = label_unselected_color;

           }
           else
           {
               this.BackColor = selected_color;
               Mac.BackColor = label_bg_selected_color;
               Mac.ForeColor = label_selected_color;
               
           }
       }




        public int CompareTo(object wi)
        {
            return this._MacAddress.CompareTo(((WocketListItem)wi)._MacAddress);
        }

        public WocketListItem(string mac, int index, int width, int height)
        {
            //this.Width = Screen.PrimaryScreen.WorkingArea.Width;
            //this.Height = Screen.PrimaryScreen.WorkingArea.Height / ;
            this.Width = width;
            this.Height = height;
            this.BackColor = bg_color;
            

            _MacAddress = mac;
            this.Index = index;

            Mac = new Label();
            Mac.Text = mac;
            Mac.ForeColor = label_unselected_color;
            Mac.BackColor = label_bg_unselected_color;
            Mac.Font = new Font(FontFamily.GenericSansSerif, 10.0f, FontStyle.Regular);
            Mac.Location = new Point(10, 10); //0,0
            Mac.Size = new Size(width - 20, height - 20); //250, 30
            Mac.SendToBack();

            //checkButton = new CheckBox();
            //checkButton.Size = new Size(48, 48);
            ////checkButton.Visible = true;
            //checkButton.Location = new Point(width - 60, 0);
            ////checkButton.Checked = false;


            this.MouseDown += new MouseEventHandler(WocketListItem_MouseDown);
            //////this.MouseUp += new MouseEventHandler(WocketListItem_MouseUp);


            this.Controls.Add(Mac);
           //// this.Controls.Add(checkButton);


        }

        //commented
        //public WocketListItem(string name, string mac, int index)
        //{
        //    this.Width = Screen.PrimaryScreen.WorkingArea.Width;
        //    this.Height = Screen.PrimaryScreen.WorkingArea.Height / 4;
        //    this.BackColor = bg_color;
            
          
        //    _MacAddress = mac;
        //    _Name = name;

            
        //   // _backBuffer = new Bitmap(this.Width, this.Height);
        //    //gxBuffer.Clear(bg_color);

        //    //Title = new Label();
        //    //Title.Text = index + ". " + name;
        //    //Title.ForeColor = Color.Black;
        //    //Title.Font = new Font(FontFamily.GenericSansSerif, 10.0f, FontStyle.Bold);
        //    //Title.Location = new Point(10, 10);
        //    //Title.Size = new Size(450, 30);
        //    //this.Controls.Add(Title);

        //    Mac = new Label();
        //    Mac.Text = mac;
        //    Mac.ForeColor = Color.DimGray;
        //    Mac.Font = new Font(FontFamily.GenericSansSerif, 8.0f, FontStyle.Regular);
        //    Mac.Location = new Point(10, 40);
        //    Mac.Size = new Size(250, 30);
        //    //Status.Text = "Ready";

        //    //Status = new Label();
        //    //Status.Font = new Font(FontFamily.GenericSansSerif, 8.0f, FontStyle.Bold | FontStyle.Italic);
        //    //Status.Location = new Point(350, 10);
        //    //Status.Size = new Size(150, 30);
        //    //Status.ForeColor = Color.Black;

        //    backBox = new PictureBox();
        //    backBox.Size = new Size(400, 60);
        //    backBox.BackColor = PictureBox_color;
        //    backBox.Location = new Point(50, 75);
        //    backBox.Visible = true;
            


        //    /*commandButton = new AlphaPictureBox();
        //    commandButton.Size = new Size(48, 48);
        //    commandButton.Image = AlphaImage.CreateFromFile(Constants.PATH + "Buttons\\CommandUnpressed.png");
        //    commandButton.Visible = true;
        //    commandButton.Location = new Point(200, 80);*/

        //    //addButton = new PictureBox();
        //    //addButton.Size = new Size(48, 48);
        //    //addButton.Image = Resources.AddUnpressed;
        //    //addButton.Visible = true;
        //    //addButton.Location = new Point(200, 80);


        //    //removeButton = new PictureBox();
        //    //removeButton.Size = new Size(48, 48);
        //    //removeButton.Image = Resources.RemoveUnpressed;
        //    //removeButton.Visible = true;
        //    //removeButton.Location = new Point(400, 80);

        //    checkButton = new CheckBox();
        //    checkButton.Size = new Size(48, 48);
        //    //checkButton.Image = Resources.RemoveUnpressed;
        //    checkButton.Visible = true;
        //    checkButton.Location = new Point(400, 80);
        //    checkButton.Checked = false;


        //    this.MouseDown += new MouseEventHandler(WocketListItem_MouseDown);
        //    //this.MouseUp += new MouseEventHandler(WocketListItem_MouseUp);

            
        //    this.Controls.Add(Mac);
        //    //this.Controls.Add(Status);
        //    //this.Controls.Add(addButton);
        //    //this.Controls.Add(removeButton);
        //    this.Controls.Add(checkButton);


        //}


        #region add hits
        //public bool AddHitTest(int x, int y)
        //{
        //    //if ((x > (addButton.Location.X - 10)) && (x < (addButton.Location.X + addButton.Width + 10)))
        //    //    return true;
        //    //else
        //    //    return false;
        //}


        //public bool AddCheckButton(int x, int y)
        //{
        //    if ((x > (checkButton.Location.X - 10)) && (x < (checkButton.Location.X + checkButton.Width + 10)))
        //        return true;
        //    else
        //        return false;
        //}


        //public bool RemoveHitTest(int x, int y)
        //{
        //    //if ((x > (removeButton.Location.X - 10)) && (x < (removeButton.Location.X + removeButton.Width + 10)))
        //    //    return true;
        //    //else
        //    //    return false;
        //    ////            return removeButton.HitTest(x, y);
        //}



        //void s_SelectedIndexChanging(object sender, System.ComponentModel.CancelEventArgs e)
        //{ }

        #endregion 


        void WocketListItem_MouseUp(object sender, MouseEventArgs e)
        {
            //((WocketSlidingList)this.Parent).WocketSlidingList_MouseUp(sender, e);
        }



        public int LastX = 0;
        public int LastY = 0;
        void WocketListItem_MouseDown(object sender, MouseEventArgs e)
        {
            LastX = e.X;
            LastY = e.Y;
            //((WocketSlidingList)this.Parent).WocketSlidingList_MouseDown(sender, e);

        }


        
        //protected override void OnPaint(PaintEventArgs e)
        //{

        //    base.OnPaint(e);
        //    e.Graphics.DrawLine(borderPen, 0, 0, this.Width, 0);
        //    e.Graphics.DrawLine(borderPen, 0, this.Height - 1, this.Width, this.Height - 1);
        //}

    }
}
