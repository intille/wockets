using System;
using System.Linq;
using System.Collections.Generic;
using System.Windows.Forms;
using System.Drawing;
using System.Text;

namespace WocketsApplication.Controls
{
    public class WocketSlidingList: UserControl
    {
        private int location = 0;
        public string _Status = "No Wockets Found...";
        private Brush blackBrush = new SolidBrush(Color.Black);

        public WocketSlidingList()
        {           
           // this.MouseDown += new MouseEventHandler(WocketSlidingList_MouseDown);
            //this.MouseUp += new MouseEventHandler(WocketSlidingList_MouseUp);
        }

        public int _Location
        {
            get
            {
                return this.location;
            }

            set
            {
                this.location = value;
            }
        }
        public void MoveUp()
        {
            if (location != (this.Controls.Count-4))
            {
                for (int i = 0; (i < 5); i++)
                    this.Controls[location + i].Location = new Point(this.Location.X, this.Controls[location + i].Height * (i-1));                
                location++;
            }
            this.Refresh();

        }

        public void MoveDown()
        {
            if (location != 0)
            {
                for (int i = 0; (i < 5); i++)                
                    this.Controls[location + i - 1].Location = new Point(this.Location.X, this.Controls[location + i - 1].Height * i);                
                location--;
            }
            this.Refresh();
}
        private void slideList()
        {
            if (this.currentTransition == Transitions.DOWN_TO_UP)
            {
                for (int i = 0; (i < 5); i++)
                {
                    this.Location = new Point(this.Location.X, this.Location.Y - 60);
                    
                }
            }
            else if (this.currentTransition == Transitions.UP_TO_DOWN)
            {
                for (int i = 0; (i < 5); i++)
                {
                    this.Location = new Point(this.Location.X, this.Location.Y + 60);                    
                }
            }
            this.Update();
        }


        private Bitmap _backBuffer;



        protected override void OnPaint(PaintEventArgs e)
        {

            if (_backBuffer == null)
            {

                _backBuffer = new Bitmap(this.ClientSize.Width, this.ClientSize.Height);

            }

            Graphics g = Graphics.FromImage(_backBuffer);
            g.Clear(Color.FromArgb(245, 219, 186));
            g.DrawString(_Status,new Font( FontFamily.GenericSansSerif,14.0f,FontStyle.Regular),blackBrush,10,this.ClientSize.Height/2);

            //Paint your graphics on g here



            g.Dispose();



            //Copy the back buffer to the screen



            e.Graphics.DrawImage(_backBuffer, 0, 0);

            //base.OnPaint (e); //optional but not recommended

        }



        protected override void OnPaintBackground(PaintEventArgs pevent)
        {
            //Don't allow the background to paint

        }

        public void WocketSlidingList_MouseUp(object sender, MouseEventArgs e)
        {
            if (sender is WocketListItem)
            {
                WocketListItem wi = (WocketListItem)sender;
                int y = e.Y + wi.Height * wi.Index;

                if ((pushed) && (clientArea.Contains(e.X, y)))
                    slideList();
            }
            this.pushed = false;
        }

   

        private Rectangle clientArea;
        public bool pushed = false;
        private Transitions currentTransition;

        public void WocketSlidingList_MouseDown(object sender, MouseEventArgs e)
        {
            if (sender is WocketListItem)
            {
                WocketListItem wi = (WocketListItem)sender;
                int y = e.Y + wi.Height * wi.Index;
                if (!pushed)
                {
                    if (y < (Screen.PrimaryScreen.WorkingArea.Height / 3))
                    {
                        this.currentTransition = Transitions.UP_TO_DOWN;
                        this.pushed = true;
                        this.clientArea = new Rectangle(e.X - (Screen.PrimaryScreen.WorkingArea.Width / 5), Screen.PrimaryScreen.WorkingArea.Height / 2, (Screen.PrimaryScreen.WorkingArea.Width / 5) * 2, Screen.PrimaryScreen.WorkingArea.Height);
                    }
                    else if (y > (Screen.PrimaryScreen.WorkingArea.Height * (2 / 3)))
                    {
                        this.currentTransition = Transitions.DOWN_TO_UP;
                        this.pushed = true;
                        this.clientArea = new Rectangle(e.X - (Screen.PrimaryScreen.WorkingArea.Width / 5), 0, (Screen.PrimaryScreen.WorkingArea.Width / 5) * 2, Screen.PrimaryScreen.WorkingArea.Height / 2);
                    }
                }
            }
        }

    }
}
