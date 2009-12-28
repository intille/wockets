using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.Drawing;
using System.Drawing.Imaging;
using WocketsApplication.Controls.Alpha;


namespace WocketsApplication.Controls
{
    public class ClickableAlphaPanel: AlphaPanel
    {
        public Bitmap _Background;
        public string _BackgroundFile;
           
        public bool[] _ButtonPressed;
        public AlphaPictureBox[] _PressedButtonControls;
        public AlphaPictureBox[] _UnpressedButtonControls;


        public ClickableAlphaPanel()
        {
        }
        public ClickableAlphaPanel(int NumButtons)
        {
            this._PressedButtonControls = new AlphaPictureBox[NumButtons];
            this._UnpressedButtonControls = new AlphaPictureBox[NumButtons];
            this._ButtonPressed = new bool[NumButtons];
        }

        public void Initialize()
        {
            if ((_Background != null) && (_BackgroundFile != null))
            {
                AlphaPictureBox background = new AlphaPictureBox();
                background.Size = new Size(_Background.Width, _Background.Height);
                background.Image = AlphaImage.CreateFromFile(_BackgroundFile);
                background.Visible = true;
                background.Location = new Point(0, 0);
            }            
            this.Visible = false;
            this.Width = Screen.PrimaryScreen.WorkingArea.Width;
            this.Height = Screen.PrimaryScreen.WorkingArea.Height;
            this.Location = new Point(Screen.PrimaryScreen.WorkingArea.Width + 5, 0); //offscreen

            if (this._UnpressedButtonControls != null)
            {
                for (int i = 0; (i < this._UnpressedButtonControls.Length); i++)
                {
                    this._ButtonPressed[i] = false;
                    this.Controls.Add(this._UnpressedButtonControls[i]); 
                    this.Controls.Add(this._PressedButtonControls[i]);
                }
            }  
        }      
    }
}
