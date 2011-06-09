//using System;
//using System.Linq;
//using System.Collections.Generic;
//using System.Text;

using System;
using System.Drawing;
using System.Windows.Forms;


namespace CollectDataUser
{


    // This class is a simple button-like control that has a background image.
    public class CustomImageButton: Control
    {
        Image   backgroundImage, pressedImage;
        public  bool pressed = false;
        private bool is_active = true;
        public  string text_aligment = "center";
        public  string SENSOR_LOCATION = "";
        public  int ID = -1;


        private Font control_font = new Font(FontFamily.GenericMonospace, (float)10.0, FontStyle.Bold);

        // Property for the background image to be drawn behind the button text.
        public Image BackgroundImage
        {
            get
            {
                return this.backgroundImage;
            }
            set
            {
                this.backgroundImage = value;
            }
        }

        // Property for the background image to be drawn behind the button text when the button is pressed.
        public Image PressedImage
        {
            get
            {
                return this.pressedImage;
            }
            set
            {
                this.pressedImage = value;
            }
        }

        public void SetButtonActive(bool value)
        {
            is_active = value;
        }

        public bool IsButtonActive()
        {
            return is_active;
        }


        // When the mouse button is pressed, set the "pressed" flag to true 
        // and invalidate the form to cause a repaint.  The .NET Compact Framework 
        // sets the mouse capture automatically.
        protected override void OnMouseDown(MouseEventArgs e)
        {
            if (is_active)
            {
                if (!this.pressed)
                    this.pressed = true;
                else
                    this.pressed = false;

                this.Invalidate();
                base.OnMouseDown(e);
            }
        }

        #region commneted
        // When the mouse is released, reset the "pressed" flag 
        // and invalidate to redraw the button in the unpressed state.
        //protected override void OnMouseUp(MouseEventArgs e)
        //{
        //    //this.pressed = false;
        //    this.Invalidate();
        //    base.OnMouseUp(e);
        //}
        #endregion 


        //public void SetButtonPressed(bool is_pressed)
        //{
        //    this.pressed = is_pressed;
        //    this.Invalidate();
        //}


        // Override the OnPaint method to draw the background image and the text.
        protected override void OnPaint(PaintEventArgs e)
        {

            if (this.pressed && this.pressedImage != null)
                e.Graphics.DrawImage(this.pressedImage, 0, 0);
            else
                e.Graphics.DrawImage(this.backgroundImage, 0, 0);


            // Draw the text if there is any
            if (this.Text.Length > 0 )
            {
                this.Font = control_font;
                SizeF size = e.Graphics.MeasureString(this.Text, this.Font);
                float aligment_x = 0;  
                float aligment_y = 0;  
               

                if( this.text_aligment.Contains("right"))
                {   aligment_x = 1;
                    aligment_y = this.ClientSize.Height- size.Height;
                }
                else if (this.text_aligment.Contains("left"))
                {
                    aligment_x = this.ClientSize.Width - size.Width - 1;
                    aligment_y = this.ClientSize.Height - size.Height;
                }
                else
                {
                    aligment_x = (this.ClientSize.Width - size.Width) / 2;
                    aligment_y = (this.ClientSize.Height - size.Height) / 2;
                }

                
                // Draw the text inside the client area of the PictureButton.
                e.Graphics.DrawString(this.Text, this.Font, new SolidBrush(this.ForeColor),aligment_x, aligment_y);
            }


            // Draw a border around the outside of the 
            // control to look like Pocket PC buttons.
            //-- e.Graphics.DrawRectangle(new Pen(Color.Green), 0, 0,
            //--    this.ClientSize.Width - 1, this.ClientSize.Height - 1);

            base.OnPaint(e);
        }


    }


}
