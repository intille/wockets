using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Drawing;
using System.Drawing.Imaging;
using System.Windows.Forms;


namespace KernelApp.GUI
{
    class ImageButtonClick:Control
    {
         #region Variables

        private Image image, imagePressed;
        private bool isPressed;

        #endregion

        /// <summary>
        /// 
        /// </summary>
        /// <param name="image">Image for button before pressed.</param>
        /// <param name="imagePressed">Image for button after pressd </param>
        public ImageButtonClick(Bitmap image, Bitmap imagePressed)
        {
            isPressed = false;

            this.image = (Bitmap)image;
            this.imagePressed = (Bitmap)imagePressed;

            this.Size = new Size(image.Width, image.Height);
        }

        #region Custom Graphics

        /// <summary>
        /// Button pressed
        /// </summary>
        /// <param name="e">Button pressed event</param>
        protected override void OnMouseDown(System.Windows.Forms.MouseEventArgs e)
        {
            isPressed = true;
            this.Invalidate(); // Force the refresh of the UI
            base.OnMouseDown(e);
        }

        /// <summary>
        /// Button released
        /// </summary>
        /// <param name="e">Button released event </param>
        protected override void OnMouseUp(System.Windows.Forms.MouseEventArgs e)
        {
            isPressed = false;
            this.Invalidate();
            base.OnMouseUp(e);
        }

        /// <summary>
        ///  Do nothing, in order to avoid flickering
        /// </summary>
        /// <param name="e">Event</param>
        protected override void OnPaintBackground(PaintEventArgs e)
        {
            //Do nothing, in order to avoid flickering
        }

        /// <summary>
        /// Paint label on button
        /// </summary>
        /// <param name="e">Event</param>
        protected override void OnPaint(System.Windows.Forms.PaintEventArgs e)
        {

            if (isPressed)
            {
                e.Graphics.DrawImage(imagePressed, 0, 0);
                e.Graphics.DrawString(this.Text, new Font("Arial", 12, FontStyle.Bold), new SolidBrush(Color.White),
                                                 new RectangleF(10, 13, this.Width, this.Height));
            }
            else
            {
                e.Graphics.DrawImage(image, 0, 0);
                e.Graphics.DrawString(this.Text, new Font("Arial", 12, FontStyle.Bold), new SolidBrush(Color.White),
                                                 new RectangleF(10, 10, this.Width, this.Height));
            }
        }

        #endregion


    }
}
