using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Drawing;
using System.Drawing.Imaging;
using System.Windows.Forms;



namespace KernelApp.GUI
{
    
    /// <summary>
    /// Custom image button control
    /// </summary>
    public class ImageButton :Control
    {
        #region Variables

        private Image image, imageActive;
        private bool isActive;

        #endregion

        /// <summary>
        /// 
        /// </summary>
        /// <param name="image">Image for button before pressed.</param>
        /// <param name="imagePressed">Image for button after pressd </param>
        public ImageButton(Bitmap imageActive, Bitmap image)
        {
            isActive = false;

            this.image = (Bitmap)imageActive;
            this.imageActive = (Bitmap)image;

            this.Size = new Size(imageActive.Width, imageActive.Height);
        }

        public void SetIsActive(bool value)
        {
            isActive = value;
        }

        public bool GetIsActive()
        {
            return isActive;
        }

        public void refreshButton()
        {
            this.Invalidate(); // Force the refresh of the UI
        }

        #region Custom Graphics

        /// <summary>
        /// Button Active
        /// </summary>
        /// <param name="e">Button pressed event</param>
        protected override void OnMouseDown(System.Windows.Forms.MouseEventArgs e)
        {
            //if (isActive)
            //    isActive = false;
            //else
            //    isActive = true;

            //this.Invalidate(); // Force the refresh of the UI
            //base.OnMouseDown(e);
        }

        ///// <summary>
        ///// Button released
        //// </summary>
        ///// <param name="e">Button released event </param>
        //protected override void OnMouseUp(System.Windows.Forms.MouseEventArgs e)
        //{
        //    isPressed = false;
        //    this.Invalidate();
        //    base.OnMouseUp(e);
        //}

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

            if (isActive)
            {
                e.Graphics.DrawImage(imageActive, 0, 0);
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
