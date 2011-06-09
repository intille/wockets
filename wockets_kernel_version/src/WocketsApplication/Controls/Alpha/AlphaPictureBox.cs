using System.Drawing;

namespace WocketsApplication.Controls.Alpha
{
    /// <summary>
    /// Simple PictureBox control handling alpha channel.
    /// </summary>
    public class AlphaPictureBox : AlphaControl
    {
        private AlphaImage _image;
        private uint _alpha = 0;

        private bool _stretch;

        public bool Stretch
        {
            get
            {
                return this._stretch;
            }
            set
            {
                this._stretch = value;
            }
        }


        public AlphaPictureBox()
        {
            this.ParentChanged += new System.EventHandler(AlphaPictureBox_ParentChanged);
        }

        void AlphaPictureBox_ParentChanged(object sender, System.EventArgs e)
        {
            this.Parent.MouseUp += new System.Windows.Forms.MouseEventHandler(Parent_MouseUp);
        }

        void Parent_MouseUp(object sender, System.Windows.Forms.MouseEventArgs e)
        {
            if (!this.Visible || !this.Enabled || !HitTest(e.X, e.Y))
                return;
            this.OnClick(null);
        }

        /// <summary>
        /// The image to draw.
        /// </summary>
        public AlphaImage Image
        {
            get { return _image; }
            set
            {                
                _image = value;
                if (_image != null)
                    _image.Alpha = _alpha;
            }
        }

        /// <summary>
        /// The Alpha channel for the image.
        /// </summary>
        public uint Alpha
        {
            get { return _alpha; }
            set
            {
                _alpha = value;
                if (_image != null)
                    _image.Alpha = _alpha;
            }
        }

        /// <summary>
        /// Cleaning.
        /// </summary>
        protected override void Dispose(bool disposing)
        {
            if (disposing)
            {
                if (_image != null)
                    _image.Dispose();
            }
            base.Dispose(disposing);
        }

        #region AlphaControl Members

        /// <summary>
        /// Draws the image if any.
        /// </summary>
        /// <param name="gx"></param>
        public override void Draw(Graphics gx)
        {
            if (_alpha==255)
                gx.Clear(this.BackColor);
            if (_image != null)                           
                _image.Draw(gx, this.Bounds, Stretch);            
        }

        #endregion
    }
}
