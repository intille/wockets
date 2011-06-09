using System;
using System.Drawing;
using System.Windows.Forms;

namespace WocketsApplication.Controls.Alpha
{
    /// <summary>
    /// Alpha Image Button.
    /// 3 images can be associated: Normal, Pushed and Disabled.
    /// </summary>
    public class AlphaImageButton : WindowsButtonBase
    {
        private AlphaImage _backgroundImage = new AlphaImage();
        private AlphaImage _activeBackgroundImage = new AlphaImage();
        private AlphaImage _disabledBackgroundImage = new AlphaImage();
        private uint _alpha;
        private bool _pushed;
        private bool _hover;
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

        public AlphaImage BackgroundImage
        {
            get { return _backgroundImage; }
            set { _backgroundImage = value; }
        }

        public AlphaImage ActiveBackgroundImage
        {
            get { return _activeBackgroundImage; }
            set { _activeBackgroundImage = value; }
        }

        public AlphaImage DisabledBackgroundImage
        {
            get { return _disabledBackgroundImage; }
            set { _disabledBackgroundImage = value; }
        }

        public uint Alpha
        {
            get { return _alpha; }
            set
            {
                _alpha = value;
                if (_backgroundImage != null)
                    _backgroundImage.Alpha = _alpha;
                if (_activeBackgroundImage != null)
                    _activeBackgroundImage.Alpha = _alpha;
                if (_disabledBackgroundImage != null)
                    _disabledBackgroundImage.Alpha = _alpha;
            }
        }

        public AlphaImageButton()
        {
            // Set some default values
            this.Size = new Size(72, 20);
            this.ForeColor = SystemColors.ControlText;

            this.ParentChanged += new EventHandler(AlphaImageButton_ParentChanged);
            this.EnabledChanged += new EventHandler(AlphaImageButton_EnabledChanged);
        }

        protected override void Dispose(bool disposing)
        {
            if (disposing)
            {
                if (_backgroundImage != null)
                    _backgroundImage.Dispose();
                if (_activeBackgroundImage != null)
                    _activeBackgroundImage.Dispose();
                if (_disabledBackgroundImage != null)
                    _disabledBackgroundImage.Dispose();
            }
            base.Dispose(disposing);
        }

        void AlphaImageButton_ParentChanged(object sender, EventArgs e)
        {
            this.Parent.MouseDown += new MouseEventHandler(Parent_MouseDown);
            this.Parent.MouseUp += new MouseEventHandler(Parent_MouseUp);
            this.Parent.MouseMove += new MouseEventHandler(Parent_MouseMove);
        }

        void AlphaImageButton_EnabledChanged(object sender, EventArgs e)
        {
            Refresh();
        }

        void Parent_MouseDown(object sender, MouseEventArgs e)
        {
            if (!this.Visible || !this.Enabled || !HitTest(e.X, e.Y))
                return;

            _pushed = true;
            _hover = true;

            Refresh();
        }

        void Parent_MouseUp(object sender, MouseEventArgs e)
        {
            if (!this.Visible || !this.Enabled || !_pushed || !HitTest(e.X, e.Y))
                return;

            _pushed = false;
            _hover = false;

            Refresh();

            this.OnClick(null);
        }

        void Parent_MouseMove(object sender, MouseEventArgs e)
        {
            if (!this.Visible || !this.Enabled || !_pushed)
                return;

            bool hit = HitTest(e.X, e.Y);
            if (hit == _hover)
                return;

            _hover = hit;

            Refresh();
        }


        #region AlphaControl Members

        /// <summary>
        /// Draws the button according to its current state.
        /// </summary>
        public override void Draw(Graphics gx)
        {
            // Draw the background image
            AlphaImage image = null;

            if (!Enabled)
                image = _disabledBackgroundImage;
            else if (_pushed && _hover)
                image = _activeBackgroundImage;
            else
                image = _backgroundImage;

            if (image != null)
                image.Draw(gx, this.Bounds, Stretch);

            // Draw the text if any
            if (!String.IsNullOrEmpty(this.Text))
            {
                SizeF stringSize = gx.MeasureString(this.Text, this.Font);
                float stringPosX = this.Bounds.X + ((this.Bounds.Width / 2) - (stringSize.Width / 2));
                float stringPosY = this.Bounds.Y + ((this.Bounds.Height / 2) - (stringSize.Height / 2));
                gx.DrawString(this.Text, this.Font, new SolidBrush(this.ForeColor), stringPosX, stringPosY);
            }
        }

        #endregion

    }
}
