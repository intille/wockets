using System;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.Drawing;


namespace WocketsApplication.Controls.Alpha
{
    public class WindowsButtonBase : Control
    {
        private int _width = 10;
        private int _height = 10;


        /// <summary>
        /// Show or Hide this Control.
        /// Note: Don't use the Control.Visible property...
        /// </summary>
        public new int Width
        {
            get { return _width; }
            set
            {
                if (_width == value)
                    return;
                _width = value;
                Refresh();
            }
        }

        public new int Height
        {
            get { return _height; }
            set
            {
                if (_height == value)
                    return;
                _height = value;
                Refresh();
            }
        }

        /// <summary>
        /// When the Text property is updated the Control is refreshed.
        /// </summary>
        public override string Text
        {
            get { return base.Text; }
            set
            {
                if (base.Text == value)
                    return;
                base.Text = value;
                Refresh();
            }
        }


        /// <summary>
        /// Default constructor.
        /// </summary>
        public WindowsButtonBase()
        {
            base.Width = 0;
            base.Height = 0;
        }


        /// <summary>
        /// Overrides Control.Refresh() to forward to action to the 
        /// parent control, which is responsible to handle the drawing process.
        /// </summary>
        public override void Refresh()
        {
            if (this.Parent != null)
                this.Parent.Invalidate(this.Bounds);
        }

        /// <summary>
        /// Checks if the given coordinates are contained by this control.
        /// </summary>
        public bool HitTest(int x, int y)
        {
            return this.Bounds.Contains(x, y);
        }


        /// <summary>
        /// Overrides Control.Resize() to force a custom Refresh.
        /// </summary>
        protected override void OnResize(EventArgs e)
        {
            base.OnResize(e);
            Refresh();
        }


        /// <summary>
        /// Internal Draw method, called by the container.
        /// Will call the actual Draw method if the control is visible.
        /// </summary>
        internal void DrawInternal(Graphics gx)
        {
            if (_width > 0 && _height > 0)
                Draw(gx);
        }

        /// <summary>
        /// Must be overridden.
        /// </summary>
        public virtual void Draw(Graphics gx)
        {
        }
    }
}
