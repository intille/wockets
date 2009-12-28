using System;

using System.Collections.Generic;
using System.Text;
using System.Drawing;
using System.Windows.Forms;
using System.Collections;

namespace WocketsApplication.Controls.Alpha
{
    public class AlphaListBoxItem
    {
        public object Data { get; set; }
        public string TitleColumn1 { get; set; }
        public string TitleColumn2 { get; set; }
        public string DetailsColumn1 { get; set; }
        public string DetailsColumn2 { get; set; }
        public StringAlignment column1Allignment { get; set; }
        public StringAlignment column2Allignment { get; set; }


        public AlphaListBoxItem(string _titleColumn1, string _titleColumn2, object _data, string _detailsColumn1, string _detailsColumn2)
        {
            this.Data = _data;
            this.TitleColumn1 = _titleColumn1;
            this.TitleColumn2 = _titleColumn2;
            this.DetailsColumn1 = _detailsColumn1;
            this.DetailsColumn2 = _detailsColumn2;
            column1Allignment = StringAlignment.Near;
            column2Allignment = StringAlignment.Near;
        }
    }

    public class AlphaListBaseList : AlphaControl
    {
        int itemHeight = -1;
        int selectedIndex = -1;
        public int _currentStartItemIndex;
        List<AlphaListBoxItem> items;

        public AlphaListBaseList()
        {
            this.ParentChanged += new EventHandler(AlphaListBaseList_ParentChanged);

            // Items to draw
            this.items = new List<AlphaListBoxItem>();
        }


        void AlphaListBaseList_ParentChanged(object sender, EventArgs e)
        {
            this.Parent.MouseUp += new MouseEventHandler(Parent_MouseUp);
        }

        void Parent_MouseUp(object sender, MouseEventArgs e)
        {
            if (!this.Visible || !this.Enabled || !HitTest(e.X, e.Y))
                return;
            this.OnMouseUp(e);
        }

        public List<AlphaListBoxItem> Items
        {
            get { return this.items; }
        }

        public event EventHandler SelectedIndexChanged;

        // Raise the SelectedIndexChanged event
        protected virtual void OnSelectedIndexChanged(EventArgs e)
        {
            if (this.SelectedIndexChanged != null)
                this.SelectedIndexChanged(this, e);
        }

        // Get or set index of selected item.
        public int SelectedIndex
        {
            get { return this.selectedIndex; }

            set
            {
                this.selectedIndex = value;
                if (this.SelectedIndexChanged != null)
                    this.SelectedIndexChanged(this, EventArgs.Empty);
            }
        }

        protected void ScrollValueChanged(object o, EventArgs e)
        {
            this.Refresh();
        }

        protected virtual int ItemHeight
        {
            get { return this.itemHeight; }
            set { this.itemHeight = value; }
        }

        // If the requested index is before the first visible index then set the
        // first item to be the requested index. If it is after the last visible
        // index, then set the last visible index to be the requested index.
        public void EnsureVisible(int index)
        {
            if (index < this._currentStartItemIndex)
            {
                this._currentStartItemIndex = index;
            }
            else if (index >= this._currentStartItemIndex + this.DrawCount)
            {
                //this._currentStartItemIndex = index - this.DrawCount + 1;
            }

            this.Refresh();
        }



        // Selected item moves when you use the keyboard up/down keys.
        public new void OnKeyDown(KeyEventArgs e)
        {
            switch (e.KeyCode)
            {
                case Keys.Down:
                    if (this.SelectedIndex < this.Items.Count)
                    {
                        EnsureVisible(++this.SelectedIndex);
                    }
                    break;
                case Keys.Up:
                    if (this.SelectedIndex > 0)
                    {
                        EnsureVisible(--this.SelectedIndex);
                    }
                    break;
            }

            base.OnKeyDown(e);
        }

        // Calculate how many items we can draw given the height of the control.
        protected int DrawCount { get; set; }



        public override void Draw(Graphics gx)
        {

        }
    }
}
