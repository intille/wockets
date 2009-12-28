using System;
using System.Collections.Generic;
using System.Text;
using System.Drawing;
using System.Windows.Forms;
using System.Data;
using System.Collections;

namespace WocketsApplication.Controls.Alpha
{
    public class AlphaListBox : AlphaListBaseList
    {
        private List<int> _itemHeightList;

        public int Column1Left { get; set; }
        public int Column2Left { get; set; }

        public new Color ForeColor { get; set; }
        public Color SelectedForeColor { get; set; }
        public Color SelectedBackColor { get; set; }
        public Color LineSeperatorColor { get; set; }
        public int TotalHeight { get; set; }
        public int TotalHeighTopHidden { get; set; }
        StringFormat format;

        public AlphaListBox()
        {
            this.MouseUp += new MouseEventHandler(AlphaListBox_MouseUp);
            format = new StringFormat();
        }

        void AlphaListBox_MouseUp(object sender, MouseEventArgs e)
        {
            int runningHeightToltal = 0;
            if (DrawCount < this.Items.Count && this.Bounds.Width - 6 <= e.X)
            {
                int scrollHeight = this.Bounds.Height / TotalHeight * this.Bounds.Height;
                //Clicked above scroll Bar
                if (this.Bounds.Y + this.TotalHeighTopHidden / this.TotalHeight * this.Bounds.Height > e.Y)
                {
                    //if (this.VScrollBar.Value > this.VScrollBar.Minimum)
                    //    this.VScrollBar.Value = this.VScrollBar.Value - 1;
                }
                //else
                else if (this.Bounds.Y + this.TotalHeighTopHidden / this.TotalHeight * this.Bounds.Height + scrollHeight < e.Y)
                {
                    //if (this.VScrollBar.Value < this.VScrollBar.Maximum)
                    //    this.VScrollBar.Value = this.VScrollBar.Value + 1;
                }
                this.Refresh();
            }
            else
            {
                for (int i = _currentStartItemIndex; i < this._itemHeightList.Count; i++)
                {
                    runningHeightToltal += this._itemHeightList[i];
                    if (runningHeightToltal > e.Y - this.Bounds.Y)
                    {
                        this.SelectedIndex = i;
                        break;
                    }
                }
                this.EnsureVisible(this.SelectedIndex);
                this.Refresh();
            }

        }
        public void Initialize()
        {

        }
        public override void Draw(Graphics gOffScreen)
        {
            Font boldFont = new Font(this.Font.Name, 10, FontStyle.Bold);
            // Calc line height to be height of letter A plus 10%
            int fontHeight = (int)(gOffScreen.MeasureString("A", boldFont).Height * 1.1);
            this.ItemHeight = fontHeight;
            int itemTop = this.Bounds.Y;
            int actualItemHeightCol1 = 0;
            int actualItemHeightCol2 = 0;
            int actualItemHeight = 0;
            int runningTotalToSelectedItem = 0;
            this.TotalHeighTopHidden = 0;
            this.TotalHeight = 0;
            _itemHeightList = new List<int>();
            boldFont = new Font(this.Font.Name, 10, FontStyle.Bold);
            Font font = new Font(this.Font.Name, 10, FontStyle.Regular);

            //This For loop calculates - Item Height of the elements
            for (int n = 0; n < this.Items.Count; n++)
            {
                actualItemHeightCol1 = this.ItemHeight;
                actualItemHeightCol2 = this.ItemHeight;
                AlphaListBoxItem lvi = (AlphaListBoxItem)this.Items[n];
                /*Wrap Text if required*/
                int widthOfText = 0;
                int widthofUnit = (int)gOffScreen.MeasureString("A", boldFont).Width;
                int allotedSpace = 0;
                int allowableTextLength;
                //Cloumn 1
                if (!string.IsNullOrEmpty(lvi.TitleColumn1))
                {
                    while (true)
                    {
                        widthOfText = (int)gOffScreen.MeasureString(lvi.TitleColumn1, boldFont).Width;
                        allotedSpace = this.Bounds.Width - Column1Left;
                        if (Column2Left > 0)
                        {
                            allotedSpace = Column2Left - Column1Left;
                        }
                        if (widthOfText > allotedSpace)
                        {
                            allowableTextLength = allotedSpace / widthofUnit;
                        }
                        else
                        {
                            break;
                        }
                        if (allowableTextLength < lvi.TitleColumn1.Length && allowableTextLength > 0)
                        {
                            lvi.TitleColumn1 = lvi.TitleColumn1.Insert((actualItemHeightCol1 / this.ItemHeight) * allowableTextLength - 1, "\n");
                            actualItemHeightCol1 += this.ItemHeight;
                        }
                    }
                }
                if (!string.IsNullOrEmpty(lvi.TitleColumn1))
                {
                    actualItemHeightCol1 = (int)gOffScreen.MeasureString(lvi.TitleColumn1, boldFont).Height;
                }
                //Cloumn 2
                if (!string.IsNullOrEmpty(lvi.TitleColumn2) && Column2Left > 0)
                {
                    while (true)
                    {
                        widthOfText = (int)gOffScreen.MeasureString(lvi.TitleColumn2, boldFont).Width;
                        allotedSpace = this.Bounds.Width - Column2Left;
                        if (widthOfText > allotedSpace)
                        {
                            allowableTextLength = allotedSpace / widthofUnit;
                        }
                        else
                        {
                            break;
                        }
                        if (allowableTextLength < lvi.TitleColumn2.Length && allowableTextLength > 0)
                        {
                            lvi.TitleColumn2.Insert(allowableTextLength - 1, "\n");
                            actualItemHeightCol2 += this.ItemHeight;
                        }
                    }
                }
                if (!string.IsNullOrEmpty(lvi.TitleColumn2) && Column2Left > 0)
                {
                    actualItemHeightCol2 = (int)gOffScreen.MeasureString(lvi.TitleColumn2, boldFont).Height;
                }
                actualItemHeight = actualItemHeightCol2 > actualItemHeightCol1 ? actualItemHeightCol2 : actualItemHeightCol1;
                if (n <= this.SelectedIndex && n >= _currentStartItemIndex)
                {
                    runningTotalToSelectedItem += actualItemHeight;
                }
                TotalHeight += actualItemHeight;

                if (_itemHeightList.Count <= n)
                {
                    _itemHeightList.Add(actualItemHeight);
                }
                else
                {
                    _itemHeightList[n] = actualItemHeight;
                }
            }
            //Calculate Start Element before drawing
            if (runningTotalToSelectedItem > this.Bounds.Height)
            {
                for (int n = _currentStartItemIndex; n <= this.SelectedIndex; n++)
                {
                    runningTotalToSelectedItem = runningTotalToSelectedItem - _itemHeightList[n];
                    _currentStartItemIndex++;
                    if (runningTotalToSelectedItem <= this.Bounds.Height)
                    {
                        break;
                    }
                }
            }
            //calculate space upto First Item
            for (int n = 0; n < _currentStartItemIndex; n++)
            {
                this.TotalHeighTopHidden += _itemHeightList[n];
            }


            // Draw the visible items.
            for (int n = _currentStartItemIndex; n < this.Items.Count; n++)
            {
                AlphaListBoxItem lvi = (AlphaListBoxItem)this.Items[n];
                DrawCount = n - _currentStartItemIndex + 1;
                if (itemTop + _itemHeightList[n] > this.Bounds.Height + this.Bounds.Y)
                {
                    break;
                }
                // Draw the selected item to appear highlighted
                if (n == this.SelectedIndex)
                {
                    gOffScreen.FillRectangle(new SolidBrush(this.SelectedBackColor),
                        this.Bounds.X,
                        itemTop,
                        // If the scroll bar is visible, subtract the scrollbar width
                        // otherwise subtract 2 for the width of the rectangle
                        this.ClientSize.Width - 7,
                        _itemHeightList[n]);
                    //Draw a gray separator for each item
                    gOffScreen.DrawLine(new Pen(this.LineSeperatorColor),
                        this.Bounds.X,
                        itemTop + _itemHeightList[n],
                        this.ClientSize.Width - 7,
                        itemTop + _itemHeightList[n]);

                    //Draw header of List Items
                    if (!string.IsNullOrEmpty(lvi.TitleColumn1))
                    {
                        format.Alignment = lvi.column1Allignment;
                        gOffScreen.DrawString(lvi.TitleColumn1, boldFont, new SolidBrush(this.SelectedForeColor), Column1Left, itemTop, format);
                    }
                    if (!string.IsNullOrEmpty(lvi.TitleColumn2) && Column2Left > 0)
                    {
                        format.Alignment = lvi.column2Allignment;
                        gOffScreen.DrawString(lvi.TitleColumn2, boldFont, new SolidBrush(this.SelectedForeColor), Column2Left, itemTop, format);
                    }
                }
                else
                {
                    //Draw a gray separator for each item
                    gOffScreen.DrawLine(new Pen(this.LineSeperatorColor),
                        1,
                        itemTop + _itemHeightList[n],
                        this.ClientSize.Width - 7,
                        itemTop + _itemHeightList[n]);

                    if (!string.IsNullOrEmpty(lvi.TitleColumn1))
                    {
                        format.Alignment = lvi.column1Allignment;
                        gOffScreen.DrawString(lvi.TitleColumn1, font, new SolidBrush(this.ForeColor), Column1Left, itemTop, format);
                    }
                    if (!string.IsNullOrEmpty(lvi.TitleColumn2) && Column2Left > 0)
                    {
                        format.Alignment = lvi.column2Allignment;
                        gOffScreen.DrawString(lvi.TitleColumn2, font, new SolidBrush(this.ForeColor), Column2Left, itemTop, format);
                    }


                }
                // Set the next item top to move down the item height
                itemTop += _itemHeightList[n];
            }
            //Draw Scroll Bar
            if (DrawCount < this.Items.Count)
            {
                int scrollHeight = (int)(((float)this.Bounds.Height / this.TotalHeight) * (float)this.Bounds.Height);
                gOffScreen.DrawLine(new Pen(this.LineSeperatorColor), this.Bounds.X + this.Bounds.Width - 3, this.Bounds.Y, this.Bounds.X + this.Bounds.Width - 3, this.Bounds.Y + this.Bounds.Height);
                gOffScreen.FillRectangle(new SolidBrush(this.LineSeperatorColor), this.Bounds.X + this.Bounds.Width - 6, this.Bounds.Y + (int)(((float)this.TotalHeighTopHidden / this.TotalHeight) * (float)this.Bounds.Height), 6, scrollHeight);
            }
            boldFont.Dispose();
            font.Dispose();
        }
    }
}
