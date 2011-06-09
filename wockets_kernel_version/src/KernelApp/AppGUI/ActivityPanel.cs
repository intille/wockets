using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.Drawing;
using System.Threading;



namespace WocketsApp
{
    class ActivityPanel : Panel
    {

        //for double buffering.
        private Graphics gxOff; //Offscreen graphics
        private Bitmap m_bmpOffscreen = null;

        //data array
        private int historyCount = 0;
        private List<int> shortHistoryData;
        private Dictionary<int, Pen> ActivityColorCode = new Dictionary<int, Pen>();

        //Activity class information
        private int MAX_NUM_ACTIVITIES = 6;
        private int PEN_WIDTH = 5;


        public ActivityPanel(int width, int height, Color bgcolor,
                             int mActivities, int penWidth)
        {

            this.Size = new Size(width, height);
            this.BackColor = bgcolor;
            this.Location = new Point(0, 0);
            this.Visible = true;

            this.MAX_NUM_ACTIVITIES = mActivities;
            this.PEN_WIDTH = penWidth;

            historyCount = width;
            shortHistoryData = new List<int>(historyCount);

            for (int i = 0; i < shortHistoryData.Capacity; i++)
            {
                shortHistoryData.Add(i % MAX_NUM_ACTIVITIES);
            }


            //Graphics
            if (m_bmpOffscreen == null) //Bitmap for doublebuffering
            {
                m_bmpOffscreen = new Bitmap(this.Size.Width, this.Size.Height);
            }
            gxOff = Graphics.FromImage(m_bmpOffscreen);


            //Color code
            ActivityColorCode.Add(0, new Pen(Color.Violet, PEN_WIDTH));
            ActivityColorCode.Add(1, new Pen(Color.Blue, PEN_WIDTH));
            ActivityColorCode.Add(2, new Pen(Color.YellowGreen, PEN_WIDTH));
            ActivityColorCode.Add(3, new Pen(Color.Green, PEN_WIDTH));
            ActivityColorCode.Add(4, new Pen(Color.White, PEN_WIDTH));
            ActivityColorCode.Add(5, new Pen(Color.Red, PEN_WIDTH));

        }




        protected override void OnPaint(PaintEventArgs e)
        {
            // code to paint plot
            gxOff.Clear(this.BackColor);

            //specify color and width of line to draw rectangle
            //Pen pen = new Pen(Color.Green, 2);
            int act = 0;

            for (int i = (shortHistoryData.Count - 1); i >= 0; i--)
            {
                act = shortHistoryData[shortHistoryData.Count - 1 - i];
                gxOff.DrawLine(ActivityColorCode[act], historyCount - i, this.Height - 10, historyCount - i, 5); // shortHistoryData[shortHistoryData.Count - 1 - i]);
            }

            e.Graphics.DrawImage(m_bmpOffscreen, 0, 0, new Rectangle(0, 0, this.Size.Width, this.Size.Height), GraphicsUnit.Pixel);
        }


        protected override void OnPaintBackground(PaintEventArgs e)
        {

        }



        public void updateData(int newdata)
        {   // same as update wallpaper
            // where Fahd calls
            // updates showHistoryData;


            if (shortHistoryData.Count == historyCount)
            {
                shortHistoryData.RemoveAt(0);
            }

            shortHistoryData.Add(newdata);

            this.Invalidate();
        }


        public void updateData(int[] newData)
        {
            DataToAdd batchData = new DataToAdd(newData, shortHistoryData, historyCount, this);
            Thread addBatchDataThread = new Thread(batchData.startAdding);
            addBatchDataThread.Start();
        }


        // class for adding data animation
        internal class DataToAdd
        {
            private int[] newData;
            private List<int> showDataHistory;
            private ActivityPanel aPanel;
            private int histCount;

            // in declaration
            private delegate void RefreshPlotDelegate();


            public DataToAdd(int[] newData, List<int> showDataHistory, int historyCount, ActivityPanel ActPanel)
            {
                this.newData = newData;
                this.showDataHistory = showDataHistory;
                this.aPanel = ActPanel;
                this.histCount = historyCount;
            }

            // in internal class
            private void refreshPlot()
            {
                aPanel.Invalidate();
            }


            internal void startAdding()
            {
                for (int i = 0; i < newData.Length; i++)
                {

                    if (showDataHistory.Count == histCount)
                    {
                        showDataHistory.Remove(0);
                    }

                    showDataHistory.Add(newData[i]);

                    // at where you want to call it. 
                    aPanel.BeginInvoke(new RefreshPlotDelegate(refreshPlot));

                    //pPanel.Invalidate();
                    Thread.Sleep(200);

                }
            }
        }


    }
}
