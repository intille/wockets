using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;
using System.Drawing;
using System.Threading;

namespace KernelApp.GUI
{
    class PlottingPanel:Panel
    {
        //for double buffering.
        private Graphics gxOff; //Offscreen graphics
        private Bitmap m_bmpOffscreen = null;
        private Pen panelPen;
        private Color pen_color;
        private int pen_size = 2;

       
        //data array
        public int historyCount = 0;
        public List<int> shortHistoryData;
        


        public PlottingPanel(int width, int height, Color pcolor, Color pen_color, int pen_size)
        {
            
            this.Size = new Size(width, height);
            this.BackColor = pcolor;
            this.Location = new Point(0, 0);
            this.Visible = true;

            this.pen_color = pen_color;
            this.pen_size = pen_size;
            this.panelPen = new Pen(this.pen_color, this.pen_size);


            historyCount = width;
            shortHistoryData = new List<int>(historyCount);

            
            //Graphics
            if (m_bmpOffscreen == null) //Bitmap for doublebuffering
            {
                m_bmpOffscreen = new Bitmap(this.Size.Width, this.Size.Height);
            }
            gxOff = Graphics.FromImage(m_bmpOffscreen);


        }

        
     
        int MAX_AC = 500;

        protected override void OnPaint(PaintEventArgs e)
        {
            // code to paint plot
            gxOff.Clear(this.BackColor);

            double raw_act= 0;
            double actp = 0;
            int act = 0;

            for (int i = (shortHistoryData.Count - 1); i >= 0; i--)
            {
                raw_act =shortHistoryData[shortHistoryData.Count - 1 - i] / 60;
                actp = raw_act/MAX_AC;
                act = (int)Math.Floor(actp * this.Height);

                gxOff.DrawLine(panelPen, 
                               historyCount - i, this.Height, 
                               historyCount - i, 
                               this.Height - act);
            }
           
            e.Graphics.DrawImage(m_bmpOffscreen, 0, 0, 
                                new Rectangle(0, 0, this.Size.Width, 
                              this.Size.Height), GraphicsUnit.Pixel);
        }


        protected override void OnPaintBackground(PaintEventArgs e)
        {
            //do nothing to avoid flickering
        }

       

        public void updateData(int newdata)
        {   
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
            private PlottingPanel pPanel;
            private int histCount;
            
            // in declaration
            private delegate void RefreshPlotDelegate();


            public DataToAdd(int[] newData, List<int> showDataHistory, int historyCount, PlottingPanel plottingPanel)
            {
                this.newData = newData;
                this.showDataHistory = showDataHistory;
                this.pPanel = plottingPanel;
                this.histCount = historyCount;
            }

            // in internal class
            private void refreshPlot()
            {
                pPanel.Invalidate();
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
                    pPanel.BeginInvoke(new RefreshPlotDelegate(refreshPlot));

                    //pPanel.Invalidate();
                    Thread.Sleep(20);

                }
            }
        }





    }
}
