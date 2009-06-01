using System;
using System.Drawing;
using System.Threading;
using Wockets.Decoders;
using Wockets.Data.Accelerometers;
using Wockets.Sensors.Accelerometers;
using System.Windows.Forms;

namespace Wockets.Data.Plotters
{

    public class WocketsScalablePlotter
    {

        public const int SIGNALS_PER_AXIS = 3;
        private Size plotAreaSize;
        private int[] axisOffset;
        private System.Drawing.Pen[] p;
        private int graphSize;
        private WocketsController wocketsController;
        private System.Windows.Forms.Panel aPanel;

        int[] currentColumns;
        int[][] previousVals;
        double[] previousTimes;
        double[] scaleFactors;

        public WocketsScalablePlotter(System.Windows.Forms.Panel aPanel, WocketsController wocketsController)
        {

            this.wocketsController = wocketsController;
            this.aPanel = aPanel;
            this.plotAreaSize = new Size(this.aPanel.Width, ((int)(this.aPanel.Height * 0.60)));
            graphSize = (int)Math.Floor((plotAreaSize.Height / ((double)this.wocketsController._Sensors.Count)));
  
            scaleFactors = new double[this.wocketsController._Sensors.Count];
            currentColumns = new int[this.wocketsController._Sensors.Count];
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                this.currentColumns[i] = 0;
                double range = ((Accelerometer)this.wocketsController._Sensors[i])._Max - ((Accelerometer)this.wocketsController._Sensors[i])._Min;
                scaleFactors[i] = graphSize / range;
            }
            int dy = (int)Math.Floor(plotAreaSize.Height / ((double)this.wocketsController._Sensors.Count));
            int offset = dy;
            axisOffset = new int[this.wocketsController._Sensors.Count];
            for (int i = 0; i < axisOffset.Length; i++)
            {
                axisOffset[i] = offset;
                offset += dy;
            }


            previousTimes = new double[this.wocketsController._Sensors.Count];
            previousVals = new int[this.wocketsController._Sensors.Count][];
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                previousVals[i] = new int[3];
                for (int j = 0; (j < 3); j++)
                    previousVals[i][j] = 0;
            }

            p = new System.Drawing.Pen[SIGNALS_PER_AXIS];

            p[0] = new Pen(System.Drawing.Color.Orange);
            p[1] = new Pen(System.Drawing.Color.Red);
            p[2] = new Pen(System.Drawing.Color.Blue);
           
        }


        private SolidBrush aBrush = new SolidBrush(Color.White);
        private SolidBrush blueBrush = new SolidBrush(Color.LightBlue);

        private bool requiresFullRedraw = true;
        int lastColumn = 0;
        int firstColumn = 999999;
        public void Draw(Graphics g)
        {

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                int receiverID = this.wocketsController._Sensors[i]._Receiver;

                if (this.wocketsController._Receivers[receiverID]._Running)
                {


                    int decoderID = this.wocketsController._Sensors[i]._Decoder;
                    for (int j = 0; (j < this.wocketsController._Decoders[decoderID]._Size); j++)
                    {
                        AccelerationData data = ((AccelerationData)this.wocketsController._Decoders[decoderID]._Data[j]);

                        //check the data comes from the sensor i if the decoder is used with multiple sensors
                        if (data.SensorID == this.wocketsController._Sensors[i]._ID)
                        {

                            if (this.currentColumns[i] >= this.plotAreaSize.Width - 1)
                                requiresFullRedraw = true;

                            if ((this.wocketsController._Sensors[data.SensorID])._Class == Wockets.Sensors.SensorClasses.HTCDiamondTouch)
                            {
                                g.DrawEllipse(p[0], lastColumn, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.X), 2, 2);
                                g.DrawEllipse(p[1], lastColumn, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Y), 2, 2);
                                g.DrawEllipse(p[2], lastColumn, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Z), 2, 2);
                            }
                            else
                            {
                                g.DrawLine(p[0], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][0]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.X));
                                g.DrawLine(p[1], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][1]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Y));
                                g.DrawLine(p[2], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][2]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Z));
                                if (this.currentColumns[i] > lastColumn)
                                    lastColumn = this.currentColumns[i];

                            }

                            previousVals[i][0] = data.X;
                            previousVals[i][1] = data.Y;
                            previousVals[i][2] = data.Z;
                            previousTimes[i] = data.UnixTimeStamp;

                            this.currentColumns[i] = this.currentColumns[i] + 1;





                        }

                    }
                }

            }

            //check if the columns are in sync within 30 points

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                for (int j = i + 1; (j < this.wocketsController._Sensors.Count); j++)
                {
                    int size1 = this.wocketsController._Decoders[this.wocketsController._Sensors[i]._Decoder]._Size;
                    int size2 = this.wocketsController._Decoders[this.wocketsController._Sensors[j]._Decoder]._Size;
                    if ((size1 > 1) && (size2 > 1) && (Math.Abs(this.currentColumns[i] - this.currentColumns[j]) > 60))
                    {
                        requiresFullRedraw = true;
                        break;
                    }
                }
            }

            if (requiresFullRedraw)
            {
                this.aPanel.Width = this.aPanel.Width;
                
                g.FillRectangle(blueBrush, 0, 0, this.plotAreaSize.Width + 10, this.plotAreaSize.Height);
                lastColumn = 0;
                firstColumn = 0;
                for (int k = 0; (k < this.wocketsController._Sensors.Count); k++)
                    this.currentColumns[k] = 0;
                aPanel.Invalidate();
                requiresFullRedraw = false;
            }
            else
                aPanel.Invalidate(new System.Drawing.Rectangle(firstColumn, 0, lastColumn-firstColumn, plotAreaSize.Height));

            firstColumn = lastColumn;

        }

    }
}
