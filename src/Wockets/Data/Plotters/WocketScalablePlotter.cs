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
        int[] plotFrom;
        int[] lastColumn;
        int[] firstColumn;
        int[] decoderTails;
        double[] lastUnixTimestamps;
        int skippedPoints = 0;

        public WocketsScalablePlotter(System.Windows.Forms.Panel aPanel, WocketsController wocketsController)
        {

            this.wocketsController = wocketsController;
            if (this.wocketsController._Sensors.Count > 3)
                skippedPoints = 3;
            else if (this.wocketsController._Sensors.Count > 1)
                skippedPoints = 2;
            
            this.aPanel = aPanel;
            this.plotAreaSize = new Size(this.aPanel.Width, ((int)(this.aPanel.Height * 0.60)));
            graphSize = (int)Math.Floor((plotAreaSize.Height / ((double)this.wocketsController._Sensors.Count)));
  
            scaleFactors = new double[this.wocketsController._Sensors.Count];
            currentColumns = new int[this.wocketsController._Sensors.Count];
            plotFrom = new int[this.wocketsController._Sensors.Count];
            firstColumn= new int[this.wocketsController._Sensors.Count];
            lastColumn = new int[this.wocketsController._Sensors.Count];
            decoderTails = new int[this.wocketsController._Sensors.Count];
            lastUnixTimestamps = new double[this.wocketsController._Sensors.Count];

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                this.currentColumns[i] = 0;
                this.plotFrom[i] = 0;
                this.firstColumn[i] = 999999;
                this.lastColumn[i] = 0;
                this.decoderTails[i] = 0;
                this.lastUnixTimestamps[i] = 0;
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

        public int[] PlotFrom
        {
            get
            {
                return this.plotFrom;
            }
            set
            {
                this.plotFrom = value;
            }
        }
        public void Draw(Graphics g)
        {
            int lastColumnDrawn = 0;
            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                int receiverID = this.wocketsController._Sensors[i]._Receiver;

                if (this.wocketsController._Receivers[receiverID]._Running)
                {
                    int currentHead = this.wocketsController._Sensors[i]._Decoder._Head;

                    //int decoderID = this.wocketsController._Sensors[i]._Decoder._ID;
                    //for (int j = this.plotFrom[decoderID]; (j < this.wocketsController._Decoders[decoderID]._Size); j++)
                    int tail = this.decoderTails[i];
                    //while(tail<=this.wocketsController._Sensors[i]._Decoder._Head)
                    AccelerationData data = ((AccelerationData)this.wocketsController._Sensors[i]._Decoder._Data[tail]);
                    while ((tail != currentHead) && (data.UnixTimeStamp > 0) && (data.UnixTimeStamp >= this.lastUnixTimestamps[i]))
                    {

                        if (skippedPoints > 0)
                        {
                            if ((tail % skippedPoints) != 0)
                            {
                                if (tail >= (this.wocketsController._Sensors[i]._Decoder._Data.Length - 1))
                                    tail = 0;
                                else
                                    tail++;
                                continue;
                            }
                        }

                        //check the data comes from the sensor i if the decoder is used with multiple sensors
                        if (data.SensorID == this.wocketsController._Sensors[i]._ID)
                        {
                            if (this.currentColumns[i] > lastColumnDrawn)
                                lastColumnDrawn = this.currentColumns[i];

                            if (this.currentColumns[i] >= this.plotAreaSize.Width - 1)
                            {
                                requiresFullRedraw = true;
                                this.currentColumns[i] = 0;
                            }

                            if ((this.wocketsController._Sensors[data.SensorID])._Class == Wockets.Sensors.SensorClasses.HTCDiamondTouch)
                            {
                                if (this.wocketsController._Sensors.Count != 1)
                                {

                                    g.DrawEllipse(p[0], lastColumnDrawn, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.X), 2, 2);
                                    g.DrawEllipse(p[1], lastColumnDrawn, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Y), 2, 2);
                                    g.DrawEllipse(p[2], lastColumnDrawn, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Z), 2, 2);
                                }
                                else
                                {
                                    g.DrawLine(p[0], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][0]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.X));
                                    g.DrawLine(p[1], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][1]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Y));
                                    g.DrawLine(p[2], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][2]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Z));
                                }
                                if (this.currentColumns[i] > lastColumn[data.SensorID])
                                    lastColumn[data.SensorID] = this.currentColumns[i];
                            }

                            else
                            {
                                g.DrawLine(p[0], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][0]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.X));
                                g.DrawLine(p[1], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][1]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Y));
                                g.DrawLine(p[2], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][2]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Z));

                                if (this.currentColumns[i] > lastColumn[data.SensorID])
                                    lastColumn[data.SensorID] = this.currentColumns[i];

                            }

                            previousVals[i][0] = data.X;
                            previousVals[i][1] = data.Y;
                            previousVals[i][2] = data.Z;
                            previousTimes[i] = data.UnixTimeStamp;

                            this.currentColumns[i] = this.currentColumns[i] + 1;

                        }


                        this.lastUnixTimestamps[i] = data.UnixTimeStamp;
                        if (tail >= (this.wocketsController._Sensors[i]._Decoder._Data.Length-1))
                            tail = 0;
                        else
                            tail++;
                        data = ((AccelerationData)this.wocketsController._Sensors[i]._Decoder._Data[tail]);
                    }
                    this.decoderTails[i] = tail;
                }

            }


            if (requiresFullRedraw)
            {
                this.aPanel.Width = this.aPanel.Width;
                
                g.FillRectangle(blueBrush, 0, 0, this.plotAreaSize.Width + 10, this.plotAreaSize.Height);


                for (int k = 0; (k < this.wocketsController._Sensors.Count); k++)
                {
                    this.currentColumns[k] = 0;
                    lastColumn[k] = 0;
                    firstColumn[k] = 999999;
                }
                aPanel.Invalidate();
                requiresFullRedraw = false;
            }
            else
                for (int k = 0; (k < this.wocketsController._Sensors.Count); k++)
                {
                    aPanel.Invalidate(new System.Drawing.Rectangle(firstColumn[k], 0, lastColumn[k] - firstColumn[k], plotAreaSize.Height));
                    firstColumn[k] = lastColumn[k];
                }

        }

    }
}
