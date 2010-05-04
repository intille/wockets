using System;
using System.Drawing;
using System.Threading;
using Wockets.Decoders;
using Wockets.Data.Accelerometers;
using Wockets.Sensors.Accelerometers;
using System.Windows.Forms;
#if (PocketPC)
using Wockets.Utils.IPC.MMF;
#endif

namespace Wockets.Data.Plotters
{
    public enum PlottingMode
    {
        Normal,
        Delayed
    }

    public class WocketsScalablePlotter
    {

        public const int SIGNALS_PER_AXIS = 3;
        private Size plotAreaSize;
        private int[] axisOffset;
        private System.Drawing.Pen[] p;
        private int graphSize;
        private WocketsController wocketsController = null;
        private System.Windows.Forms.Panel aPanel;

        int[] currentColumns;
        int[][] previousVals;
        double[] previousTimes;
        double[] scaleFactors;
        int[] lastColumn;
        int[] firstColumn;
        int[] decoderTails;
        double[] lastUnixTimestamps;
        int[] pointsToPlot;
        int skippedPoints = 0;
        private PlottingMode mode;

#if(PocketPC)
        private MemoryMappedFileStream[] sdata = null;
        private MemoryMappedFileStream[] shead = null;
        private int sdataSize = 0;
        private int numSensors = 0;


        public WocketsScalablePlotter(System.Windows.Forms.Panel aPanel)//, int numSensors)
        {
            this.numSensors = CurrentWockets._Controller._Sensors.Count;// numSensors;

            if (numSensors > 3)
                skippedPoints = 3;
            else if (numSensors > 1)
                skippedPoints = 2;

            this.aPanel = aPanel;
            this.plotAreaSize = new Size(this.aPanel.Width, ((int)(0.60* this.aPanel.Height )));
            graphSize = (int)Math.Floor((plotAreaSize.Height / ((double)numSensors)));



            scaleFactors = new double[numSensors];
            currentColumns = new int[numSensors];
            firstColumn = new int[numSensors];
            lastColumn = new int[numSensors];
            decoderTails = new int[numSensors];
            lastUnixTimestamps = new double[numSensors];
            this.pointsToPlot = new int[numSensors];
            this.mode = PlottingMode.Normal;

            for (int i = 0; (i < numSensors); i++)
            {
                this.currentColumns[i] = this.plotAreaSize.Width - 1;
                this.firstColumn[i] = 999999;
                this.lastColumn[i] = this.plotAreaSize.Width - 1;
                this.decoderTails[i] = 0;
                this.lastUnixTimestamps[i] = 0;
                this.pointsToPlot[i] = 0;
                double range = 1024;//((Accelerometer)this.wocketsController._Sensors[i])._Max - ((Accelerometer)this.wocketsController._Sensors[i])._Min;
                scaleFactors[i] = graphSize / range;
            }
            
#if (PocketPC)
            if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
            {
                sdata = new MemoryMappedFileStream[numSensors];
                shead = new MemoryMappedFileStream[numSensors];
                this.sdataSize = (int)Decoder._DUSize * Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE;
                for (int i = 0; (i < numSensors); i++)
                {
                    sdata[i] = new MemoryMappedFileStream("\\Temp\\wocket" + i + ".dat", "wocket" + i, (uint)this.sdataSize, MemoryProtection.PageReadWrite);
                    shead[i] = new MemoryMappedFileStream("\\Temp\\whead" + i + ".dat", "whead" + i, sizeof(int), MemoryProtection.PageReadWrite);

                    sdata[i].MapViewToProcessMemory(0, this.sdataSize);
                    shead[i].MapViewToProcessMemory(0, sizeof(int));

                    shead[i].Read(head, 0, 4);
                    int currentHead = BitConverter.ToInt32(head, 0);
                    this.decoderTails[i] = currentHead;
                    shead[i].Seek(0, System.IO.SeekOrigin.Begin);
                    sdata[i].Seek((currentHead * (sizeof(double) + 3 * sizeof(short))), System.IO.SeekOrigin.Begin);

                }
            }
#endif
            int dy = (int)Math.Floor(plotAreaSize.Height / ((double)numSensors));
            int offset = dy;
            axisOffset = new int[numSensors];
            for (int i = 0; i < axisOffset.Length; i++)
            {
                axisOffset[i] = offset;
                offset += dy;
            }


            previousTimes = new double[numSensors];
            previousVals = new int[numSensors][];
            for (int i = 0; (i < numSensors); i++)
            {
                previousVals[i] = new int[3];
                for (int j = 0; (j < 3); j++)
                    previousVals[i][j] = 0;
            }


            p = new System.Drawing.Pen[SIGNALS_PER_AXIS];

            p[0] = new Pen(System.Drawing.Color.Orange);
            p[1] = new Pen(System.Drawing.Color.Red);
            p[2] = new Pen(System.Drawing.Color.Blue);
            requiresFullRedraw = true;
            aPanel.Invalidate();
        }

        byte[] head = new byte[4];
        AccelerationData data = new Accelerometers.WocketsAccelerationData();
        byte[] timestamp = new byte[sizeof(double)];
        byte[] acc = new byte[sizeof(short)];

        public void Dispose()
        {
            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
            {
                sdata[i].Close();
                shead[i].Close();

            }

        }
        int x = 0;
        public void Draw(Graphics g)
        {
            int lastColumnDrawn = 0;

            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
            {
                int tail = this.decoderTails[i];
                int currentHead = tail;

                if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)
                {
                    currentHead = CurrentWockets._Controller._Sensors[i]._Decoder._Head;
                }
#if (PocketPC)
                else if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
                {
                    shead[i].Read(head, 0, 4);
                    currentHead = BitConverter.ToInt32(head, 0);
                    shead[i].Seek(0, System.IO.SeekOrigin.Begin);
                }
#endif
               

                while (tail != currentHead)
                {
                    if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.NON_SHARED)                    
                        data = ((AccelerationData)CurrentWockets._Controller._Sensors[i]._Decoder._Data[tail]);                    
#if (PocketPC)
                    else if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)
                    {
                        sdata[i].Read(timestamp, 0, sizeof(double));
                        data.UnixTimeStamp = BitConverter.ToDouble(timestamp, 0);
                        sdata[i].Read(acc, 0, sizeof(short));
                        data.X = BitConverter.ToInt16(acc, 0);
                        sdata[i].Read(acc, 0, sizeof(short));
                        data.Y = BitConverter.ToInt16(acc, 0);
                        sdata[i].Read(acc, 0, sizeof(short));
                        data.Z = BitConverter.ToInt16(acc, 0);
                    }
#endif         
                    if (!((data.UnixTimeStamp > 0) && (data.UnixTimeStamp >= this.lastUnixTimestamps[i])))
                        break;


                    //check the data comes from the sensor i if the decoder is used with multiple sensors

                    if (this.currentColumns[i] > lastColumnDrawn)
                        lastColumnDrawn = this.currentColumns[i];

                    if (this.currentColumns[i] >= this.plotAreaSize.Width - 1)
                    {
                        g.FillRectangle(blueBrush, 0, 0, this.plotAreaSize.Width + 10, this.plotAreaSize.Height);
                        requiresFullRedraw = true;
                        this.currentColumns[i] = 0;
                    }


                    g.DrawLine(p[0], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][0]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.X));
                    g.DrawLine(p[1], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][1]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Y));
                    g.DrawLine(p[2], this.currentColumns[i], axisOffset[i] - (int)Math.Floor(scaleFactors[i] * previousVals[i][2]), this.currentColumns[i] + 1, axisOffset[i] - (int)Math.Floor(scaleFactors[i] * data.Z));

                    if (this.currentColumns[i] > lastColumn[i])
                        lastColumn[i] = this.currentColumns[i];
        

                    previousVals[i][0] = data.X;
                    previousVals[i][1] = data.Y;
                    previousVals[i][2] = data.Z;
                    previousTimes[i] = data.UnixTimeStamp;

                    this.currentColumns[i] = this.currentColumns[i] + 1;




                    this.lastUnixTimestamps[i] = data.UnixTimeStamp;

                    if (tail >= (Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE - 1))
                    {
                        tail = 0;
#if (PocketPC)
                        if (CurrentWockets._Configuration._MemoryMode == Wockets.Data.Configuration.MemoryConfiguration.SHARED)                    
                            this.sdata[i].Seek(0, System.IO.SeekOrigin.Begin);
#endif
                    }
                    else
                        tail++;

                }
                this.decoderTails[i] = currentHead;
            }




            if (requiresFullRedraw)
            {
                aPanel.Invalidate();
                requiresFullRedraw = false;
                this.aPanel.Width = this.aPanel.Width;
                for (int k = 0; (k < CurrentWockets._Controller._Sensors.Count); k++)
                {
                    this.currentColumns[k] = 0;
                    lastColumn[k] = 0;
                    firstColumn[k] = 999999;
                }

            }
            else
                for (int k = 0; (k < CurrentWockets._Controller._Sensors.Count); k++)
                {
                    aPanel.Invalidate(new System.Drawing.Rectangle(firstColumn[k], 0, lastColumn[k] - firstColumn[k], plotAreaSize.Height));
                    firstColumn[k] = lastColumn[k];
                }

        }
#else
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
            firstColumn= new int[this.wocketsController._Sensors.Count];
            lastColumn = new int[this.wocketsController._Sensors.Count];
            decoderTails = new int[this.wocketsController._Sensors.Count];
            lastUnixTimestamps = new double[this.wocketsController._Sensors.Count];
            this.pointsToPlot = new int[this.wocketsController._Sensors.Count];
            this.mode = PlottingMode.Normal;

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                this.currentColumns[i] = 0;
                this.firstColumn[i] = 999999;
                this.lastColumn[i] = 0;
                this.decoderTails[i] = 0;
                this.lastUnixTimestamps[i] = 0;
                this.pointsToPlot[i] = 0;
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

        public void Draw(Graphics g)
        {
            int lastColumnDrawn = 0;

            for (int i = 0; (i < this.wocketsController._Sensors.Count); i++)
            {
                int receiverID = this.wocketsController._Sensors[i]._Receiver._ID;
                int plottedPoints = 0;

                if (this.wocketsController._Receivers[receiverID]._Status == Wockets.Receivers.ReceiverStatus.Connected)
                {
                    int currentHead = this.wocketsController._Sensors[i]._Decoder._Head;

                    //int decoderID = this.wocketsController._Sensors[i]._Decoder._ID;
                    //for (int j = this.plotFrom[decoderID]; (j < this.wocketsController._Decoders[decoderID]._Size); j++)
                    int tail = this.decoderTails[i];
                    //while(tail<=this.wocketsController._Sensors[i]._Decoder._Head)
                    AccelerationData data = ((AccelerationData)this.wocketsController._Sensors[i]._Decoder._Data[tail]);

                    if (this.mode == PlottingMode.Delayed) //wait until 3 seconds are there then plot 5 pts max
                    {
                        int counter = 0;
                        if ((tail < currentHead) && (currentHead < (this.wocketsController._Sensors[i]._Decoder._Data.Length - 1)))
                            counter = currentHead - tail;
                        else
                            counter = (this.wocketsController._Sensors[i]._Decoder._Data.Length - 1) - tail + currentHead;

                        if (counter > 360)
                            pointsToPlot[i] = 20;
                        else if (counter > 180)
                            pointsToPlot[i] = 10;
                        else
                            pointsToPlot[i] = 5;

                    }
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
                                g.FillRectangle(blueBrush, 0, 0, this.plotAreaSize.Width + 10, this.plotAreaSize.Height);
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
                        if (tail >= (this.wocketsController._Sensors[i]._Decoder._Data.Length - 1))
                            tail = 0;
                        else
                            tail++;

                        data = ((AccelerationData)this.wocketsController._Sensors[i]._Decoder._Data[tail]);
                        plottedPoints++;
                        if ((this.mode == PlottingMode.Delayed) && (plottedPoints == pointsToPlot[i]))
                            break;
                        else if (plottedPoints == 20)
                            break;
                    }
                    this.decoderTails[i] = currentHead;
                }

            }


            if (requiresFullRedraw)
            {
                aPanel.Invalidate();
                requiresFullRedraw = false;
                this.aPanel.Width = this.aPanel.Width;
                for (int k = 0; (k < this.wocketsController._Sensors.Count); k++)
                {
                    this.currentColumns[k] = 0;
                    lastColumn[k] = 0;
                    firstColumn[k] = 999999;
                }

            }
            else
                for (int k = 0; (k < this.wocketsController._Sensors.Count); k++)
                {
                    aPanel.Invalidate(new System.Drawing.Rectangle(firstColumn[k], 0, lastColumn[k] - firstColumn[k], plotAreaSize.Height));
                    firstColumn[k] = lastColumn[k];
                }

        }



#endif
        private SolidBrush aBrush = new SolidBrush(Color.White);
        private SolidBrush blueBrush = new SolidBrush(Color.LightBlue);

        private bool requiresFullRedraw = true;


        public PlottingMode _Mode
        {
            get
            {
                return this.mode;
            }
            set
            {
                this.mode = value;
            }
        }

    }
}
