using System;
using System.Drawing;
using System.Threading;
using System.Windows.Forms;
using HousenCS.MITes;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesPlotter.
	/// </summary>
	public class MITesScalablePlotter
	{
		private bool DEBUG = false;

		/// <summary>
		/// 
		/// </summary>
		public const int SIGNALS_PER_AXIS = 3;

		private Size plotAreaSize;
		
		private int[] axisOffset;
		private System.Drawing.Pen[] p;

		private DeviceTypes devType; 
		
		private int graphSize;
		private double scaleFactor;

		private int[,,] plotVals;

		private int maxPlots;

		private MITesDecoder aMITesDecoder;

		private System.Windows.Forms.Panel aPanel;

		private int col = 0;
		private int lastCol = 0;
		//int lastColDrawn = 0;
		private bool firstTime = true;

		private int currentIDCount = 0; 


		/// <summary>
		/// 
		/// </summary>
		public static int MAXRETURNVALS = 40 * 4; // 10 works, 4 is NUMSENSORS


		int[] returnVals = new int[MAXRETURNVALS];
		int returnValsIndex = 0;

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int[] GetReturnVals()
		{
			return returnVals;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetReturnValsIndex()
		{
			return returnValsIndex;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="value"></param>
		public void SetReturnValsIndex(int value)
		{
			returnValsIndex = value;
		}


		/// <summary>
		/// 
		/// </summary>
		public void SetAccelResultsData()
		{
			if (aMITesDecoder.someMITesDataIndex > aMITesDecoder.someMITesData.Length)
				Warning("setAccelResultsData sent invalid dataIndex parameter");

			for (int i=0;i < aMITesDecoder.someMITesDataIndex;i++)
			{			
				if (aMITesDecoder.someMITesData[i].type == ((int) MITesTypes.ACCEL))
					if ((returnValsIndex + 4) < returnVals.Length)
					{
						returnVals[returnValsIndex] = aMITesDecoder.someMITesData[i].channel;
						returnVals[returnValsIndex+1] = aMITesDecoder.someMITesData[i].x;
						returnVals[returnValsIndex+2] = aMITesDecoder.someMITesData[i].y;
						returnVals[returnValsIndex+3] = aMITesDecoder.someMITesData[i].z;
						returnValsIndex += 4;
					}
					else
					{
						Warning("Losing data to plot in SetAccelResultsData");
						returnValsIndex = 0;
					}
			}
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="col"></param>
		public void SetLastCol(int col)
		{
			lastCol = col;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="value"></param>
		public void SetIsFirstTime(bool value)
		{
			firstTime = value;
		}

		/// <summary>
		/// 
		/// </summary>
		public enum DeviceTypes
		{
			/// <summary>
			/// 
			/// </summary>
			PC,
			/// <summary>
			/// 
			/// </summary>
			IPAQ,
			/// <summary>
			/// 
			/// </summary>
			MPX220 
		}

		private void Debug(String aMsg)
		{
			if (DEBUG)
				Console.WriteLine ("DEBUG: " + aMsg);
		}

		private void Warning(String aMsg)
		{
			Console.WriteLine ("WARNING: " + aMsg);
		}

		private void Error(String aMsg)
		{
			Console.WriteLine ("ERROR: " + aMsg);
			Thread.Sleep(10000);
			Application.Exit();
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public bool IsNeedFullRedraw()
		{
			if ((lastCol > col) || firstTime)
				return true;
			else
				return false;
		}

		private void CheckDeviceType(DeviceTypes aDeviceType)
		{
			if ((aDeviceType != DeviceTypes.PC) &&
				(aDeviceType != DeviceTypes.IPAQ) &&
				(aDeviceType != DeviceTypes.MPX220))
			{
				Error("Unknown device type" + aDeviceType);
			}
		}
		private void SetPenColors()
		{
			p = new System.Drawing.Pen[SIGNALS_PER_AXIS];

			p[0] = new Pen(System.Drawing.Color.Orange);
			p[1] = new Pen(System.Drawing.Color.Red);
			p[2] = new Pen(System.Drawing.Color.Blue);
		}

		private void SetAxisOffset()
		{
			int dy = (int) Math.Floor(plotAreaSize.Height/((double) maxPlots));
			int offset = dy; 

			for (int i = 0; i < axisOffset.Length; i++)
			{
				axisOffset[i] = offset;
				offset += dy;
			}
		}

		private void SetupStorage()
		{
			axisOffset = new int[maxPlots];
			plotVals = new int[maxPlots,3,plotAreaSize.Width];	
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aPlotAreaSize"></param>
		/// <param name="maxNumPlots"></param>
		public void SetupScaleFactor(Size aPlotAreaSize, int maxNumPlots)
		{
			plotAreaSize = aPlotAreaSize;

            // This is necessary to avoid a crash if the plotting window is closed
            if (plotAreaSize.Height <= 0)
                plotAreaSize.Height = 1;
            if (plotAreaSize.Width <= 0)
                plotAreaSize.Width = 1;

			maxPlots = maxNumPlots;
			SetupStorage();
			
			//graphSize = (int) Math.Floor((plotAreaSize.Height/((double) 2*maxPlots))); 
			graphSize = (int) Math.Floor((plotAreaSize.Height/((double) maxPlots))); 
			scaleFactor = graphSize/((float) MITesData.NUM_ACCEL_STEPS);	
			//scaleFactor = graphSize*2.0/((float) MITesData.NUM_ACCEL_STEPS);	
			SetAxisOffset();	
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aForm"></param>
		/// <param name="aDeviceType"></param>
		/// <param name="maxPlots"></param>
		/// <param name="aMITesDecoder"></param>
		/// <param name="aSize"></param>
        /// 
        private int[] columns;
		public MITesScalablePlotter(System.Windows.Forms.Panel aPanel, DeviceTypes aDeviceType, int maxPlots, MITesDecoder aMITesDecoder, Size aSize)
		{
			this.plotAreaSize = aSize; 
			this.aMITesDecoder = aMITesDecoder;
			//this.aTab = aTab;
            this.aPanel = aPanel;
			this.maxPlots = maxPlots;
            this.columns = new int[this.maxPlots];
            for (int i = 0; i < this.maxPlots; i++)
                this.columns[i] = 0;
			devType = aDeviceType; 
			CheckDeviceType(devType);

			for (int i = 0; i < someIDMappings.Length; i++)
				someIDMappings[i] = MITesData.NONE; 

			// Allocate arrays and setup for scaling 
			SetupScaleFactor(plotAreaSize, maxPlots);

			InitPlotVals();

			SetPenColors();
			SetAxisOffset();

			ResetIsSeenID();

		}

		private void InitPlotVals()
		{
			for (int i = 0; i < maxPlots; i++)
				for (int j = 0; j < 3; j++)
					for (int k = 0; k < plotAreaSize.Width; k++)
						plotVals[i,j,k] = MITesData.EMPTY;
		}


		/// <summary>
		/// 
		/// </summary>
		/// <param name="c"></param>
		public void resetPlotVals(int c)
		{
			for (int i = 0; i < maxPlots; i++)
			{
				plotVals[i,0,c] = MITesData.EMPTY;
				plotVals[i,1,c] = MITesData.EMPTY;
				plotVals[i,2,c] = MITesData.EMPTY;
			}
		}

		private bool InValidRange(int n)
		{
			if ((n >= 0) && (n <= MITesData.NUM_ACCEL_STEPS))  // SSI < or <= -- check
				return true;
			else
			{
				Console.WriteLine ("N out of range for plot" + n);
				return false;
			}
		}

		private int x,y,z,id;
		private int errorPrintCount = 0; 

		private int[] someIDMappings = new int[MITesData.MAX_MITES_CHANNELS];
		private bool[] isSeenID = new bool[MITesData.MAX_MITES_CHANNELS];

 

		private void ResetIsSeenID()
		{
			for (int i = 0; i < isSeenID.Length; i++)
			{
				isSeenID[i] = false;
			}
		}

        
		/// <summary>
		/// 
		/// </summary>
		/// <param name="sensorID"></param>
		/// <returns></returns>
		public bool checkIsSeenID(int sensorID)
		{
			if (isSeenID[sensorID] == true)
			{
				ResetIsSeenID();
				return true;
			}
			else
			{
				isSeenID[sensorID] = true;
				return false;
			}
		}

        public bool checkIsSeenAllID(int sensorID)
        {
            bool t = true;
            for (int i = 0; (i < this.maxPlots); i++)            
                t = t & isSeenID[i];            
            if (t)
            {            
                ResetIsSeenID();
                return true;
            }
            else
            {
                isSeenID[sensorID] = true;
                return false;
            }
        }

		/// <summary>
		/// The MITesDecoder maps the sensor channel ID onto an index value used when 
		/// storing data. This method returns that index value given the channel ID.
		/// </summary>
		/// <param name="anID">Channel ID number</param>
		/// <returns>Index used to store that channel</returns>
		private int GetSensorIDMap(int anID)
		{
			if (anID < MITesData.MAX_MITES_CHANNELS)
			{
				if (someIDMappings[anID] == MITesData.NONE)
				{
					// Add the sensor ID
					someIDMappings[anID] = currentIDCount; 
					currentIDCount++;
					return someIDMappings[anID];
				}
				else
					return someIDMappings[anID];
			}

			return MITesData.NONE;
		}

        public void setBuiltinPlotVals(int[] sensorData, int startPlotIndex)
        {

            for (int j = 0; (j < sensorData.Length); j = j + 3)
            {
                if (sensorData[j*3]>0)
                    plotVals[startPlotIndex+j, 0, col] = sensorData[j * 3];
                else
                    plotVals[startPlotIndex+j, 0, col] = MITesData.EMPTY;

                if (sensorData[j * 3 +1] > 0)
                    plotVals[startPlotIndex+j, 1, col] = sensorData[j * 3 + 1];
                else
                    plotVals[startPlotIndex+j, 1, col] = MITesData.EMPTY;

                if (sensorData[j * 3 + 2] > 0)
                    plotVals[startPlotIndex + j, 2, col] = sensorData[j * 3 + 2];
                else
                    plotVals[startPlotIndex+j, 2, col] = MITesData.EMPTY;
            }
        }

        //public void setPlotVals(GenericAccelerometerData builtInData, int startPlotIndex)
        //{

        //    if (builtInData.X > 0)
        //        plotVals[startPlotIndex, 0, col] = builtInData.X / 5;
        //    else
        //        plotVals[startPlotIndex, 0, col] = MITesData.EMPTY;

        //    if (builtInData.Y > 0)
        //        plotVals[startPlotIndex, 1, col] = builtInData.Y / 5;
        //    else
        //        plotVals[startPlotIndex, 1, col] = MITesData.EMPTY;

        //    if (builtInData.Z > 0)
        //        plotVals[startPlotIndex, 2, col] = builtInData.Z / 5;
        //    else
        //        plotVals[startPlotIndex, 2, col] = MITesData.EMPTY;

            
        //    //aPanel.Invalidate(new System.Drawing.Rectangle(col, 0, 2, plotAreaSize.Height));
        //    //col++;
        //    //if (col >= plotAreaSize.Width)
        //    //    col = 0;

        //    //resetPlotVals(col);
        //}

		/// <summary>
		/// 
		/// </summary>
        public void setPlotVals(GenericAccelerometerData builtInData, int startPlotIndex)
        {
            int[] returnVals = GetReturnVals();
            int numVals = GetReturnValsIndex();

            if ((numVals == 0) && (builtInData != null))
            {

                plotVals[startPlotIndex, 0, col] = builtInData.X / 5;
                plotVals[startPlotIndex, 1, col] = builtInData.Y / 5;
                plotVals[startPlotIndex, 2, col] = builtInData.Z / 5;

                aPanel.Invalidate(new System.Drawing.Rectangle(col - 1, 0, 2, plotAreaSize.Height));
                col++;
                if (col >= plotAreaSize.Width)
                    col = 0;

                resetPlotVals(col);

            }
            else
            {
                for (int j = 0; j < numVals; j = j + 4)
                {
                    if (returnVals[j] != MITesDecoder.STATIC_CHANNEL)
                    {
                        id = GetSensorIDMap(returnVals[j]);
                        if (id == MITesData.NONE)
                            Warning("GetSensorIDMap returned NONE!");

                        if (id < maxPlots)
                        {
                            x = returnVals[j + 1];
                            y = returnVals[j + 2];
                            z = returnVals[j + 3];

                            if (InValidRange(x))
                                plotVals[id, 0, col] = x;
                            else
                                plotVals[id, 0, col] = MITesData.EMPTY;

                            if (InValidRange(y))
                                plotVals[id, 1, col] = y;
                            else
                                plotVals[id, 1, col] = MITesData.EMPTY;

                            if (InValidRange(z))
                                plotVals[id, 2, col] = z;
                            else
                                plotVals[id, 2, col] = MITesData.EMPTY;

                            //if there are extra plots to plot the builtin sensor data
                            if (startPlotIndex != maxPlots)
                            {
                                if (builtInData != null)
                                {

                                    plotVals[startPlotIndex, 0, col] = builtInData.X / 5;
                                    plotVals[startPlotIndex, 1, col] = builtInData.Y / 5;
                                    plotVals[startPlotIndex, 2, col] = builtInData.Z / 5;
                                    //builtInData = null;

                                    //aPanel.Invalidate(new System.Drawing.Rectangle(0, 0,plotAreaSize.Width, plotAreaSize.Height));
                                    //col++;
                                    //if (col >= plotAreaSize.Width)
                                    //    col = 0;

                                    //resetPlotVals(col);

                                }
                                else
                                {
                                    plotVals[startPlotIndex, 0, col] = MITesData.EMPTY;
                                    plotVals[startPlotIndex, 1, col] = MITesData.EMPTY;
                                    plotVals[startPlotIndex, 2, col] = MITesData.EMPTY;
                                }
                            }

                            if (checkIsSeenAllID(id)) // Set isSeenID array
                            {
                                aPanel.Invalidate(new System.Drawing.Rectangle(col - 1, 0, 2, plotAreaSize.Height));
                                col++;
                                if (col >= plotAreaSize.Width)
                                    col = 0;

                                resetPlotVals(col);
                            }
                        }
                        else
                        {
                            if (errorPrintCount == 0)
                                Console.WriteLine("WARNING! Not plotting data from Sensor ID:" + returnVals[j]);
                            errorPrintCount++;
                            if (errorPrintCount > 1000)
                                errorPrintCount = 0;
                        }
                    }
                }
            }

            SetReturnValsIndex(0);
        }

		private int v1;
		private int v2;
		private int dc;


		/// <summary>
		/// 
		/// </summary>
		/// <param name="g"></param>
		public void DrawValsFast(Graphics g)
		{			
			int lastColDrawn = lastCol;
			dc = col;

			if (lastColDrawn > dc)		
			{
				for (int c = lastColDrawn; c < plotAreaSize.Width; c++)
				{
					for (int i = 0; i < maxPlots;i++) //SSI maxPlots correct?
						for (int j = 0; j < 3; j++)
						{
							if (plotVals[i,j,c] == MITesData.EMPTY)
								v1 = MITesData.EMPTY;
							else
								v1 = axisOffset[i]-ScaleToGraph(plotVals[i,j,c]);
						
							if (c != 0)
							{
								if (plotVals[i,j,c-1] == MITesData.EMPTY)
									v2 = MITesData.EMPTY;
								else
									v2 = axisOffset[i]-ScaleToGraph(plotVals[i,j,c-1]);
							}
							else 
								v2 = MITesData.EMPTY;
												
							if ((v1 != MITesData.EMPTY) && (v2 != MITesData.EMPTY))
							{
								g.DrawLine(p[j],c+4,v1,c-1+4,v2); // 4 is gapDistance
								//g.DrawRectangle(p[i*3 + j],dc,v1,1,1);
							}
						}
				}
			}

			if (lastColDrawn > dc)
				lastColDrawn = 0;

			for (int c = lastColDrawn; c <= dc; c++)
			{
				for (int i = 0; i < maxPlots;i++) // SSI maxPlots correct?
					for (int j = 0; j < 3; j++)
					{
						if (plotVals[i,j,c] == MITesData.EMPTY)
							v1 = MITesData.EMPTY;
						else
							v1 = axisOffset[i]-ScaleToGraph(plotVals[i,j,c]);
						
						if (c != 0)
						{
							if (plotVals[i,j,c-1] == MITesData.EMPTY)
								v2 = MITesData.EMPTY;
							else
								v2 = axisOffset[i]-ScaleToGraph(plotVals[i,j,c-1]);
						}
						else 
							v2 = MITesData.EMPTY;
												
						if ((v1 != MITesData.EMPTY) && (v2 != MITesData.EMPTY))
						{
							g.DrawLine(p[j],c+4,v1,c-1+4,v2); // 4 is gapDistance
							//g.DrawRectangle(p[i*3 + j],dc,v1,1,1);
						}
					}
			}
			SetLastCol(col);
		}

		/// <summary>
		/// Convert a 8 bit value to the graphable value
		/// </summary>
		/// <param name="n"></param>
		private int ScaleToGraph(int n)
		{
			int v = (int) Math.Floor(n * scaleFactor);
			//			if (v < 0)
			//				textBox1.Text = "Val to low " + v;
			//			else if (v > 1024)
			//				textBox1.Text = "Val to high " + v;
			return (v); 
		}

	}
}