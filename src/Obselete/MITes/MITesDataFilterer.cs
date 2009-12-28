using System;
using HousenCS.MITes;
using System.Collections;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesDataFilterer.
	/// </summary>
	public class MITesDataFilterer
	{
		private MITesDecoder aMITesDecoder;
		private static int SIZE_SAVE_ARRAY = 5;
		private int[,,] pastSamples = new int[MITesData.MAX_MITES_CHANNELS,3,SIZE_SAVE_ARRAY];
		private int[] pastSamplesIndex = new int[MITesData.MAX_MITES_CHANNELS];


        /// <summary>
        /// 
        /// </summary>
 

        public static MITesPerformanceStats[]  MITesPerformanceTracker= new MITesPerformanceStats[MITesData.MAX_MITES_CHANNELS];


		private int nonNoiseCount = 0;
				


        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        /// 
        // Modified this method to update individual performance counters based on the channel ID for each
        // MITes sensor. 
        public int CountNonNoise()
        {
            nonNoiseCount = 0;

            for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
            {
                if (aMITesDecoder.someMITesData[i].type != (int)MITesTypes.NOISE)
                {
                    if (aMITesDecoder.someMITesData[i].channel>0) // Don't include HR
                        MITesPerformanceTracker[(int)aMITesDecoder.someMITesData[i].channel].SampleCounter++;                   
                    nonNoiseCount++;
                }
            }
            return nonNoiseCount;
        }
    


		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		public MITesDataFilterer(MITesDecoder aMITesDecoder)
		{
			this.aMITesDecoder = aMITesDecoder;
		}

		/// <summary>
		/// 
		/// </summary>
		public void RemoveZeroNoise()
		{
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.ACCEL)
				{
					if ((aMITesDecoder.someMITesData[i].x == 0) || 
						(aMITesDecoder.someMITesData[i].y == 0) ||
						(aMITesDecoder.someMITesData[i].z == 0))
						aMITesDecoder.someMITesData[i].type = (int) MITesTypes.NOISE;
					if ((aMITesDecoder.someMITesData[i].x == 1022) || 
						(aMITesDecoder.someMITesData[i].y == 1022) ||
						(aMITesDecoder.someMITesData[i].z == 1022))
						aMITesDecoder.someMITesData[i].type = (int) MITesTypes.NOISE;
				}
			}
		}

		/// <summary>
		/// 
		/// </summary>
		public void RemoveSpikeNoise()
		{
		}
	}
}

//	//shifting array
//	for(k=0;k<5;k++)
//{
//	x_past_samples[k] = x_past_samples[k+1];
//	y_past_samples[k] = y_past_samples[k+1];
//}
//
//       //adding acceleration to signal queue buffer
//x_past_samples[5] = x_acc;
//y_past_samples[5] = y_acc;
//
//	   //IF SPIKE DETECTOR IS ON
//       #SPIKE_DETECTOR
//		  
//          //calculating difference between adjacent samples(absolute value)
//if(x_past_samples[3] < x_past_samples[5]) 
//x_acc = x_past_samples[5] - x_past_samples[3];
//else 
//x_acc = x_past_samples[3] - x_past_samples[5];
//          //calculating difference between adjacent samples and spike(absolute
//value)
//if(x_past_samples[3] < x_past_samples[4])
//y_acc =  x_past_samples[4]-x_past_samples[3];
//else 
//y_acc = x_past_samples[3] - x_past_samples[4];
//
//          //if spike detected in X, eliminate it
//if (x_acc<LSPIKE && y_acc>HSPIKE )
//x_past_samples[4] = x_past_samples[3];	  
//
//
//          //calculating difference between adjacent samples(absolute value)
//if(y_past_samples[3] < y_past_samples[5]) 
//x_acc = y_past_samples[5] - y_past_samples[3];
//else 
//x_acc = y_past_samples[3] - y_past_samples[5];
//          //calculating difference between adjacent samples and spike(absolute
//value)
//if(y_past_samples[3] < y_past_samples[4])
//y_acc = y_past_samples[4] - y_past_samples[3];
//else 
//y_acc = y_past_samples[3] - y_past_samples[4];
// 
//          //if spike detected in Y, eliminate it
//if (x_acc<LSPIKE && y_acc>HSPIKE )
//y_past_samples[4] = y_past_samples[3];	  
//           
//#endif
