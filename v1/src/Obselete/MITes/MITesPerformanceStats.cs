using System;
using System.Collections.Generic;
using System.Text;

namespace HousenCS.MITes
{
    /// <summary>
    /// This class keeps track of the expected and actual sampling rates for a MITes sensor
    /// 
    /// </summary>
    public class MITesPerformanceStats
    {
        /// <summary>
        /// 
        ///  
        /// </summary>
        /// 

        private  int goodRate;
        private int sampleCounter;
        private int perfectRate;
        private double lastTimeStamp;
        private double lastSamplingRate;
        /// <summary>
        /// 
        ///  
        /// </summary>
        public MITesPerformanceStats(int goodRate)
        {

            this.goodRate = goodRate;
            this.sampleCounter = 0;
            this.lastTimeStamp = 0.0;
            this.lastSamplingRate = 0.0;
        }

        public double LastSamplingRate
        {
            get
            {
                return this.lastSamplingRate;
            }
            set
            {
                this.lastSamplingRate = value;
            }
        }
        public double LastTimeStamp
        {
            get
            {
                return this.lastTimeStamp;
            }

            set
            {
                this.lastTimeStamp = value;
            }
        }
        public int PerfectRate
        {
            get
            {
                return this.perfectRate;
            }
            set
            {
                this.perfectRate = value;
            }
        }
        /// <summary>
        /// 
        ///  
        /// </summary>
        /// 
        public int GoodRate
        {
            get
            {
                return this.goodRate;
            }
            set
            {
                this.goodRate = value;
            }
        }



        /// <summary>
        /// 
        ///  
        /// </summary>
        public int SampleCounter
        {
            get
            {
                return this.sampleCounter;
            }
            set
            {
                this.sampleCounter= value;
            }
        }


    }
}
