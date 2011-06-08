
using System;
using System.Collections.Generic;
using System.Text;

namespace MITesAnalysisApplication.conf
{
    public class GeneralConfiguration
    {
   
        private int windowTime;
        private double windowOverlap;
        private int expectedSamplingRate;
        private int maximumConsecutiveFramesLoss;
        private double maximumNonconsecutiveFramesLoss;
        private int fftInterpolatedPower;
        private int fftMaxFrequencies;
        private int trainingWaitTime;
        private int trainingTime;
        private int overlapTime;
        private int smooth_windows;

        private string mode;
        private string connection;
        private string passkey;
        private string mac;
        private byte[] macAddress;

        private int qualityWindowSize;

        public GeneralConfiguration()
        {
            this.macAddress = new byte[Constants.MAC_SIZE];
        }


        public byte[] MacAddress
        {
            get
            {
                return this.macAddress;
            }
        }
        public string Mac
        {
            get
            {
                return this.mac;
            }
            set
            {
                this.mac = value;
            }
        }

        public string Connection
        {
            get
            {
                return this.connection;
            }
            set
            {
                this.connection = value;
            }
        }


        public string Passkey
        {
            get
            {
                return this.passkey;
            }
            set
            {
                this.passkey = value;
            }
        }

        public string Mode
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

        public int QualityWindowSize
        {
            get
            {
                return this.qualityWindowSize;
            }
            set
            {
                this.qualityWindowSize = value;
            }
        }
        public int SmoothWindows
        {
            get
            {
                return this.smooth_windows;
            }
            set
            {
                this.smooth_windows = value;
            }
        }
        public int OverlapTime
        {
            get
            {
                return this.overlapTime;
            }
            set
            {
                this.overlapTime = value;
            }
        }
        public int TrainingTime
        {
            get
            {
                return this.trainingTime;
            }
            set
            {
                this.trainingTime = value;
            }
        }

        public int TrainingWaitTime
        {
            get
            {
                return this.trainingWaitTime;
            }
            set
            {
                this.trainingWaitTime = value;
            }
        }
        public int WindowTime
        {
            get
            {
                return this.windowTime;
            }
            set
            {
                this.windowTime = value;
            }
        }

        public double WindowOverlap
        {
            get
            {
                return this.windowOverlap;
            }
            set
            {
                this.windowOverlap = value;
            }
        }

        public int ExpectedSamplingRate
        {
            get
            {
                return this.expectedSamplingRate;
            }
            set
            {
                this.expectedSamplingRate = value;
            }
        }

        public int MaximumConsecutiveFrameLoss
        {
            get
            {
                return this.maximumConsecutiveFramesLoss;
            }
            set
            {
                this.maximumConsecutiveFramesLoss = value;
            }
        }

        public double MaximumNonconsecutiveFrameLoss
        {
            get
            {
                return this.maximumNonconsecutiveFramesLoss;
            }
            set
            {
                this.maximumNonconsecutiveFramesLoss = value;
            }
        }

        public int FFTInterpolatedPower
        {
            get
            {
                return this.fftInterpolatedPower;
            }
            set
            {
                this.fftInterpolatedPower = value;
            }
        }

        public int FFTMaximumFrequencies
        {
            get
            {
                return this.fftMaxFrequencies;
            }

            set
            {
                this.fftMaxFrequencies = value;
            }
        }
    }
}

