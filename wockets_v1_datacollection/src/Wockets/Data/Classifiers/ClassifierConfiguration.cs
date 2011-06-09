using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Classifiers
{
    public abstract class ClassifierConfiguration: XMLSerializable
    {

                
        #region XML Constants
        private const string CONFIGURATION_ELEMENT = "CONFIGURATION";
        private const string WINDOW_ELEMENT = "WINDOW";
        private const string SAMPLING_ELEMENT = "SAMPLING";
        private const string ERROR_ELEMENT = "ERROR";
        private const string FFT_ELEMENT = "FFT";
        private const string TRAINING_ELEMENT = "TRAINING";
        private const string CLASSIFIER_ELEMENT = "CLASSIFIER";
        private const string QUALITY_ELEMENT = "QUALITY";       
        private const string QUALITY_WINDOW_SIZE = "window_size";
        private const string WINDOW_TIME_ATTRIBUTE = "time";
        private const string WINDOW_OVERLAP_ATTRIBUTE = "overlap";
        private const string SAMPLING_RATE_ATTRIBUTE = "rate";
        private const string CONSECUTIVE_ERROR_ATTRIBUTE = "consecutive";
        private const string NONCONSECUTIVE_ERROR_ATTRIBUTE = "nonconsecutive";
        private const string INTERPOLATION_POWER_ATTRIBUTE = "interpolation_power";
        private const string MAX_FREQUENCIES_ATTRIBUTE = "maximum_frequencies";
        private const string WAIT_TIME_ATTRIBUTE = "wait_time";
        private const string TRAINING_TIME_ATTRIBUTE = "training_time";
        private const string SMOOTH_WINDOW_ATTRIBUTE = "smooth_windows";
        #endregion XML Constants

        #region Feature Window Vairables
        private int windowTime;
        private double windowOverlap;
        private int overlapTime;
        private int fftInterpolatedPower;
        private int fftMaxFrequencies;
        #endregion Feature Window Vairables

        #region Training and Smoothening
        private int trainingWaitTime;
        private int trainingTime;
        private int smooth_windows;
        #endregion Training and Smoothening

        #region Quality Variables
        private int qualityWindowSize;
        private int maximumConsecutiveFramesLoss;
        private double maximumNonconsecutiveFramesLoss;
        #endregion Quality Variables

        public ClassifierConfiguration()
        {
        }

        #region Access Methods
        public int _QualityWindowSize
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
        public int _SmoothWindows
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
        public int _OverlapTime
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
        public int _TrainingTime
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

        public int _TrainingWaitTime
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
        public int _WindowTime
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

        public double _WindowOverlap
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

        public int _MaximumConsecutiveFrameLoss
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

        public double _MaximumNonconsecutiveFrameLoss
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

        public int _FFTInterpolatedPower
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

        public int _FFTMaximumFrequencies
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

        #endregion Access Methods

        #region Serialization Methods
        public string ToXML()
        {
            string xml = "";
            return "";
        }
        public void FromXML(string xmlFile)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xmlFile);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == CONFIGURATION_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode iNode in xNode.ChildNodes)
                {

                    if (iNode.Name == WINDOW_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)                        
                            if (iAttribute.Name == WINDOW_TIME_ATTRIBUTE)                        
                                this._WindowTime = Convert.ToInt32(iAttribute.Value);                            
                            else if (iAttribute.Name == WINDOW_OVERLAP_ATTRIBUTE)                            
                                this._WindowOverlap = Convert.ToDouble(iAttribute.Value);                                                    
                    }
                    else if (iNode.Name == QUALITY_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)                                                    
                            if (iAttribute.Name == QUALITY_WINDOW_SIZE)
                                this._QualityWindowSize = Convert.ToInt32(iAttribute.Value);                                                    
                    }
                    else if (iNode.Name == ERROR_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)                        
                            if (iAttribute.Name == CONSECUTIVE_ERROR_ATTRIBUTE)                            
                                this._MaximumConsecutiveFrameLoss = Convert.ToInt32(iAttribute.Value);                            
                            else if (iAttribute.Name == NONCONSECUTIVE_ERROR_ATTRIBUTE)                            
                                this._MaximumNonconsecutiveFrameLoss = Convert.ToDouble(iAttribute.Value);                                                    
                    }

                    else if (iNode.Name == FFT_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)                        
                            if (iAttribute.Name == INTERPOLATION_POWER_ATTRIBUTE)                            
                                this._FFTInterpolatedPower = Convert.ToInt32(iAttribute.Value);                            
                            else if (iAttribute.Name == MAX_FREQUENCIES_ATTRIBUTE)                            
                                this._FFTMaximumFrequencies = Convert.ToInt32(iAttribute.Value);                                                    
                    }
                    else if (iNode.Name == TRAINING_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)                        
                            if (iAttribute.Name == WAIT_TIME_ATTRIBUTE)                            
                                this._TrainingWaitTime = Convert.ToInt32(iAttribute.Value);                            
                            else if (iAttribute.Name == TRAINING_TIME_ATTRIBUTE)                            
                                this._TrainingTime = Convert.ToInt32(iAttribute.Value);                                                    
                    }
                    else if (iNode.Name == CLASSIFIER_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)                                                    
                            if (iAttribute.Name == SMOOTH_WINDOW_ATTRIBUTE)                            
                                this._SmoothWindows = Convert.ToInt32(iAttribute.Value);                                                    
                    }
                }
            }

            this._OverlapTime = ((int)(this._WindowTime * this._WindowOverlap));
        }

        #endregion Serialization Methods
    }
}
