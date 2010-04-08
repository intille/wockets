using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Configuration
{
    public class WocketsConfiguration : XMLSerializable
    {


        #region XML Constants
        private const string CONFIGURATION_ELEMENT = "CONFIGURATION";

        private const string SOFTWARE_ELEMENT = "SOFTWARE";
        private const string VERSION_ATTRIBUTE = "version";
        private const string MODE_ATTRIBUTE = "mode";
        private const string MEMORY_MODE_ATTRIBUTE = "memorymode";

        private const string FEATURES_ELEMENT = "FEATURES";
        private const string FFT_INTERPOLATION_POWER_ATTRIBUTE = "fft_interpolation_power";
        private const string FFT_MAX_FREQUENCIES_ATTRIBUTE = "fft_maximum_frequencies";
        private const string SMOOTH_WINDOW_ATTRIBUTE = "smooth_window_count";
        private const string FEATURE_WINDOW_SIZE_ATTRIBUTE = "feature_window_size";
        private const string FEATURE_WINDOW_OVERLAP_ATTRIBUTE = "feature_window_overlap";
        private const string ERROR_WINDOW_SIZE_ATTRIBUTE = "error_window_size";
        private const string MAXIMUM_CONSECUTIVE_PACKET_LOSS_ATTRIBUTE = "maximum_consecutive_packet_loss";
        private const string MAXIMUM_NONCONSECUTIVE_PACKET_LOSS_ATTRIBUTE = "maximum_nonconsecutive_packet_loss";


        #endregion XML Constants

        #region Software Variables
        public string _Version = WocketsController._Version;
        public SoftwareConfiguration _SoftwareMode =  SoftwareConfiguration.DEBUG;
        public MemoryConfiguration _MemoryMode = MemoryConfiguration.NON_SHARED;
        #endregion Software Variables

        #region Feature Window Vairables
        public int _FFTInterpolationPower;
        public int _FFTMaximumFrequencies;
        public int _SmoothWindowCount;
        public int _FeatureWindowSize;
        public double _FeatureWindowOverlap;
        public int _ErrorWindowSize;
        public int _MaximumConsecutivePacketLoss;
        public double _MaximumNonconsecutivePacketLoss;
        #endregion Feature Window Vairables

        public WocketsConfiguration()
        {
            CurrentWockets._Configuration = this;
        }

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

                    if (iNode.Name == SOFTWARE_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                            if (iAttribute.Name == VERSION_ATTRIBUTE)
                                this._Version = iAttribute.Value;
                            else if (iAttribute.Name == MODE_ATTRIBUTE)
                                this._SoftwareMode = ((String.Compare(iAttribute.Value, SoftwareConfiguration.DEBUG.ToString(), true) == 0) ? SoftwareConfiguration.DEBUG : SoftwareConfiguration.RELEASE);
                            else if (iAttribute.Name == MEMORY_MODE_ATTRIBUTE)
                                this._MemoryMode = ((String.Compare(iAttribute.Value, MemoryConfiguration.NON_SHARED.ToString(), true) == 0) ? MemoryConfiguration.NON_SHARED : MemoryConfiguration.SHARED);
                    }
                    else if (iNode.Name == FEATURES_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                            if (iAttribute.Name == FFT_INTERPOLATION_POWER_ATTRIBUTE)
                                this._FFTInterpolationPower = Convert.ToInt32(iAttribute.Value);
                            else if (iAttribute.Name == FFT_MAX_FREQUENCIES_ATTRIBUTE)
                                this._FFTMaximumFrequencies = Convert.ToInt32(iAttribute.Value);
                            else if (iAttribute.Name == SMOOTH_WINDOW_ATTRIBUTE)
                                this._SmoothWindowCount = Convert.ToInt32(iAttribute.Value);
                            else if (iAttribute.Name == FEATURE_WINDOW_SIZE_ATTRIBUTE)
                                this._FeatureWindowSize= Convert.ToInt32(iAttribute.Value);
                            else if (iAttribute.Name == FEATURE_WINDOW_OVERLAP_ATTRIBUTE)
                                this._FeatureWindowOverlap = Convert.ToDouble(iAttribute.Value);
                            else if (iAttribute.Name == ERROR_WINDOW_SIZE_ATTRIBUTE)
                                this._ErrorWindowSize = Convert.ToInt32(iAttribute.Value);
                            else if (iAttribute.Name == MAXIMUM_CONSECUTIVE_PACKET_LOSS_ATTRIBUTE)
                                this._MaximumConsecutivePacketLoss = Convert.ToInt32(iAttribute.Value);
                            else if (iAttribute.Name == MAXIMUM_NONCONSECUTIVE_PACKET_LOSS_ATTRIBUTE)
                                this._MaximumNonconsecutivePacketLoss = Convert.ToDouble(iAttribute.Value);
                    }
                }
            }

            //this._OverlapTime = ((int)(this._WindowTime * this._WindowOverlap));
        }

        #endregion Serialization Methods
    }
}
