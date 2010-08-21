using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;

namespace Wockets.Data.Configuration
{
    /// <summary>
    /// This class stores configuration information about the running wocket setup and can be serialized into an xml
    /// </summary>
    public class WocketsConfiguration : XMLSerializable
    {

        #region XML Constants
        /// <summary>
        /// The XML root configuration element
        /// </summary>
        private const string CONFIGURATION_ELEMENT = "CONFIGURATION";

        /// <summary>
        /// The software root element
        /// </summary>
        private const string SOFTWARE_ELEMENT = "SOFTWARE";

        /// <summary>
        /// The element that stores the software version
        /// </summary>
        private const string VERSION_ATTRIBUTE = "version";

        /// <summary>
        /// The element that stores the mode of the software whether it was in debug or release mode
        /// </summary>
        private const string MODE_ATTRIBUTE = "mode";

        /// <summary>
        /// The element that stores the memory mode for the software whether decoded data is stored in shared or non shared memory
        /// </summary>
        private const string MEMORY_MODE_ATTRIBUTE = "memorymode";


        /// <summary>
        /// The root element that stores configuration details for feature extraction
        /// </summary>
        private const string FEATURES_ELEMENT = "FEATURES";

        /// <summary>
        /// The power for the FFT window, for example 7 would mean the size of the window has to be mapped to 2^7
        /// typically using cubic spline interpolation
        /// </summary>
        private const string FFT_INTERPOLATION_POWER_ATTRIBUTE = "fft_interpolation_power";

        /// <summary>
        /// The maximum number of frequencies that are included in the computed feature vector
        /// </summary>
        private const string FFT_MAX_FREQUENCIES_ATTRIBUTE = "fft_maximum_frequencies";

        /// <summary>
        /// The number of windows used for smoothening
        /// </summary>
        private const string SMOOTH_WINDOW_ATTRIBUTE = "smooth_window_count";

        /// <summary>
        /// The number of milliseconds used to calculate a feature vector
        /// </summary>
        private const string FEATURE_WINDOW_SIZE_ATTRIBUTE = "feature_window_size";

        /// <summary>
        /// The percentage of overlap between consecutive feature windows
        /// </summary>
        private const string FEATURE_WINDOW_OVERLAP_ATTRIBUTE = "feature_window_overlap";

        /// <summary>
        /// The number of milliseconds used to check for data quality and error percentages
        /// </summary>
        private const string ERROR_WINDOW_SIZE_ATTRIBUTE = "error_window_size";

        /// <summary>
        /// The maximum number of consecutive missed data points in a window of data
        /// </summary>
        private const string MAXIMUM_CONSECUTIVE_PACKET_LOSS_ATTRIBUTE = "maximum_consecutive_packet_loss";

        /// <summary>
        /// The maximum percentage of loss in a window of data
        /// </summary>
        private const string MAXIMUM_NONCONSECUTIVE_PACKET_LOSS_ATTRIBUTE = "maximum_nonconsecutive_packet_loss";


        #endregion XML Constants

        #region Software Variables     
        /// <summary>
        /// Specifies if the software is in debug or release mode
        /// </summary>
        public SoftwareConfiguration _SoftwareMode =  SoftwareConfiguration.DEBUG;

        /// <summary>
        /// Specifies if shared or non shared memory is used
        /// </summary>
        public MemoryConfiguration _MemoryMode = MemoryConfiguration.NON_SHARED;
        #endregion Software Variables

        #region Feature Window Vairables
        /// <summary>
        /// Specifies the size of the window expected by the FFT, always a power of 2
        /// </summary>
        public int _FFTInterpolationPower;

        /// <summary>
        /// Specifies the maximum number of frequencies to be used in feature calculation
        /// </summary>
        public int _FFTMaximumFrequencies=7;

        /// <summary>
        /// Specifies the number of windows used by a classifier to smoothen the predicited class
        /// </summary>
        public int _SmoothWindowCount=5;

        /// <summary>
        /// Specifies the number of milliseconds used to compute a feature vector
        /// </summary>
        public int _FeatureWindowSize=1000;

        /// <summary>
        /// Specifies the percentage of overlap between consecutive windows
        /// </summary>
        public double _FeatureWindowOverlap=0.5;

        /// <summary>
        /// Specifies the size of the window used to detect errors
        /// </summary>
        public int _ErrorWindowSize=1000;

        /// <summary>
        /// Specifies the maximum acceptable packet loss
        /// </summary>
        public int _MaximumConsecutivePacketLoss=20;

        /// <summary>
        /// Specifies the maximum percentage of packet loss within a window
        /// </summary>
        public double _MaximumNonconsecutivePacketLoss=0.2;
        #endregion Feature Window Vairables

        /// <summary>
        /// The constructor sets the object to its default values
        /// </summary>
        public WocketsConfiguration()
        {
        }

        #region Serialization Methods

        /// <summary>
        /// Converts the configuration to an XML string
        /// </summary>
        /// <returns>XML string that describes the configuration</returns>
        public string ToXML()
        {
            string xml = "";
            return "";
        }

        /// <summary>
        /// Loads the configuration from an xml file
        /// </summary>
        /// <param name="xmlFile">The name of an xml file that stores the configuration information</param>
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
                            /*if (iAttribute.Name == VERSION_ATTRIBUTE)
                                CurrentWockets._Version = iAttribute.Value;                  
                            else*/ if (iAttribute.Name == MODE_ATTRIBUTE)
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
        }

        #endregion Serialization Methods
    }
}
