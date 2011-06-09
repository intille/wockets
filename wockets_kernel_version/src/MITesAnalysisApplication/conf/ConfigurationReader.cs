using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;

namespace MITesAnalysisApplication.conf
{
    public class ConfigurationReader
    {
        public const string DEFAULT_XML_FILE = "Configuration.xml";
        private string xmlFile;


        public ConfigurationReader(string dataDirectory)
        {
            this.xmlFile = dataDirectory + "\\" + DEFAULT_XML_FILE;
        }

        public GeneralConfiguration parse()
        {
            GeneralConfiguration configuration = new GeneralConfiguration();
            XmlDocument dom = new XmlDocument();
            dom.Load(this.xmlFile);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == Constants.CONFIGURATION_ELEMENT) && (xNode.HasChildNodes))
            {

                //child nodes
                foreach (XmlNode iNode in xNode.ChildNodes)
                {

                    if (iNode.Name == Constants.WINDOW_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.WINDOW_TIME_ATTRIBUTE)
                            {
                                configuration.WindowTime = Convert.ToInt32(iAttribute.Value);
                            }
                            else if (iAttribute.Name == Constants.WINDOW_OVERLAP_ATTRIBUTE)
                            {
                                configuration.WindowOverlap = Convert.ToDouble(iAttribute.Value);
                            }
                        }
                    }
                    else if (iNode.Name == Constants.SAMPLING_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.SAMPLING_RATE_ATTRIBUTE)
                            {
                                configuration.ExpectedSamplingRate = Convert.ToInt32(iAttribute.Value);
                            }
                        }
                    }
                    else if (iNode.Name == Constants.SOFTWARE_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.SOFTWARE_MODE_ATTRIBUTE)
                            {
                                configuration.Mode = iAttribute.Value;
                            }
                            else if (iAttribute.Name == Constants.SOFTWARE_CONNECTION_ATTRIBUTE)
                            {
                                configuration.Connection = iAttribute.Value;
                            }
                            else if (iAttribute.Name == Constants.SOFTWARE_CONNECTION_PASSKEY)
                            {
                                configuration.Passkey = iAttribute.Value;
                            }
                            else if (iAttribute.Name == Constants.SOFTWARE_CONNECTION_MAC)
                            {
                                configuration.Mac = iAttribute.Value;

                                for (int i = 0; (i < Constants.MAC_SIZE); i++)
                                    configuration.MacAddress[i] = (byte)(System.Int32.Parse(iAttribute.Value.Substring(i * 2, 2), System.Globalization.NumberStyles.AllowHexSpecifier) & 0xff);

                            }
                        }
                    }

                    else if (iNode.Name == Constants.QUALITY_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.QUALITY_WINDOW_SIZE)
                            {
                                configuration.QualityWindowSize = Convert.ToInt32(iAttribute.Value);
                            }
                        }
                    }
                    else if (iNode.Name == Constants.ERROR_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.CONSECUTIVE_ERROR_ATTRIBUTE)
                            {
                                configuration.MaximumConsecutiveFrameLoss = Convert.ToInt32(iAttribute.Value);
                            }
                            else if (iAttribute.Name == Constants.NONCONSECUTIVE_ERROR_ATTRIBUTE)
                            {
                                configuration.MaximumNonconsecutiveFrameLoss = Convert.ToDouble(iAttribute.Value);
                            }
                        }
                    }

                    else if (iNode.Name == Constants.FFT_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.INTERPOLATION_POWER_ATTRIBUTE)
                            {
                                configuration.FFTInterpolatedPower = Convert.ToInt32(iAttribute.Value);
                            }
                            else if (iAttribute.Name == Constants.MAX_FREQUENCIES_ATTRIBUTE)
                            {
                                configuration.FFTMaximumFrequencies = Convert.ToInt32(iAttribute.Value);
                            }
                        }
                    }
                    else if (iNode.Name == Constants.TRAINING_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.WAIT_TIME_ATTRIBUTE)
                            {
                                configuration.TrainingWaitTime = Convert.ToInt32(iAttribute.Value);
                            }
                            else if (iAttribute.Name == Constants.TRAINING_TIME_ATTRIBUTE)
                            {
                                configuration.TrainingTime = Convert.ToInt32(iAttribute.Value);
                            }
                        }
                    }
                    else if (iNode.Name == Constants.CLASSIFIER_ELEMENT)
                    {
                        foreach (XmlAttribute iAttribute in iNode.Attributes)
                        {
                            //read nodes attributes
                            if (iAttribute.Name == Constants.SMOOTH_WINDOW_ATTRIBUTE)
                            {
                                configuration.SmoothWindows = Convert.ToInt32(iAttribute.Value);
                            }
                        }
                    }
                }
            }

            configuration.OverlapTime = ((int)(configuration.WindowTime * configuration.WindowOverlap));
            return configuration;
        }
    }
}
