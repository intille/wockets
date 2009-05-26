using System;
using System.Xml;
using Wockets.Sensors;
using Wockets.Decoders;
using Wockets.Receivers;
using Wockets.Utils;

namespace Wockets.Sensors.Accelerometers
{
    public abstract class Accelerometer : Sensor
    {

        #region Serialization Constants

        protected const string CALIBRATION_ELEMENT = "CALIBRATION";
        protected const string RANGE_ELEMENT = "RANGE";


        protected const string MAX_ATTRIBUTE = "max";
        protected const string MIN_ATTRIBUTE = "min";
        protected const string X1G_ATTRIBUTE = "x1g";
        protected const string XN1G_ATTRIBUTE = "xn1g";
        protected const string Y1G_ATTRIBUTE = "y1g";
        protected const string YN1G_ATTRIBUTE = "yn1g";
        protected const string Z1G_ATTRIBUTE = "z1g";
        protected const string ZN1G_ATTRIBUTE = "zn1g";

        protected const string XSTD_ATTRIBUTE = "xstd";
        protected const string YSTD_ATTRIBUTE = "ystd";
        protected const string ZSTD_ATTRIBUTE = "zstd";
        #endregion Serialization Constants


        #region calibration data
        private double x1g;
        private double xn1g;
        private double y1g;
        private double yn1g;
        private double z1g;
        private double zn1g;
        private double xstd;
        private double ystd;
        private double zstd;
        private double min;
        private double max;
        #endregion calibration data

        public Accelerometer(SensorClasses sensorclass):base(SensorTypes.ACCEL,sensorclass)
        {
        }

       /* public Accelerometer(int id,SensorClasses classname, string location, string description):
            base(id,classname, SensorTypes.ACCEL, location, description)
        {
            this.xmean = 0;
            this.xstd = 0;
            this.ymean = 0;
            this.ystd = 0;
            this.zmean = 0;
            this.zstd = 0;
        }
        */

        public double _Min
        {
            get
            {
                return this.min;
            }

            set
            {
                this.min = value;
            }
        }

        public double _Max
        {
            get
            {
                return this.max;
            }

            set
            {
                this.max = value;
            }
        }
        public double _XSTD
        {
            get
            {
                return this.xstd;
            }
            set
            {
                this.xstd = value;
            }
        }

        public double _YSTD
        {
            get
            {
                return this.ystd;
            }
            set
            {
                this.ystd = value;
            }
        }

        public double _ZSTD
        {
            get
            {
                return this.zstd;
            }
            set
            {
                this.zstd = value;
            }
        }


        public double _X1G
        {
            get
            {
                return this.x1g;
            }
            set
            {
                this.x1g = value;
            }
        }

        public double _XN1G
        {
            get
            {
                return this.xn1g;
            }
            set
            {
                this.xn1g = value;
            }
        }


        public double _Y1G
        {
            get
            {
                return this.y1g;
            }
            set
            {
                this.y1g = value;
            }
        }

        public double _YN1G
        {
            get
            {
                return this.yn1g;
            }
            set
            {
                this.yn1g = value;
            }
        }


        public double _Z1G
        {
            get
            {
                return this.z1g;
            }
            set
            {
                this.z1g = value;
            }
        }

        public double _ZN1G
        {
            get
            {
                return this.zn1g;
            }
            set
            {
                this.zn1g = value;
            }
        }
        protected string ToXML(string innerXML)
        {
            innerXML += "<" + CALIBRATION_ELEMENT + " " + X1G_ATTRIBUTE +
                "=\"" + this.x1g.ToString("0.00") + "\" " + XN1G_ATTRIBUTE + "=\"" + this.xn1g.ToString("0.00") +
                "\" " + Y1G_ATTRIBUTE + "=\"" + this.y1g.ToString("0.00") + "\" " +
                YN1G_ATTRIBUTE + "=\"" + this.yn1g.ToString("0.00") + "\" " +
                Z1G_ATTRIBUTE + "=\"" + this.z1g.ToString("0.00") + "\" " +
                ZN1G_ATTRIBUTE + "=\"" + this.zn1g.ToString("0.00") + "\" " +
                XSTD_ATTRIBUTE + "=\"" + this.xstd.ToString("0.00") + "\" " +
                YSTD_ATTRIBUTE + "=\"" + this.ystd.ToString("0.00") + "\" " +
                ZSTD_ATTRIBUTE + "=\"" + this.zstd.ToString("0.00") +  "\" />\n";
            innerXML += "<" + RANGE_ELEMENT + " " + MAX_ATTRIBUTE +
                "=\"" + this.max.ToString("0.00") + "\" " + MIN_ATTRIBUTE + "=\"" + this.min.ToString("0.00") + "\" />\n";
            return base.ToXML(innerXML);
        }


        public override void FromXML(string xml)
        {
            base.FromXML(xml);
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            if (iNode.Name == SENSOR_ELEMENT)
            {
                foreach (XmlNode jNode in iNode.ChildNodes)
                {
                    foreach (XmlAttribute jAttribute in jNode.Attributes)
                    {
                        if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == X1G_ATTRIBUTE))
                            this.x1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == XN1G_ATTRIBUTE))
                            this.xn1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == Y1G_ATTRIBUTE))
                            this.y1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == YN1G_ATTRIBUTE))
                            this.yn1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == Z1G_ATTRIBUTE))
                            this.z1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == ZN1G_ATTRIBUTE))
                            this.zn1g = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == XSTD_ATTRIBUTE))
                            this.xstd = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == YSTD_ATTRIBUTE))
                            this.ystd = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == CALIBRATION_ELEMENT) && (jAttribute.Name == ZSTD_ATTRIBUTE))
                            this.zstd = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == RANGE_ELEMENT) && (jAttribute.Name == MIN_ATTRIBUTE))
                            this._Min = Convert.ToDouble(jAttribute.Value);
                        else if ((jNode.Name == RANGE_ELEMENT) && (jAttribute.Name == MAX_ATTRIBUTE))
                            this._Max = Convert.ToDouble(jAttribute.Value);

                    }
                }
            }
        }

    }
}
