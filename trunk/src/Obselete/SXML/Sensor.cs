using System;
using System.Collections.Generic;
using System.Text;

namespace SXML
{
    public class Sensor
    {
        private string sensor_class;
        private string type;
        private string id;
        private string sensor_object;
        private string location;
        private string description;
        private string receiver;
        private string display_type;
        private string display_x;
        private string display_y;
        private string color_on;
        private string color_off;
        private double xmean;
        private double xstd;
        private double ymean;
        private double ystd;
        private double zmean;
        private double zstd;
        private int index;
        private int samplingRate;


        public Sensor()
        {
            this.samplingRate = -1; //only used for builtin sensors
        }

        public int SamplingRate
        {
            get
            {
                return this.samplingRate;
            }

            set
            {
                this.samplingRate = value;
            }
        }
        public int Index
        {
            get
            {
                return this.index;
            }
            set
            {
                this.index = value;
            }
        }
        public string SensorClass
        {
            get
            {
                return this.sensor_class;
            }
            set
            {
                this.sensor_class = value;
            }
        }

        public string Type
        {
            get
            {
                return this.type;
            }

            set
            {
                this.type = value;
            }
        }

        public string ID
        {
            get
            {
                return this.id;
            }

            set
            {
                this.id = value;
            }
        }

        public string SensorObject
        {
            get
            {
                return this.sensor_object;
            }

            set
            {
                this.sensor_object = value;
            }
        }

        public string Receiver
        {
            get
            {
                return this.receiver;
            }
            set
            {
                this.receiver = value;
            }
        }

        public string Location
        {
            get
            {
                return this.location;
            }
            set
            {
                this.location = value;
            }
        }

        public string Description
        {
            get
            {
                return this.description;
            }

            set
            {
                this.description = value;
            }
        }

        public string DisplayType
        {
            get
            {
                return this.display_type;
            }
            set
            {
                this.display_type = value;
            }
        }

        public string DisplayX
        {
            get
            {
                return this.display_x;
            }
            set
            {
                this.display_x = value;
            }
        }

        public string DisplayY
        {
            get
            {
                return this.display_y;
            }
            set
            {
                this.display_y = value;
            }
        }

        public string ColorOn
        {

            get
            {
                return this.color_on;
            }
            set
            {
                this.color_on = value;
            }
        }

        public string ColorOff
        {
            get
            {
                return this.color_off;
            }
            set
            {
                this.color_off = value;
            }
        }

        public double XMean
        {
            get
            {
                return this.xmean;
            }
            set
            {
                this.xmean = value;
            }
        }

        public double YMean
        {
            get
            {
                return this.ymean;
            }
            set
            {
                this.ymean = value;
            }
        }

        public double ZMean
        {
            get
            {
                return this.zmean;
            }
            set
            {
                this.zmean = value;
            }
        }


        public double XStd
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

        public double YStd
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

        public double ZStd
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

        public string toXML()
        {
            string xml = "<"+Constants.SENSOR_ELEMENT+ " "+
                Constants.CLASS_ATTRIBUTE+"=\""+this.sensor_class+"\" "+
                Constants.TYPE_ATTRIBUTE+"=\""+this.type+"\">\n";

            xml += "<" + Constants.ID_ELEMENT + " " + Constants.ID_ATTRIBUTE + "=\"" +
                this.id + "\"></" + Constants.ID_ELEMENT + ">\n";

            xml += "<" + Constants.OBJECT_ELEMENT + " " + Constants.TEXT_ATTRIBUTE + "=\"\"></" +
                Constants.OBJECT_ELEMENT + ">\n";
            xml += "<" + Constants.RECEIVER_ELEMENT + " " + Constants.ID_ATTRIBUTE + "=\"" +
                this.receiver + "\"></" + Constants.RECEIVER_ELEMENT + ">\n";
            xml += "<" + Constants.LOCATION_ELEMENT + " " + Constants.TEXT_ATTRIBUTE + "=\"" +
                this.location + "\"></" + Constants.LOCATION_ELEMENT + ">\n";
            xml += "<" + Constants.DESCRIPTION_ELEMENT + " " + Constants.TEXT_ATTRIBUTE +
                "=\"" + this.description + "\"></" + Constants.DESCRIPTION_ELEMENT + ">\n";
            xml += "<" + Constants.DISPLAY_ELEMENT + " " + Constants.DISPLAY_TYPE_ATTRIBUTE + "=\"" +
                this.display_type + "\" " + Constants.DISPLAY_X + "=\"" + this.display_x + "\" " +
                Constants.DISPLAY_Y + "=\"" + this.display_y + "\">\n";
            xml += "<" + Constants.COLOR_ELEMENT + " " + Constants.ON_ATTRIBUTE + "=\"" +
                this.color_on + "\" " + Constants.OFF_ATTRIBUTE + "=\"" + this.color_off +
                "\"></" + Constants.COLOR_ELEMENT + ">\n";
            xml += "</" + Constants.DISPLAY_ELEMENT + ">\n";
            xml += "<" + Constants.CALIBRATION_ELEMENT + " " + Constants.XMEAN_ATTRIBUTE +
                "=\"" + this.xmean.ToString("0.00") + "\" " + Constants.XSTD_ATTRIBUTE + "=\"" + this.xstd.ToString("0.00") +
                "\" " + Constants.YMEAN_ATTRIBUTE + "=\"" + this.ymean.ToString("0.00") + "\" " +
                Constants.YSTD_ATTRIBUTE + "=\"" + this.ystd.ToString("0.00") + "\" " +
                Constants.ZMEAN_ATTRIBUTE + "=\"" + this.zmean.ToString("0.00") + "\" " +
                Constants.ZSTD_ATTRIBUTE + "=\"" + this.zstd.ToString("0.00") + "\" />\n";
            xml += "</" + Constants.SENSOR_ELEMENT + ">\n";

            return xml;
        }
    }
}
