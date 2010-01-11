using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace AXML
{
    public class AnnotatedRecord
    {
        private ArrayList labels;
        private int start_hour;
        private int start_minute;
        private int start_second;
        private int start_millisecond;
        private double start_unix;
        private string start_date;
        private string end_date;
        private int end_hour;
        private int end_minute;
        private int end_second;
        private int end_millisecond;
        private double end_unix;
        private float quality;

        public AnnotatedRecord()
        {
            this.labels=new ArrayList();
        }


        public ArrayList Labels
        {
            get
            {
                return this.labels;
            }
        }
        public float Quality
        {
            get
            {
                return this.quality;
            }

            set
            {
                this.quality = value;
            }
        }
        public string EndDate
        {
            get
            {
                return this.end_date;
            }
            set
            {
                this.end_date = value;
            }
        }

        public string StartDate
        {
            get
            {
                return this.start_date;
            }
            set
            {
                this.start_date = value;
            }
        }

        public double StartUnix
        {
            get
            {
                return this.start_unix;
            }
            set
            {
                this.start_unix = value;
            }
        }

        public double EndUnix
        {
            get
            {
                return this.end_unix;
            }
            set
            {
                this.end_unix = value;
            }
        }
        public int StartHour
        {
            get
            {
                return this.start_hour;
            }
            set
            {
                this.start_hour = value;
            }
        }

        public int StartMinute
        {
            get
            {
                return this.start_minute;
            }

            set
            {
                this.start_minute = value;
            }
        }

        public int StartSecond
        {
            get
            {
                return this.start_second;
            }
            set
            {
                this.start_second = value;
            }
        }


        public int StartMillisecond
        {
            get
            {
                return this.start_millisecond;
            }
            set
            {
                this.start_millisecond = value;
            }
        }

        public int EndMillisecond
        {
            get
            {
                return this.end_millisecond;
            }
            set
            {
                this.end_millisecond = value;
            }
        }

        public int EndHour
        {
            get
            {
                return this.end_hour;
            }
            set
            {
                this.end_hour = value;
            }
        }

        public int EndMinute
        {
            get
            {
                return this.end_minute;
            }

            set
            {
                this.end_minute = value;
            }
        }

        public int EndSecond
        {
            get
            {
                return this.end_second;
            }
            set
            {
                this.end_second = value;
            }
        }

        public string ToXML()
        {
            string xml = "";
            xml += "<" + Constants.LABEL_ELEMENT + " " + Constants.STARTDATE_ATTRIBUTE + "=\"" + this.start_date + "\" " +
                Constants.ENDDATE_ATTRIBUTE + "=\"" + this.end_date + "\" " + Constants.STARTTIME_ATTRIBUTE + "=\"" +
                this.start_hour + ":" + this.start_minute + ":" + this.start_second + "." + this.start_millisecond + "\" " + Constants.ENDTIME_ATTRIBUTE + "=\"" +
                this.end_hour + ":" + this.end_minute + ":" + this.end_second + "." + this.end_millisecond + "\">";

            foreach (Label label in this.labels)
            {
                xml+=label.ToValueXML();
            }
            xml += "</" + Constants.LABEL_ELEMENT + ">\n";
            return xml;
        }


        public string ToCSV()
        {
 
            string csv = "";

            csv += this.start_date + "," + this.end_date+",";
            foreach (Label label in this.labels)
            {
                csv += ","+label.Name ;
            }
            
            return csv;
        }

        public AnnotatedRecord copy()
        {
            AnnotatedRecord ann = new AnnotatedRecord();
            foreach (Label lab in labels)
            {
                ann.Labels.Add(lab);
            }
            ann.StartHour = start_hour;
            ann.StartMinute = start_minute;
            ann.StartSecond = start_second;
            ann.StartMillisecond = start_millisecond;
            ann.StartUnix = start_unix;
            ann.StartDate = start_date;
            ann.EndDate = end_date;
            ann.EndHour = end_hour;
            ann.EndMinute = end_minute;
            ann.EndSecond = end_second;
            ann.EndMillisecond = end_millisecond;
            ann.EndUnix = end_unix;
            ann.Quality = quality;

            return ann;
        }

    }
}
