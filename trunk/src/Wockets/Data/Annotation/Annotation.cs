using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Text.RegularExpressions;
using Wockets.Utils;

namespace Wockets.Data.Annotation
{
    public class Annotation : XMLSerializable
    {
        public const string ANNOTATION_ELEMENT = "LABEL";
        public const string VALUE_ELEMENT = "VALUE";
        public const string DATE_ATTRIBUTE = "DATE";
        public const string STARTDATE_ATTRIBUTE = "STARTDATE";
        public const string ENDDATE_ATTRIBUTE = "ENDDATE";
        public const string STARTTIME_ATTRIBUTE = "STARTTIME";
        public const string ENDTIME_ATTRIBUTE = "ENDTIME";
        public const string LABEL_ATTRIBUTE = "LABEL";
        public const string CATEGORY_ATTRIBUTE = "CATEGORY";
        
        private ActivityList activities;
        private int start_month=-1;
        private int start_day=-1;
        private int start_year=-1;
        private int start_hour=-1;
        private int start_minute=-1;
        private int start_second=-1;
        private int start_millisecond=-1;
        private double start_unix=-1;
        private string start_date;
        private string end_date;
        private int end_month=-1;
        private int end_day=-1;
        private int end_year=-1;
        private int end_hour=-1;
        private int end_minute=-1;
        private int end_second=-1;
        private int end_millisecond=-1;
        private double end_unix=-1;




        public Annotation()
        {
            this.activities = new ActivityList();
        }

        #region Access Properties
        public ActivityList Activities
        {
            get
            {
                return this.activities;
            }
            set
            {
                this.activities = value;
            }
        }
        public string _EndDate
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

        public string _StartDate
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

        public double _StartUnix
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

        public double _EndUnix
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
        public int _StartHour
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

        public int _StartMinute
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

        public int _StartSecond
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


        public int _StartMillisecond
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

        public int _EndMillisecond
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

        public int _EndHour
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

        public int _EndMinute
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

        public int _EndSecond
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
        #endregion Access Properties

        public string ToXML()
        {
            string xml = "";
            xml += "<" + ANNOTATION_ELEMENT + " " + STARTDATE_ATTRIBUTE + "=\"" + this.start_date + "\" " +
                ENDDATE_ATTRIBUTE + "=\"" + this.end_date + "\" " + STARTTIME_ATTRIBUTE + "=\"" +
                this.start_hour + ":" + this.start_minute + ":" + this.start_second + "." + this.start_millisecond + "\" " + ENDTIME_ATTRIBUTE + "=\"" +
                this.end_hour + ":" + this.end_minute + ":" + this.end_second + "." + this.end_millisecond + "\">";
            for (int i=0;(i<this.activities.Count);i++)
                xml += "<" + VALUE_ELEMENT + " " + LABEL_ATTRIBUTE + "=\"" + this.activities[i]._Name + "\" " +
                    CATEGORY_ATTRIBUTE + "=\"" + this.activities[i]._Category + "\" />\n";
            xml += "</" + ANNOTATION_ELEMENT + ">\n";
            return xml;
        }

        public string ToCSV()
        {
            string csv = "";
            csv += this.start_date + "," + this.end_date + ",";
            for (int i = 0; (i < this.activities.Count); i++)
                csv += "," + this.activities[i]._Name;            
            return csv;
        }
        
        
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.LoadXml(xml);
            XmlNode iNode = dom.DocumentElement;
            int index = 0;
            if (iNode.Name == ANNOTATION_ELEMENT)
            {
                //parsing category attributes
                foreach (XmlAttribute iAttribute in iNode.Attributes)
                {
                    if (iAttribute.Name == DATE_ATTRIBUTE)
                    {
                        //parse date
                        string p = @"(\d+)/(\d+)/(\d+)";
                        Match m = Regex.Match(iAttribute.Value, p);
                        if (m.Groups.Count == 4)
                        {
                            this.start_month = this.end_month = Convert.ToInt32(m.Groups[1].Value);
                            this.start_day = this.end_day = Convert.ToInt32(m.Groups[2].Value);
                            this.start_year = this.end_year = Convert.ToInt32(m.Groups[3].Value);

                        }
                        else
                            throw new Exception("Error parsing " + DATE_ATTRIBUTE + ". " + iAttribute.Value);
                    }
                    else if (iAttribute.Name == STARTTIME_ATTRIBUTE)
                    {
                        //parse date   
                        string p = @"(\d+):(\d+):(\d+)([.](\d+))?";
                        Match m = Regex.Match(iAttribute.Value, p);
                        this.start_hour = Convert.ToInt32(m.Groups[1].Value);
                        this.start_minute = Convert.ToInt32(m.Groups[2].Value);
                        
                        this.start_second = Convert.ToInt32(m.Groups[3].Value);
                        if (m.Groups[5].Value.Length > 0)
                            this.start_millisecond = Convert.ToInt32(m.Groups[5].Value);                        

                    }

                    else if (iAttribute.Name == ENDTIME_ATTRIBUTE)
                    {
                        //parse date
                        string p = @"(\d+):(\d+):(\d+)([.](\d+))?";
                        Match m = Regex.Match(iAttribute.Value, p);

                        this.end_hour = Convert.ToInt32(m.Groups[1].Value);
                        this.end_minute = Convert.ToInt32(m.Groups[2].Value);
                        this.end_second = Convert.ToInt32(m.Groups[3].Value);
                        
                        this.end_millisecond = 0;
                        if (m.Groups[5].Value.Length > 0)
                            this.end_millisecond = Convert.ToInt32(m.Groups[5].Value);
                    }
                    else if (iAttribute.Name == STARTDATE_ATTRIBUTE)
                    {
                        //parse date
                        //2008-06-17 14:03:42-07:00
                        string p = @"^(\d+)-(\d+)-(\d+)\s+(\d+):(\d+):(\d+)";
                        Match m = Regex.Match(iAttribute.Value, p);
                        if (m.Groups.Count == 7)
                        {
                            this.start_date = m.Groups[0].Value.Substring(0, 10);
                            
                            this.start_month = Convert.ToInt32(m.Groups[2].Value);
                            this.start_day = Convert.ToInt32(m.Groups[3].Value);
                            this.start_year = Convert.ToInt32(m.Groups[1].Value);
                            this.start_hour = Convert.ToInt32(m.Groups[4].Value);
                            this.start_minute = Convert.ToInt32(m.Groups[5].Value);
                            this.start_second = Convert.ToInt32(m.Groups[6].Value);
                            this.start_millisecond = 0;
                            

                        }
                        else
                            throw new Exception("Error parsing " + STARTDATE_ATTRIBUTE + ". " + iAttribute.Value);
                    }
                    else if (iAttribute.Name == ENDDATE_ATTRIBUTE)
                    {
                        //parse date
                        string p = @"^(\d+)-(\d+)-(\d+)\s+(\d+):(\d+):(\d+)";
                        Match m = Regex.Match(iAttribute.Value, p);
                        if (m.Groups.Count == 7)
                        {
                            //added
                            this.end_date = m.Groups[0].Value.Substring(0, 10);

                            this.end_month = Convert.ToInt32(m.Groups[2].Value);
                            this.end_day = Convert.ToInt32(m.Groups[3].Value);
                            this.end_year = Convert.ToInt32(m.Groups[1].Value);
                            this.end_hour = Convert.ToInt32(m.Groups[4].Value);
                            this.end_minute = Convert.ToInt32(m.Groups[5].Value);
                            this.end_second = Convert.ToInt32(m.Groups[6].Value);
                            this.end_millisecond = 0;

                        }
                        else
                            throw new Exception("Error parsing " + ENDDATE_ATTRIBUTE + ". " + iAttribute.Value);
                    }

                    if ((this.start_unix < 0) && (this.start_year > 0) && (this.start_hour > 0) && (iAttribute.Name == STARTTIME_ATTRIBUTE))
                    {
                        DateTime dt=new DateTime(this.start_year,this.start_month,this.start_day,this.start_hour,this.start_minute,this.start_second,this.start_millisecond);
                        this.start_unix = WocketsTimer.GetUnixTime(dt);
                    }

                    if ((this.end_unix < 0) && (this.end_year > 0) && (this.end_hour > 0) && (iAttribute.Name == ENDTIME_ATTRIBUTE))
                    {
                        DateTime dt = new DateTime(this.end_year, this.end_month, this.end_day, this.end_hour, this.end_minute, this.end_second,this.end_millisecond);
                        this.end_unix = WocketsTimer.GetUnixTime(dt);
                    }
                }
                this.activities = new ActivityList();
                foreach (XmlNode jNode in iNode.ChildNodes)
                {
                    Activity activity = new Activity();
                    foreach (XmlAttribute jAttribute in jNode.Attributes)
                    {
                        
                        if (jAttribute.Name == LABEL_ATTRIBUTE)
                            activity._Name = jAttribute.Value.Replace("A - ", "").Replace("A- ", "").Replace(' ', '-').Replace(',', '_').ToLower();
                        else if (jAttribute.Name == CATEGORY_ATTRIBUTE)
                            activity._Category = jAttribute.Value;
                    }
                    this.activities.Insert(index++, activity);
                }               
            }
        }


        public Annotation copy()
        {
            Annotation ann = new Annotation();

            foreach (Activity act in activities)
            {
                ann.activities.Add(act);
            }

            ann._StartHour= start_hour;
            ann._StartMinute = start_minute;
            ann._StartSecond = start_second;
            ann._StartMillisecond = start_millisecond;
            ann._StartUnix = start_unix;
            ann._StartDate = start_date;
            
            ann._EndDate = end_date;
            ann._EndHour = end_hour;
            ann._EndMinute = end_minute;
            ann._EndSecond = end_second;
            ann._EndMillisecond = end_millisecond;
            ann._EndUnix = end_unix;
            

            return ann;
        }
    
    
    }
}
