using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Summary
{
    public class ActivitySummary
    {
        private string name;
        private double unixStart;
        private double unixEnd;
        private int percent;

        public ActivitySummary()
        {
        }

        public string Name
        {
            get
            {
                return this.name;
            }

            set
            {
                this.name = value;
            }
        }

        public double StartTime
        {
            get
            {
                return this.unixStart;
            }
            set
            {
                this.unixStart = value;
            }
        }

        public double EndTime
        {
            get
            {
                return this.unixEnd;
            }
            set
            {
                this.unixEnd = value;
            }
        }

        public int Percent
        {
            get
            {
                return this.percent;
            }

            set
            {
                this.percent = value;
            }
        }

 
        public string toString()
        {
            string output = "<" + Constants.ACTIVITY_ELEMENT + ">\n";
            output += "<" + Constants.NAME_ATTRIBUTE + "=\"" + this.name + "\" />\n";
            output += "<" + Constants.START_TIME_ATTRIBUTE + "=\"" + this.StartTime + "\" " + Constants.END_TIME_ATTRIBUTE + "=\"" + this.EndTime + "\"" + " />\n";
            output += "<" + Constants.PERCENT_ELEMENT + "=\"" + this.percent + "\" />\n";
            output += "</" + Constants.ACTIVITY_ELEMENT + ">\n";
            return output;
        }
    }
}
