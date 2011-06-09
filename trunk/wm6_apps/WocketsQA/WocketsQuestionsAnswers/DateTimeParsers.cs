using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Wockets
{
    public static class DateTimeParsers
    {
        public const string DATETIME_MASK = "yyyy-MM-dd HH:mm:ss.fff";
        public const string DATE_MASK = "yyyy-MM-dd";
        public const string HOUR_MASK = "HH";

        public static string GetDateTimeString(DateTime aDateTime)
        {
            return aDateTime.ToString(DATETIME_MASK);
        }

        public static string GetTimeOfDayString(DateTime aDateTime)
        {
            if (aDateTime.TimeOfDay.ToString().Length >= 12)
                return aDateTime.TimeOfDay.ToString().Substring(0, 12);
            else if (aDateTime.TimeOfDay.ToString().Length < 12)
                return aDateTime.TimeOfDay.ToString().Substring(0, 8) + ".000";
            else
                return "";
        }

        public static DateTime DateTimeParse(string DateString)
        {
            string[] dateArray = DateString.Split(' ');
            string[] timeArray = dateArray[dateArray.Length - 1].Split(':');
            string[] secondArray = timeArray[2].Split('.');
            string[] newDateArray = new string[3];
            if (dateArray.Length > 1)                       //Create array to store date
                newDateArray = dateArray[0].Split('-');
            else                                            //Handle cases where date component is not defined in string
                newDateArray = new string[] { "1999", "01", "01" };
            return new DateTime(Convert.ToInt32(newDateArray[0]), Convert.ToInt32(newDateArray[1]), Convert.ToInt32(newDateArray[2]), Convert.ToInt32(timeArray[0]), Convert.ToInt32(timeArray[1]), Convert.ToInt32(secondArray[0]), Convert.ToInt32(secondArray[1]));
        }

        public static DateTime UnixTimeParse(string UnixString)
        {
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
            string[] unixArray = UnixString.Split('.');
            double milliseconds = 0;
            milliseconds = double.Parse(unixArray[0]);
            DateTime newTime = origin.AddMilliseconds(milliseconds);
            return newTime;
        }

        public static DateTime ConvertFromUnixTimestamp(double unixTime)
        {
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
            return origin.AddSeconds(unixTime);
        }


        public static double ConvertToUnixTimestamp(DateTime aDateTime)
        {
            DateTime origin = new DateTime(1970, 1, 1, 0, 0, 0, 0);
            TimeSpan diff = aDateTime - origin;
            return Math.Floor(diff.TotalSeconds);
        }



    }
}
