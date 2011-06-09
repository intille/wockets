using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.Data;
#if !PocketPC
using System.Data.OleDb;
#endif
using System.Globalization;
using System.IO;
using System.Reflection;

namespace WocketsWeka.Utils
{
    public class TextNumberFormat
    {
        // Declaration of fields
        private NumberFormatInfo numberFormat;

        private enum formatTypes
        {
            General,
            Number,
            Currency,
            Percent
        } ;

        private int numberFormatType;
        private bool groupingActivated;
        private string separator;
        private int digits;

        // CONSTRUCTORS
        public TextNumberFormat()
        {
            numberFormat = new NumberFormatInfo();
            numberFormatType = (int)formatTypes.General;
            groupingActivated = true;
            separator = GetSeparator((int)formatTypes.General);
            digits = 3;
        }

        private TextNumberFormat(formatTypes theType, int digits)
        {
            numberFormat = NumberFormatInfo.CurrentInfo;
            numberFormatType = (int)theType;
            groupingActivated = true;
            separator = GetSeparator((int)theType);
            this.digits = digits;
        }

        private TextNumberFormat(formatTypes theType, CultureInfo cultureNumberFormat, int digits)
        {
            numberFormat = cultureNumberFormat.NumberFormat;
            numberFormatType = (int)theType;
            groupingActivated = true;
            separator = GetSeparator((int)theType);
            this.digits = digits;
        }

        public static TextNumberFormat GetTextNumberInstance()
        {
            TextNumberFormat instance = new TextNumberFormat(formatTypes.Number, 3);
            return instance;
        }

        public static TextNumberFormat GetTextNumberCurrencyInstance()
        {
            TextNumberFormat instance = new TextNumberFormat(formatTypes.Currency, 3);
            return instance;
        }

        public static TextNumberFormat GetTextNumberPercentInstance()
        {
            TextNumberFormat instance = new TextNumberFormat(formatTypes.Percent, 3);
            return instance;
        }

        public static TextNumberFormat GetTextNumberInstance(CultureInfo culture)
        {
            TextNumberFormat instance = new TextNumberFormat(formatTypes.Number, culture, 3);
            return instance;
        }

        public static TextNumberFormat GetTextNumberCurrencyInstance(CultureInfo culture)
        {
            TextNumberFormat instance = new TextNumberFormat(formatTypes.Currency, culture, 3);
            return instance;
        }

        public static TextNumberFormat GetTextNumberPercentInstance(CultureInfo culture)
        {
            TextNumberFormat instance = new TextNumberFormat(formatTypes.Percent, culture, 3);
            return instance;
        }



        public override bool Equals(Object textNumberObject)
        {
            return Equals((Object)this, textNumberObject);
        }

        public string FormatDouble(double number)
        {
            if (groupingActivated)
            {
                return number.ToString(GetCurrentFormatString() + digits, numberFormat);
            }
            else
            {
                return (number.ToString(GetCurrentFormatString() + digits, numberFormat)).Replace(separator, string.Empty);
            }
        }

        public string FormatLong(long number)
        {
            if (groupingActivated)
            {
                return number.ToString(GetCurrentFormatString() + digits, numberFormat);
            }
            else
            {
                return (number.ToString(GetCurrentFormatString() + digits, numberFormat)).Replace(separator, string.Empty);
            }
        }

        #if !PocketPC
        public static CultureInfo[] GetAvailableCultures()
        {
            return CultureInfo.GetCultures(CultureTypes.AllCultures);
        }
#endif
        public override int GetHashCode()
        {
            return GetHashCode();
        }

        private string GetCurrentFormatString()
        {
            string currentFormatString = "n"; //Default value
            switch (numberFormatType)
            {
                case (int)formatTypes.Currency:
                    currentFormatString = "c";
                    break;

                case (int)formatTypes.General:
                    currentFormatString = string.Format("n{0}", numberFormat.NumberDecimalDigits);
                    break;

                case (int)formatTypes.Number:
                    currentFormatString = string.Format("n{0}", numberFormat.NumberDecimalDigits);
                    break;

                case (int)formatTypes.Percent:
                    currentFormatString = "p";
                    break;
            }
            return currentFormatString;
        }

        private string GetSeparator(int numberFormatType)
        {
            string separatorItem = " "; //Default Separator

            switch (numberFormatType)
            {
                case (int)formatTypes.Currency:
                    separatorItem = numberFormat.CurrencyGroupSeparator;
                    break;

                case (int)formatTypes.General:
                    separatorItem = numberFormat.NumberGroupSeparator;
                    break;

                case (int)formatTypes.Number:
                    separatorItem = numberFormat.NumberGroupSeparator;
                    break;

                case (int)formatTypes.Percent:
                    separatorItem = numberFormat.PercentGroupSeparator;
                    break;
            }
            return separatorItem;
        }

        public bool GroupingUsed
        {
            get { return (groupingActivated); }
            set { groupingActivated = value; }
        }

        public int Digits
        {
            get { return digits; }
            set { digits = value; }
        }


    }
}
