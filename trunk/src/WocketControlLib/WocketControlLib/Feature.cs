using System;
using System.Collections.Generic;
using System.Text;

namespace WocketControlLib
{
    public class Feature
    {
        private string name;
        private TimeSpan period;
        private int hash;
        private TimeSpan requiredOldness;
        private int versionNumber;

        public Feature(string nameParam, TimeSpan periodParam, TimeSpan requiredOldnessParam, int versionNumberParam) 
        {
            name = nameParam;
            period = periodParam;
            hash = name.GetHashCode() * 17 + period.GetHashCode();
            requiredOldness = requiredOldnessParam;
            versionNumber = versionNumberParam;
        }

        public string Name { get { return name; } }

        public TimeSpan Period { get { return period; } }

        internal TimeSpan RequiredOldness { 
            get { return requiredOldness; }
            set { requiredOldness = value; }
        }
        internal int VersionNumber
        {
            get { return versionNumber; }
            set { versionNumber = value; }
        }

        public override string ToString() { return name + period.ToString(); }

        public override bool Equals(object obj) 
        {
            if (!(obj is Feature))
                return false;
            Feature other = (Feature)obj;
            return (this.name.Equals(other.name) && this.period.Equals(other.period));
        }

        public override int GetHashCode() { return hash; }
    }

    public class FeaturePeriodComparer : Comparer<Feature>
    {
        public static FeaturePeriodComparer instance;
        static FeaturePeriodComparer()
        {
            instance = new FeaturePeriodComparer();
        }
        public override int Compare(Feature x, Feature y)
        {
            if (x.Period == y.Period)
                return 0;
            if (x.Period > y.Period)
                return -1;
            return 1;
        }
    }
}
