using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils.Filters
{
    public abstract class BandPass : Filter
    {
        public Frequency _LowCornerFrequency;
        public Frequency _HighCornerFrequency;

        public BandPass(Frequency low_frequency, Frequency high_frequency, Order order)
            : base(Type.BandPass, order)
        {
            if (high_frequency < low_frequency)
                throw new Exception("Bandpass filter error: high frequency needs to be higher than low frequency");
            _LowCornerFrequency = low_frequency;
            _HighCornerFrequency = high_frequency;
        }
    }
}