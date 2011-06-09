using System;

using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils.Filters
{
    public abstract class LowPass : Filter
    {
        public Frequency _CornerFrequency;


        public LowPass(Frequency low_frequency, Order order)
            : base(Type.LowPass, order)
        {
            
            _CornerFrequency = low_frequency;            
        }
    }
}
