using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace WocketsWeka.Utils.Filters
{
    public class LPButterworth : LowPass
    {
        public SamplingRates _SamplingRate;
        int sr = 0;
        string filename = "BW_LP_SR_";
  

        public LPButterworth(Frequency lowFrequency, Order order, SamplingRates sr, double[] a, double[] b) :
            base(lowFrequency, order)
        {
            _SamplingRate = sr;
            this.a = a;
            this.b = b;
            this.xv = new double[((int)order)  + 1];
            this.yv = new double[((int)order)  + 1];
        }
  
    }
}
