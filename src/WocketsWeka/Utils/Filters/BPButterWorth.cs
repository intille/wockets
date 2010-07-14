using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace WocketsWeka.Utils.Filters
{
    public class BPButterworth : BandPass
    {
        public SamplingRates _SamplingRate;
        int sr = 0;
      

        string filename = "BW_BP_SR_";
        ButterWorthDF bbutter;

        public BPButterworth(Frequency lowFrequency, Frequency highFrequency, Order order, SamplingRates sr,double[] a,double[] b) :
            base(lowFrequency, highFrequency, order)
        {
            _SamplingRate = sr;
            this.a = a;
            this.b = b;
            xv = new double[((int)order) * 2 + 1];
            yv = new double[((int)order) * 2 + 1];
        }
        public BPButterworth(Frequency lowFrequency, Frequency highFrequency, Order order, SamplingRates sr): 
            base(lowFrequency,highFrequency,order)
        {           
            
        
            _SamplingRate = sr;
            a = new double[((int)order) *2 +1];
            b = new double[ ((int)order) * 2 + 1];
            filename+= ((int)_SamplingRate)+"_ORDER_"+((int)order) +"_LF_" + ( (((int)lowFrequency)%10 ==0) ? (((int)lowFrequency)/10).ToString(): (((double)lowFrequency)/10 ).ToString("0.0"))+".csv";
            TextReader tr = new StreamReader(@"C:\Users\albinali\Desktop\FitFriends\Filters\"+filename);
            int skip = ((((int)highFrequency) - ((int)lowFrequency)-1) * 2);
            while (skip-- != 0)
                tr.ReadLine();
            string[] tokens = tr.ReadLine().Split(new char[1] { ',' });
            for (int i = 0; (i < tokens.Length); i++)            
                a[i] = Convert.ToDouble(tokens[i]);
     
            tokens = tr.ReadLine().Split(new char[1] { ',' });
            for (int i = 0; (i < tokens.Length); i++)
                b[i] = Convert.ToDouble(tokens[i]);

            bbutter = new ButterWorthDF();
            int[] vals = bbutter.ccof_bwbp(((int)order));

            tr.Close();
            xv = new double[((int)order)*2 + 1];
            yv = new double[((int)order)*2 + 1];
        }

      
    }
}
