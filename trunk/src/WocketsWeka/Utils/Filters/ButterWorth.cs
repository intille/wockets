using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace WocketsWeka.Utils.Filters
{
    public class Butterworth : BandPass
    {
        public SamplingRates _SamplingRate;
        int sr = 0;
        double[] a=new double[5] { 1.00, -3.7856, 5.3793, -3.4016, 0.8079 };
        double[] b;

        double[] xv;
        double[] yv;

        string filename = "BW_BP_SR_";
        ButterWorthDF bbutter;

        public Butterworth(Frequency lowFrequency, Frequency highFrequency, Order order, SamplingRates sr): 
            base(lowFrequency,highFrequency,order)
        {           
            
        
            _SamplingRate = sr;
            //a = new double[((int)order) *2 +1];
            b = new double[ ((int)order) * 2 + 1];
            filename+= ((int)_SamplingRate)+"_ORDER_"+((int)order) +"_LF_" + ( (((int)lowFrequency)%10 ==0) ? (((int)lowFrequency)/10).ToString(): (((double)lowFrequency)/10 ).ToString("0.0"))+".csv";
            TextReader tr = new StreamReader(@"C:\Users\albinali\Desktop\FitFriends\Filters\"+filename);
            string line = "";
            int skip = ((((int)highFrequency) - ((int)lowFrequency)) * 2);
            while (skip-- != 0)
                tr.ReadLine();
            string[] tokens = tr.ReadLine().Split(new char[1] { ',' });
            //for (int i = 0; (i < tokens.Length); i++)
              //  a[i] = Convert.ToDouble(tokens[i]);
            tokens = tr.ReadLine().Split(new char[1] { ',' });
            for (int i = 0; (i < tokens.Length); i++)
                b[i] = Convert.ToDouble(tokens[i]);

            bbutter = new ButterWorthDF();
            int[] vals = bbutter.ccof_bwbp(((int)order));

            for (int i = 0; (i < b.Length); i++)
                b[i] = vals[i];


            tr.Close();
            xv = new double[((int)order)*2 + 1];
            yv = new double[((int)order)*2 + 1];
        }



        public double[] Filter(double[] data)
        {

            double[] filtered = new double[data.Length];
                     
            for (int i = 0; (i < data.Length); i++)
            {
                int j = 0;
                for (; (j < xv.Length-1); j++)
                    xv[j] = xv[j + 1];
                xv[j] = data[i];
                //xv[0] = xv[1]; xv[1] = xv[2]; xv[2] = xv[3]; xv[3] = xv[4];
                //xv[4] = data[i];

                j = 0;
                for (; (j < yv.Length - 1); j++)
                    yv[j] = yv[j + 1];
                yv[j] = 0;// data[i];

               // yv[0] = yv[1]; yv[1] = yv[2]; yv[2] = yv[3]; yv[3] = yv[4];
               // yv[4] = (xv[0] + xv[4]) - 2 * xv[2] -
                 //   a[1] * yv[3] - a[2] * yv[2] - a[3] * yv[1] - a[4] * yv[0];
               
                for (int k=1; (k < yv.Length); k++)
                    yv[j] -= a[k] * yv[yv.Length - k -1];
                for (int k = 0; (k < xv.Length); k++)
                    yv[j] += b[k] * xv[k];

                filtered[i] = yv[j];
            }

            
            return filtered;
        }
      
    }
}
