using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils.Filters
{
    public abstract class Filter
    {
        public Type _Type;
        public Order _Order;
        protected int order;
        public bool _Initialized = false;
        protected double[] xv;
        protected double[] yv;
        protected double[] a;
        protected double[] b;       

        public Filter(Type type, Order order)
        {
            _Type = type;
            _Order = order;
        }



        public double Apply(double data)
        {
            double filtered = 0;

            int j = 0;
            for (; (j < xv.Length - 1); j++)
                xv[j] = xv[j + 1];
            xv[j] = data;

            j = 0;
            for (; (j < yv.Length - 1); j++)
                yv[j] = yv[j + 1];
            yv[j] = 0;


            for (int k = 0; (k < xv.Length); k++)
                yv[j] += b[k] * xv[k];
            for (int k = 1; (k < yv.Length); k++)
                yv[j] -= a[k] * yv[yv.Length - k - 1];

            filtered = yv[j];

            return filtered;
        }

        public double[] Apply(double[] data)
        {
            double[] filtered = new double[data.Length];
            for (int i = 0; (i < data.Length); i++)
            {
                int j = 0;
                for (; (j < xv.Length - 1); j++)
                    xv[j] = xv[j + 1];
                xv[j] = data[i];

                j = 0;
                for (; (j < yv.Length - 1); j++)
                    yv[j] = yv[j + 1];
                yv[j] = 0;


                for (int k = 0; (k < xv.Length); k++)
                    yv[j] += b[k] * xv[k];
                for (int k = 1; (k < yv.Length); k++)
                    yv[j] -= a[k] * yv[yv.Length - k - 1];

                filtered[i] = yv[j];
            }
            return filtered;
        }
    }
}
