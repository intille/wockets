using System;
using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class QuickSort
    {

        public static double[] Sort(double[] a, int i, int j)
        {
            if (i < j)
            {
                int q = Partition(a, i, j);
                a = Sort(a, i, q);
                a = Sort(a, q + 1, j);
            }
            return a;
        }

        private static int Partition(double[] a, int p, int r)
        {
            double x = a[p];
            int i = p - 1;
            int j = r + 1;
            double tmp = 0;
            while (true)
            {
                do
                {
                    j--;
                } while (a[j] > x);
                do
                {
                    i++;
                } while (a[i] < x);
                if (i < j)
                {
                    tmp = a[i];
                    a[i] = a[j];
                    a[j] = tmp;
                }
                else return j;
            }
        } 
    }
}
