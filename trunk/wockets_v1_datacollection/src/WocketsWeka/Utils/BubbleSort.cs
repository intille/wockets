using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils
{
    public class BubbleSort
    {

          double[] a;
    int[] indices;  //indices of original positions
    int nmax;

    //temporal variables
    double T;
    int i,j,T2;



        public BubbleSort(double[] arraytoSort, int nmax, bool deepcopy)
        {
            this.nmax = nmax;


            if (deepcopy)
            {
                //making deep copy of array A
                this.a = new double[arraytoSort.Length];
                Array.Copy(arraytoSort, 0, this.a, 0, arraytoSort.Length);
            }
            else
            {
                //using same array to store results
                this.a = arraytoSort;
            }


            //creating array containing array indices
            indices = new int[a.Length];
            for (int i = 0; i < a.Length; i++) indices[i] = i;


        }


        public void sort()
        {

            for (i = a.Length; --i >= a.Length- nmax; )
            {
                bool flipped = false;

                for (j = 0; j < i; j++)
                {

                    if (a[j] > a[j + 1])
                    {
                        //swapping value
                        T = a[j];
                        a[j] = a[j + 1];
                        a[j + 1] = T;

                        //swapping index
                        T2 = indices[j];
                        indices[j] = indices[j + 1];
                        indices[j + 1] = T2;

                        flipped = true;
                    }

                }

                if (!flipped)
                {
                    return;
                }
            }
        }



    //return array indices after sorting
        public int[] getIndices()
        {
            return indices;
        }


    //returns the sorted array
        public double[] getSortedArray()
        {
            return this.a;
        }
    }
}
