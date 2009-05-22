using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;
//using FixedPoint;
using WocketsWeka.Utils;

namespace WocketsWeka.core
{
    /// <summary>
    /// Calculates the FFT for a Qm.n input array
    /// </summary>
    public class FFT
    {
        private static int fftSize;        
        private static IntPtr a1 = new IntPtr();
        private static IntPtr a2 = new IntPtr();
        private static IntPtr a3 = new IntPtr();
        private static double[] magnitude;
        private static double[] phase;
        private static double normEntropy = 0.0;
        private static double[] frequencies;

        private static double energy;
        private static double entropy;
      

        private static int maxFrequencies;
        private static double[] maxFrequenciesFeatures;
        private static int[] maxFrequenciesIndicies;

        [DllImport("FixedPointFFT.dll", EntryPoint = "ComputeFFT")]
        private static extern int ComputeFFT();

        [DllImport("FixedPointFFT.dll", EntryPoint = "BenchmarkFFT")]
        private static extern int BenchmarkFFT();

        [DllImport("FixedPointFFT.dll", EntryPoint = "ComputeInvFFT")]
        private static extern int ComputeInvFFT();

        [DllImport("FixedPointFFT.dll", EntryPoint = "InitializeBuffers")]
        private static extern void InitializeBuffers(ref IntPtr a1, ref IntPtr a2, ref IntPtr a3, int size);

        [DllImport("FixedPointFFT.dll", EntryPoint = "CleanupBuffers")]
        private static extern void CleanupBuffers();


        public static void Initialize(int size,int maxFrequencies)
        {
            FFT.fftSize = (int)Math.Pow(2,size);
            FFT.magnitude = new double[fftSize/2];
            FFT.phase = new double[fftSize/2];

            //initialize for max frequency array features
            FFT.maxFrequencies = maxFrequencies;
            FFT.maxFrequenciesFeatures = new double[FFT.maxFrequencies * 2];
            FFT.maxFrequenciesIndicies = new int[FFT.maxFrequencies];
            //double[] sorted = new double[FFT.magnitude.Length - 1];

            //Calculate the normalization factor for entropy          
            double val = 1.0 / (fftSize - 1);
            for (int i = 1; i < fftSize; i++)
            {  //from 1 because there dc component is not taken into account
                if (val == 0.0) val = 1; //avoid zero values
                normEntropy += val * (Math.Log(val) / Math.Log(2));
            }
            normEntropy = -1.0 * FFT.normEntropy;


            //need to be checked
            //Creating an evenly space frequency vector for each unique point in the FFT
            //Calculate frequencies
            double Fs = FFT.fftSize;
            double inc = 1 / (Math.Floor((double)(FFT.fftSize / 2) - 1));
            val=0.0;
            FFT.frequencies = new double[FFT.fftSize/ 2 - 1];
            for(int i=0;i<FFT.frequencies.Length;i++)
            {
                val += inc;
                FFT.frequencies[i] = val * Fs/2.0;
            }

            //place holder for indicies without the DC component
            FFT.maxFrequenciesIndicies = new int[FFT.magnitude.Length - 1];

            InitializeBuffers(ref a1, ref a2, ref a3,size);
        }

        public static void Calculate(int[] input)
        {
            if ((input.Length & (input.Length - 1)) != 0)
                throw new Exception("FFT input not power of 2.");
            unsafe
            {
                int* t = (int*)a1.ToInt32();
                for (int i = 0; (i < input.Length); i++)
                    *(t + i) = input[i];

            }
            ComputeFFT();
            FFT.CalculateMagnitudeAngle();
            FFT.ComputeEnergy();

            //WARNING: The frequencies has to be calculated last, because we are sorting
            // the magnitude data structures that may impact other features.
            //This is done for efficiency reasons to avoid copying the FFT array
            FFT.ComputeMaximumFrequencies();

            //int[] result = new int[fftSize + 2];
            //unsafe
            //{
            //    int* t2 = (int*)a2.ToInt32();
            //    for (int i = 0; (i < fftSize + 2); i++)
            //        result[i] = ((int)*(t2 + i));
            //}
            //return result;
        }


        private static void CalculateMagnitudeAngle()
        {
            unsafe
            {
                int* fft = (int*)a2.ToInt32();
                double real=0,imag=0;
                int dataLength=FFT.fftSize/2;
                for (int i = 0; (i < dataLength); i++)
                {
                    real=(double) ((int)*(fft + (i * 2)));
                    imag=(double) ((int)*(fft + (i * 2) + 1));
                    FFT.magnitude[i] = Math.Sqrt(real * real + imag * imag);
                    if ((real == 0) && (imag == 0))
                        FFT.phase[i] = 0.0;
                    else
                        FFT.phase[i] = Math.Atan(imag / real) * 180.0 / Math.PI;

                    if ((real < 0.0) && (imag == 0.0))
                        phase[i] = 180.0;
                    else if ((real < 0.0) && (imag == -0.0))
                        phase[i] = -180.0;
                    else if ((real < 0.0) && (imag > 0.0))
                        phase[i] += 180.0;
                    else if ((real < 0.0) && (imag < 0.0))
                        phase[i] += -180;
                }
            }
        }

        public static double[] Magnitudes
        {
            get
            {
                return FFT.magnitude;
            }
        }

        public static double[] PhaseAngles
        {
            get
            {
                return FFT.phase;
            }
        }

        public static double Energy
        {
            get
            {
                return FFT.energy;
            }
        }

        public static double Entropy
        {
            get
            {
                return FFT.entropy;
            }
        }

        public static double[] MaximumFrequencies
        {
            get
            {
                return FFT.maxFrequenciesFeatures;
            }
        }

        private static void ComputeEnergy()
        {
            FFT.energy = 0;

            for (int i = 1; (i < FFT.magnitude.Length); i++)
                FFT.energy += FFT.magnitude[i] * FFT.magnitude[i];       
        }

        private static void ComputeEntropy()
        {
           double  sum = 0;
            for (int i= 1; i < FFT.magnitude.Length; i++)            
                sum += FFT.magnitude[i];           

            double val = 0,H = 0;
            for (int i = 1; i < FFT.magnitude.Length; i++)
            {
                val = FFT.magnitude[i] / sum;
                if (val == 0.0) val = 1; //avoid zero values
                H += val * (Math.Log(val) / Math.Log(2));
            }
            H = -1.0 * H;

            H = H / FFT.normEntropy;

            if (Double.IsNaN(H))
                H = 0;

            FFT.entropy=H;

        }

        private static void ComputeMaximumFrequencies()
        {
            //The code below is 100% correct, not very efficient though
            double[] sorted = new double[FFT.magnitude.Length - 1];
            Array.Copy(FFT.magnitude, 1, sorted, 0, FFT.magnitude.Length - 1);
            BubbleSort sorter = new BubbleSort(sorted, maxFrequencies, false);
            sorter.sort();

            int i = 0;
            for (int j = FFT.frequencies.Length - 1; j > FFT.frequencies.Length - 1 - FFT.maxFrequencies; j--)
            {
                FFT.maxFrequenciesFeatures[i * 2] = FFT.frequencies[sorter.getIndices()[j]];
                FFT.maxFrequenciesFeatures[i * 2 + 1] = sorter.getSortedArray()[j];
                i++;
            }

            //A more efficient version that requires more testing

            ////Initialize the indicies array 
            //for (int i = 0; i < FFT.magnitude.Length - 1; i++) FFT.maxFrequenciesIndicies[i] = i;

            ////Bubble sort only FFT.maxFrequencies, i.e determine the highest magnitudes and frequencies
            //int k = 0;
            //for (int i = FFT.magnitude.Length; --i >= FFT.magnitude.Length - FFT.maxFrequencies; )
            //{
            //    bool flipped = false;

            //    //skip the first element DC component
            //    for (int j = 1; j < i; j++)
            //    {
            //        if (FFT.magnitude[j] > FFT.magnitude[j + 1])
            //        {
            //            //swapping value
            //            double T  = FFT.magnitude[j];                        
            //            FFT.magnitude[j] = FFT.magnitude[j + 1];
            //            FFT.magnitude[j + 1] = T;

            //            //swapping index
            //            int T2 = FFT.maxFrequenciesIndicies[j - 1];
            //            FFT.maxFrequenciesIndicies[j - 1] = FFT.maxFrequenciesIndicies[j];
            //            FFT.maxFrequenciesIndicies[j] = T2;
            //            flipped = true;
            //        }

            //    }
            //    FFT.maxFrequenciesFeatures[k * 2 + 1] = FFT.magnitude[i];
            //    FFT.maxFrequenciesFeatures[k * 2] = FFT.frequencies[FFT.maxFrequenciesIndicies[i - 1]];
            //    k++;
            //    if (!flipped)
            //    {
            //        return null;
            //    }
            //}
           
            
            //return FFT.maxFrequenciesFeatures;
        }


        public static int[] Invert(int[] input)
        {
            unsafe
            {
                int* t = (int*)a2.ToInt32();
                for (int i = 0; (i < input.Length); i++)
                    *(t + i) = input[i];

            }
            ComputeInvFFT();

            int[] result = new int[fftSize];
            unsafe
            {
                int* t3 = (int*)a3.ToInt32();
                for (int i = 0; (i < fftSize); i++)
                    result[i] = ((int)*(t3 + i));

            }

            return result;

        }

        public static void Invert()
        {
            ComputeInvFFT();
        }

  

        public static void Cleanup()
        {
            CleanupBuffers();
        }

        public static string toString()
        {
            string s = "";
            unsafe
            {
                int* t1 = (int*)a1.ToInt32();
                int* t2 = (int*)a2.ToInt32();
                int* t3 = (int*)a3.ToInt32();
                for (int i = 0; (i < 9); i++)
                    s += " <" + ((int)*(t1 + i)) .ToString() + "," + ((int)*(t2 + (i * 2))).ToString() + "," + ((int)*(t2 + (i * 2)+1)).ToString()+ "," + ((int)*(t3 + i)).ToString() + "> ";

            }
            return new String(s.ToCharArray());

        }
    }



}
