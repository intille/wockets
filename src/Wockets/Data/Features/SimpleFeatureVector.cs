using System;
using System.Collections.Generic;
using System.Text;
using WocketsWeka.Utils;
using Wockets;
using Wockets.Data.Configuration;
using Wockets.Data.Annotation;
using Wockets.Data.Accelerometers;
using WocketsWeka.Utils.Filters;

namespace Wockets.Data.Features
{
    public class SimpleFeatureVector: FeatureVector
    {
        private  double[][] raw;
        private int raw_rows_size;
        private int raw_columns_size;
        public int _Length = 0;
        private int num_wockets;
        private int sr;
        private int input_power;

        private const int FFT_MAX_FREQUENCIES = 2;

        //Vectors to store intermidate values
        private double[][] standardized;
        private double[][] standardizedn;
        private double[][] lpData;
        private double[][] bpData;
        private double[] means;
        private double[] meanslp;
        private double[] meansbp;
        private static int[] inputFFT;

        //Filters
        public bool _Filtered=true;
        private int iterations_tostabilize = 0;
        private BPButterworth[] bpFilters;
        private LPButterworth[] lpFilters;

        private double[] bpb = new double[5] { 0.0745, 0.0, -0.1490, 0.0, 0.0745 };
        private double[] bpa = new double[5] { 1.0000, -3.0584, 3.5224, -1.8552, 0.3915 };

        private double[] lpb = new double[3] { 0.0002973, 0.0005945, 0.0002973 };
        private double[] lpa = new double[3] { 1.0000, -1.9506, 0.9518 };

        //Feature Labels
        public string[] _Names;

        public bool _Initialized = false;

        private int[] lastHead;


        public SimpleFeatureVector(int num_wockets, int raw_length, int sr)
        {
            this.num_wockets = num_wockets;
            this.sr = sr;
            this.raw_rows_size = num_wockets * 3;
            this.input_power = Wockets.Utils.Math.NextPower2(raw_length-1);
            this.raw_columns_size = (int) Math.Pow(2.0, this.input_power);
            this._Length = this.raw_columns_size;
            this.lastHead = new int[num_wockets];

            //Calculate the number of features in a simple feature vector
            int num_features = this.raw_rows_size; // number of distances
            num_features += 1; //total mean;
            num_features += this.raw_rows_size; // number of variances
            num_features += this.raw_rows_size; // number of ranges
            num_features += 2 * FFT_MAX_FREQUENCIES * this.raw_rows_size; // number of fft magnitudes and frequencies
            num_features += this.raw_rows_size; // number of energies
            num_features += ((this.raw_rows_size * this.raw_rows_size) - this.raw_rows_size) / 2; //correlation coefficients off-di
            num_features += this.raw_rows_size; //RM
            num_features += this.raw_rows_size; //SN
            num_features += this.num_wockets;

            //Allocate the feature vector and labels vector
            this._Values = new double[num_features];
            this._Names = new string[num_features];

            //Initialize raw and filtered data vectors
            raw = new double[this.raw_rows_size][]; // 1 row for each axis
            if (_Filtered)
            {
                lpData = new double[this.raw_rows_size][];
                bpData = new double[this.raw_rows_size][];
            }
            for (int i = 0; (i < num_wockets); i++)
            {
                for (int j = 0; (j < 3); j++)
                {
                    int index = (i * 3) + j;
                    raw[index] = new double[this.raw_columns_size];
                    if (_Filtered)
                    {
                        lpData[index] = new double[this.raw_columns_size];
                        bpData[index] = new double[this.raw_columns_size];
                    }
                    for (int k = 0; (k < raw[index].Length); k++)
                    {
                        raw[index][k] = 0;
                        if (_Filtered)
                        {
                            lpData[index][k] = 0;
                            bpData[index][k] = 0;
                        }
                    }
                }
            }


            //Initialize vectors for storing intermediate  values
            standardized = new double[this.raw_rows_size][];
            for (int i = 0; (i < this.raw_rows_size); i++)
                standardized[i] = new double[this.raw_columns_size];

            standardizedn = new double[this.raw_rows_size][];
            for (int i = 0; (i < this.raw_rows_size); i++)
                standardizedn[i] = new double[this.raw_columns_size];

            if (_Filtered)
            {
                meansbp = new double[this.raw_rows_size];
                meanslp = new double[this.raw_rows_size];
            }                            
            means = new double[this.raw_rows_size];                        
            inputFFT = new int[this.raw_columns_size];
            FFT.Initialize(input_power, FFT_MAX_FREQUENCIES);
            
            //Initialize Filters
            if (_Filtered)
            {
                bpFilters = new BPButterworth[this.raw_rows_size];
                lpFilters = new LPButterworth[this.raw_rows_size];
                for (int i = 0; (i < bpFilters.Length); i++)
                {
                    bpFilters[i] = new BPButterworth(Frequency._1_0Hz, Frequency._20_0Hz, Order.Second, SamplingRates._90Hz, bpa, bpb);
                    lpFilters[i] = new LPButterworth(Frequency._1_0Hz, Order.Second, SamplingRates._90Hz, lpa, lpb);
                }
                iterations_tostabilize = (int)Order.Second * 2;
            }

            _Initialized = true;
  
        }
       
        public override bool Extract()
        {
            int j = 0, i = 0;
            double sumlp = 0, sumbp = 0,sum=0, min = 0, max = 0, total = 0, variance = 0,variancen=0;

            #region Copy data from wockets decoder
            int decoderIndex = 0;
            for (i = 0; (i < CurrentWockets._Controller._Decoders.Count); i++)
            {
                //Hack to make sure we do not compute the FV for the same window
                if (CurrentWockets._Controller._Decoders[i]._Head==lastHead[i])
                    return false;

                int sensorIndex = i * 3;
                int start = CurrentWockets._Controller._Decoders[i]._Head - 1 - this.raw_columns_size;
                if (start < 0)
                    start = CurrentWockets._Controller._Decoders[i]._BufferSize + start;
                decoderIndex = start;
                for (j = 0; (j < this.raw_columns_size); j++)
                {


                    raw[sensorIndex][j] = ((AccelerationData)CurrentWockets._Controller._Decoders[i]._Data[decoderIndex])._X;
                    raw[sensorIndex + 1][j] = ((AccelerationData)CurrentWockets._Controller._Decoders[i]._Data[decoderIndex])._Y;
                    raw[sensorIndex + 2][j] = ((AccelerationData)CurrentWockets._Controller._Decoders[i]._Data[decoderIndex])._Z;
                    decoderIndex++;
                    if (decoderIndex >= CurrentWockets._Controller._Decoders[i]._BufferSize)
                        decoderIndex = 0;
                }

                lastHead[i] = CurrentWockets._Controller._Decoders[i]._Head;
            }

            #endregion Copy data from wockets decoder

            #region Filter the data if needed
            if (_Filtered)
            {
                for (i = 0; (i < raw.Length); i++)
                {
                    bpData[i] = bpFilters[i].Apply(raw[i]);
                    lpData[i] = lpFilters[i].Apply(raw[i]);
                }

                //Don't return a feature vector until the filter stabilizes at the 
                //begining
                if (iterations_tostabilize != 0)
                {
                    iterations_tostabilize--;
                    return false;
                }
            }
            #endregion Filter the data if needed

            #region Calculate feature vector



            i = 0; j = 0;
            int distanceIndex = 0;//number of means on every row + 1 for total mean, 0 based index
            int varianceIndex = distanceIndex + this.raw_rows_size + 1; // add number of distances
            int rangeIndex = varianceIndex + this.raw_rows_size;
            int fftIndex = rangeIndex + this.raw_rows_size;
            int energyIndex = fftIndex + (2 * FFT_MAX_FREQUENCIES * this.raw_rows_size);
            int correlationIndex = energyIndex + this.raw_rows_size; //add number of variances         
            int rmIndex = correlationIndex + ((this.raw_rows_size * this.raw_rows_size) - this.raw_rows_size) / 2;
            int snIndex = rmIndex + this.raw_rows_size;
            int svIndex = snIndex + this.raw_rows_size;
           

            for (i = 0; (i < this._Values.Length); i++)
                this._Values[i] = 0;

            //for good cache locality go through the rows then columns
            for (i = 0; (i < this.raw_rows_size); i++)
            {
                min = 999999999.0;
                max = -999999999.0;

                for (j = 0; (j < this.raw_columns_size); j++)
                {
                    if (_Filtered)
                    {
                        if (bpData[i][j] < min)
                            min = bpData[i][j];
                        if (bpData[i][j] > max)
                            max = bpData[i][j];
                        inputFFT[j] = (int)(bpData[i][j]);
                        sumbp += bpData[i][j];
                        sumlp += lpData[i][j];
                        sum += raw[i][j];
                    }
                    else
                    {
                        if (raw[i][j] < min)
                            min = raw[i][j];
                        if (raw[i][j] > max)
                            max = raw[i][j];
                        inputFFT[j] = (int)(raw[i][j]);
                        sum += raw[i][j];                        
                    }
                }
                if (_Filtered)
                {
                    meansbp[i] = sumbp / this.raw_columns_size;   //mean
                    meanslp[i] = sumlp / this.raw_columns_size;   //mean
                    means[i] = sum / this.raw_columns_size;
                    this._Values[rmIndex++] = meanslp[i];                  
                    total += meansbp[i];  //total mean
                }
                else
                {
                    means[i] = sum / this.raw_columns_size;
                    this._Values[rmIndex++] = means[i];
                    total += means[i];  //total mean
                }



                if ((i + 1) % 3 == 0)
                {
                    if (_Filtered)
                    {
                        this._Values[distanceIndex++] = meanslp[i - 2] - meanslp[i - 1];
                        this._Values[distanceIndex++] = meanslp[i - 2] - meanslp[i];
                        this._Values[distanceIndex++] = meanslp[i - 1] - meanslp[i];
                    }
                    else
                    {
                        this._Values[distanceIndex++] = means[i - 2] - means[i - 1];
                        this._Values[distanceIndex++] = means[i - 2] - means[i];
                        this._Values[distanceIndex++] = means[i - 1] - means[i];
                    }
                }



                //fill variance
                variance = 0;
                for (j = 0; (j < this.raw_columns_size); j++)
                {
                    if (_Filtered)
                    {
                        variance += Math.Pow(bpData[i][j] - meansbp[i], 2);
                        variancen += Math.Pow(raw[i][j] - means[i], 2);
                        //***mean subtracted
                        standardized[i][j] = bpData[i][j] - meansbp[i]; //mean subtracted
                        standardizedn[i][j] = raw[i][j] - means[i]; //mean subtracted
                    }
                    else
                    {
                        variance += Math.Pow(raw[i][j] - means[i], 2);
                        //***mean subtracted
                        standardized[i][j] = raw[i][j] - means[i]; //mean subtracted
                    }

                }
                this._Values[snIndex++] = variance/variancen;
                this._Values[varianceIndex++] = variance / (this.raw_columns_size - 1);

                //calculate the range
                this._Values[rangeIndex++] = Math.Abs(max - min);

                //calculate FFT                
                FFT.Calculate(inputFFT);


                this._Values[energyIndex++] = FFT.Energy;
                double[] maxFreqs = FFT.MaximumFrequencies;

                for (int k = 0; (k < maxFreqs.Length); k++)
                {
                    this._Values[fftIndex++] = maxFreqs[k++];
                    this._Values[fftIndex++] = maxFreqs[k];
                }


                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    for (int w = 0; (w < this.raw_columns_size); w++)
                        this._Values[correlationIndex] += standardized[i][w] * standardized[k][w];
                    this._Values[correlationIndex] /= (this.raw_columns_size - 1);
                    this._Values[correlationIndex] /= Math.Sqrt(this._Values[varianceIndex - 1]);  // ith std deviation
                    this._Values[correlationIndex] /= Math.Sqrt(this._Values[varianceIndex - 1 - (i - k)]);  //kth std deviation 
                    correlationIndex++;
                }

            }

            this._Values[this.raw_rows_size] = total;

            varianceIndex = this.raw_rows_size + 1; // add number of distances
            double sv=0;
            for (i = 0; (i < this.raw_rows_size); i++)
            {
                sv+=this._Values[varianceIndex++];
                if ((i + 1) % 3 == 0)
                {
                    this._Values[svIndex++]=sv;
                    sv=0;
                }
            }
            #endregion Calculate feature vector

            return true;

        }

        public void Cleanup()
        {
            if (_Initialized)
            {
                FFT.Cleanup();
                _Initialized = false;
            }
        }


        public string GetHeader()
        {
            string DISTANCE_ATTRIBUTES = "";
            string TOTAL_ATTRIBUTE = "";
            string VARIANCE_ATTRIBUTES = "";
            string RANGE_ATTRIBUTES = "";
            string FFT_ATTRIBUTES = "";
            string ENERGY_ATTRIBUTES = "";
            string CORRELATION_ATTRIBUTES = "";
            string RM_ATTRIBUTES = "";
            string SN_ATTRIBUTES = "";
            string SV_ATTRIBUTES = "";

            int distanceIndex = 0;//number of means on every row + 1 for total mean, 0 based index
            int varianceIndex = distanceIndex + this.raw_rows_size + 1; // add number of distances
            int rangeIndex = varianceIndex + this.raw_rows_size;
            int fftIndex = rangeIndex + this.raw_rows_size;
            int energyIndex = fftIndex + (2 * FFT_MAX_FREQUENCIES * this.raw_rows_size);
            int correlationIndex = energyIndex + this.raw_rows_size; //add number of variances   
            int rmIndex = correlationIndex + ((this.raw_rows_size * this.raw_rows_size) - this.raw_rows_size) / 2;
            int snIndex = rmIndex + this.raw_rows_size;
            int svIndex = snIndex + this.raw_rows_size;
            

            for (int i = 0; (i < this.raw_rows_size); i++)
            {
                if ((i + 1) % 3 == 0)
                {
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 2) + "_Mean" + (i - 1) + " NUMERIC\n";
                    this._Names[distanceIndex++] = "Dist_Mean" + (i - 2) + "_Mean" + (i - 1);
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 2) + "_Mean" + (i) + " NUMERIC\n";
                    this._Names[distanceIndex++] = "Dist_Mean" + (i - 2) + "_Mean" + (i);
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 1) + "_Mean" + (i) + " NUMERIC\n";
                    this._Names[distanceIndex++] = "Dist_Mean" + (i - 1) + "_Mean" + (i);
                }


                VARIANCE_ATTRIBUTES += "@ATTRIBUTE Variance_" + i + " NUMERIC\n";
                this._Names[varianceIndex++] = "Variance_" + i;


                RANGE_ATTRIBUTES += "@ATTRIBUTE RANGE_" + i + " NUMERIC\n";
                this._Names[rangeIndex++] = "RANGE_" + i;

                RM_ATTRIBUTES += "@ATTRIBUTE RM_" + i + " NUMERIC\n";
                this._Names[rmIndex++] = "RM_" + i;

                SN_ATTRIBUTES += "@ATTRIBUTE SN_" + i + " NUMERIC\n";
                this._Names[snIndex++] = "SN_" + i;

                for (int k = 0; (k < (FFT_MAX_FREQUENCIES * 2)); k++)
                {
                    k++;
                    FFT_ATTRIBUTES += "@ATTRIBUTE FFT_MAX_FREQ" + i + "_" + k + " NUMERIC\n";
                    this._Names[fftIndex++] = "FFT_MAX_FREQ" + i + "_" + k;

                    FFT_ATTRIBUTES += "@ATTRIBUTE FFT_MAX_MAG" + i + "_" + k + " NUMERIC\n";
                    this._Names[fftIndex++] = "FFT_MAX_MAG" + i + "_" + k;

                }

                ENERGY_ATTRIBUTES += "@ATTRIBUTE ENERGY_" + i + " NUMERIC\n";
                this._Names[energyIndex++] = "ENERGY_" + i;


                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    CORRELATION_ATTRIBUTES += "@ATTRIBUTE CORRELATION_" + k + "_" + i + " NUMERIC\n";
                    this._Names[correlationIndex++] = "CORRELATION_" + k + "_" + i;
                }
            }

            TOTAL_ATTRIBUTE += "@ATTRIBUTE TotalMean NUMERIC\n";
            this._Names[distanceIndex] = "TotalMean";

            for (int i = 0; (i < this.num_wockets); i++)
            {
                SV_ATTRIBUTES += "@ATTRIBUTE SV_" +  i + " NUMERIC\n";
                this._Names[svIndex++] =  "SV_" +  i;

            }

            return DISTANCE_ATTRIBUTES + TOTAL_ATTRIBUTE + VARIANCE_ATTRIBUTES + RANGE_ATTRIBUTES +
               FFT_ATTRIBUTES + ENERGY_ATTRIBUTES + CORRELATION_ATTRIBUTES + RM_ATTRIBUTES +SN_ATTRIBUTES + SV_ATTRIBUTES;
        }

        public string toString()
        {
            string s = "";
            int i = 0;

            for (i = 0; (i < this._Values.Length - 1); i++)
                s += this._Values[i].ToString("F2") + ",";
            s += this._Values[i].ToString("F2");
            return s;

        }
    }
}
