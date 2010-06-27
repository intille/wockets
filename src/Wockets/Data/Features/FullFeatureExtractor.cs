using System;
using System.Collections.Generic;
using System.Text;
using WocketsWeka.Utils;
using Wockets;
using Wockets.Data.Configuration;
using Wockets.Data.Annotation;
using Wockets.Data.Accelerometers;
using WocketsWeka.Utils.Filters;
#if (PocketPC)
using Wockets.Utils.IPC.MMF;
#endif
using System.IO;

namespace Wockets.Data.Features
{
    public class FullFeatureExtractor
    {
        private static int extractorSensorCount = 0;
        private static int inputRowSize;
        private static int inputColumnSize;
        private static int fftInterpolationPower;
        private static int fftMaximumFrequencies;
        private static int num_features = 0;

        private static double[] features;
        private static double[][] standardized;
        private static double[][] lpData;
        private static double[][] bpData;
        private static double[] means;
        private static double[] meanslp;
        private static double[] meansbp;
        private static double[] variances;
        private static int[] inputFFT;
        private static string[] arffAttriburesLabels;

        private static WocketsController wocketsController;
        private static WocketsConfiguration configuration;

        //total number of points per interpolated window
        private static int INTERPOLATED_SAMPLING_RATE_PER_WINDOW;
        //space between interpolated samples
        private static double INTERPOLATED_SAMPLES_SPACING;

        //private static int[] EXPECTED_SAMPLING_RATES;
        private static int[] EXPECTED_WINDOW_SIZES;
        private static int[] EXPECTED_GOOD_SAMPLING_RATES;
        private static double[] EXPECTED_SAMPLES_SPACING;

        //window counters and delimiters
        private static double next_window_end = 0;
        private static int total_window_count = 0;
        private static int num_feature_windows = 0;

        //data quality variables
        private static bool isAcceptableLossRate = true;
        private static bool isAcceptableConsecutiveLoss = true;
        private static int unacceptable_window_count = 0;
        private static int unacceptable_consecutive_window_loss_count = 0;


        private static double[][] data;
        private static double[][] interpolated_data;
        private static int[] y_index;
        private static int[] tail;
        private static double[] tailUnixtimestamp;

        private static int discardedLossRateWindows = 0;
        private static int discardedConsecutiveLossWindows = 0;
        private static bool _Initialized = false;

        private static double[] bpb = new double[5] { 0.0745, 0.0, -0.1490, 0.0, 0.0745 };
        private static double[] bpa = new double[5] { 1.0000, -3.0584, 3.5224, -1.8552, 0.3915 };

        private static double[] lpb = new double[3] { 0.0002973, 0.0005945, 0.0002973 };
        private static double[] lpa = new double[3] { 1.0000, -1.9506, 0.9518 };
        private static BPButterworth[] bpFilters;
        private static LPButterworth[] lpFilters;

        public static string[] ArffAttributeLabels
        {
            get
            {
                return FullFeatureExtractor.arffAttriburesLabels;
            }
        }

        public static double[] Features
        {
            get
            {
                return FullFeatureExtractor.features;
            }
        }

#if (PocketPC)
        private static MemoryMappedFileStream[] sdata = null;
        private static MemoryMappedFileStream[] shead = null;
        private static int sdataSize = 0;
        private static byte[] head = new byte[4];
        private static byte[] timestamp = new byte[sizeof(double)];
        private static byte[] acc = new byte[sizeof(short)];
        public static int[] _DecoderTails;

        public static void Initialize(int sensorCount, int samplingRate, WocketsConfiguration configuration, ActivityList activities)
        {
            if (!_Initialized)
            {

                sdata = new MemoryMappedFileStream[sensorCount];
                shead = new MemoryMappedFileStream[sensorCount];
                sdataSize = (int)Wockets.Decoders.Decoder._DUSize * Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE;
                _DecoderTails = new int[sensorCount];

                for (int i = 0; (i < sensorCount); i++)
                    _DecoderTails[i] = 0;

                for (int i = 0; (i < sensorCount); i++)
                {
                    sdata[i] = new MemoryMappedFileStream("\\Temp\\wocket" + i + ".dat", "wocket" + i, (uint)sdataSize, MemoryProtection.PageReadWrite);
                    shead[i] = new MemoryMappedFileStream("\\Temp\\whead" + i + ".dat", "whead" + i, sizeof(int), MemoryProtection.PageReadWrite);

                    sdata[i].MapViewToProcessMemory(0, sdataSize);
                    shead[i].MapViewToProcessMemory(0, sizeof(int));

                    shead[i].Read(head, 0, 4);
                    int currentHead = BitConverter.ToInt32(head, 0);
                    _DecoderTails[i] = currentHead;
                    shead[i].Seek(0, System.IO.SeekOrigin.Begin);
                    sdata[i].Seek((currentHead * (sizeof(double) + 3 * sizeof(short))), System.IO.SeekOrigin.Begin);

                }

                FullFeatureExtractor.configuration = configuration;
                //window counters and delimiters
                next_window_end = 0;
                total_window_count = 0;
                num_feature_windows = 0;

                //data quality variables
                isAcceptableLossRate = true;
                isAcceptableConsecutiveLoss = true;
                unacceptable_window_count = 0;
                unacceptable_consecutive_window_loss_count = 0;


                //Upgrade to handle HR
                extractorSensorCount = sensorCount;
                inputRowSize = sensorCount * 3;
                fftInterpolationPower = configuration._FFTInterpolationPower;
                fftMaximumFrequencies = configuration._FFTMaximumFrequencies;
                inputColumnSize = (int)Math.Pow(2, configuration._FFTInterpolationPower);

                num_features = inputRowSize; // number of distances
                num_features += 1; //total mean;
                num_features += inputRowSize; // number of variances
                num_features += inputRowSize; // number of ranges
                num_features += 2 * configuration._FFTMaximumFrequencies * inputRowSize; // number of fft magnitudes and frequencies
                num_features += inputRowSize; // number of energies
                num_features += ((inputRowSize * inputRowSize) - inputRowSize) / 2; //correlation coefficients off-di


                features = new double[num_features];
                arffAttriburesLabels = new string[num_features];

                standardized = new double[sensorCount * 3][];
                for (int i = 0; (i < inputRowSize); i++)
                    standardized[i] = new double[inputColumnSize];//input[0].Length];

                means = new double[inputRowSize];

                inputFFT = new int[inputColumnSize];
                FFT.Initialize(configuration._FFTInterpolationPower, configuration._FFTMaximumFrequencies);
                //FullFeatureExtractor.wocketsController = wocketsController;

                //Create the ARFF File header
                string arffHeader = "@RELATION wockets\n\n" + GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
                arffHeader += "@ATTRIBUTE activity {";
                for (int i = 0; (i < activities.Count); i++)
                    arffHeader += activities[i]._Name.Replace(' ', '_') + ",";
                arffHeader += "unknown}\n";
                arffHeader += "\n@DATA\n\n";


                //total number of points per interpolated window
                INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, configuration._FFTInterpolationPower); //128;  

                //space between interpolated samples
                INTERPOLATED_SAMPLES_SPACING = (double)configuration._FeatureWindowSize / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


                //EXPECTED_SAMPLING_RATES = new int[extractorSensorCount]; - Calculate during loading
                EXPECTED_WINDOW_SIZES = new int[extractorSensorCount];
                EXPECTED_GOOD_SAMPLING_RATES = new int[extractorSensorCount];
                EXPECTED_SAMPLES_SPACING = new double[extractorSensorCount];

                for (int i = 0; (i < sensorCount); i++)
                {
                    EXPECTED_WINDOW_SIZES[i] = (int)(samplingRate * (configuration._FeatureWindowSize / 1000.0));
                    EXPECTED_GOOD_SAMPLING_RATES[i] = EXPECTED_WINDOW_SIZES[i] - (int)(configuration._MaximumNonconsecutivePacketLoss * EXPECTED_WINDOW_SIZES[i]);
                    EXPECTED_SAMPLES_SPACING[i] = (double)configuration._FeatureWindowSize / EXPECTED_WINDOW_SIZES[i];
                }


                //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
                data = new double[extractorSensorCount * 4][]; // 1 row for each axis

                // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
                interpolated_data = new double[extractorSensorCount * 3][];

                // array to store the y location for each axes as data is received
                // will be different for every sensor of course
                y_index = new int[extractorSensorCount];


                //Initialize expected data array
                for (int i = 0; (i < sensorCount); i++)
                {
                    for (int j = 0; j < 4; j++)
                    {
                        data[(i * 4) + j] = new double[EXPECTED_WINDOW_SIZES[i]];
                        for (int k = 0; (k < EXPECTED_WINDOW_SIZES[i]); k++)
                            data[(i * 4) + j][k] = 0;
                    }
                }


                //Here it is equal across all sensors, so we do not need to consider
                //the sampling rate of each sensor separately
                for (int i = 0; (i < (extractorSensorCount * 3)); i++)
                {
                    interpolated_data[i] = new double[INTERPOLATED_SAMPLING_RATE_PER_WINDOW];
                    for (int j = 0; (j < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); j++)
                        interpolated_data[i][j] = 0;
                }

                tail = new int[extractorSensorCount];
                tailUnixtimestamp = new double[extractorSensorCount];
                //Initialize y index for each sensor
                for (int i = 0; (i < extractorSensorCount); i++)
                {
                    y_index[i] = 0;
                    tail[i] = 0;
                    tailUnixtimestamp[i] = 0.0;
                }


                _Initialized = true;
            }
        }




     

        public static void Initialize3(int sensorCount, int samplingRate, WocketsConfiguration configuration, ActivityList activities)
        {
            if (!_Initialized)
            {

                sdata = new MemoryMappedFileStream[sensorCount];
                shead = new MemoryMappedFileStream[sensorCount];
                sdataSize = (int)Wockets.Decoders.Decoder._DUSize * Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE;
                _DecoderTails = new int[sensorCount];

                for (int i = 0; (i < sensorCount); i++)
                    _DecoderTails[i] = 0;

                for (int i = 0; (i < sensorCount); i++)
                {
                    sdata[i] = new MemoryMappedFileStream("\\Temp\\wocket" + i + ".dat", "wocket" + i, (uint)sdataSize, MemoryProtection.PageReadWrite);
                    shead[i] = new MemoryMappedFileStream("\\Temp\\whead" + i + ".dat", "whead" + i, sizeof(int), MemoryProtection.PageReadWrite);

                    sdata[i].MapViewToProcessMemory(0, sdataSize);
                    shead[i].MapViewToProcessMemory(0, sizeof(int));

                    shead[i].Read(head, 0, 4);
                    int currentHead = BitConverter.ToInt32(head, 0);
                    _DecoderTails[i] = currentHead;
                    shead[i].Seek(0, System.IO.SeekOrigin.Begin);
                    sdata[i].Seek((currentHead * (sizeof(double) + 3 * sizeof(short))), System.IO.SeekOrigin.Begin);
                }

                FullFeatureExtractor.configuration = configuration;
                //window counters and delimiters
                next_window_end = 0;
                total_window_count = 0;
                num_feature_windows = 0;

                //data quality variables
                isAcceptableLossRate = true;
                isAcceptableConsecutiveLoss = true;
                unacceptable_window_count = 0;
                unacceptable_consecutive_window_loss_count = 0;

                
                //Upgrade to handle HR
                extractorSensorCount = sensorCount;
                inputRowSize = sensorCount * 3;
                fftInterpolationPower = configuration._FFTInterpolationPower;
                fftMaximumFrequencies = configuration._FFTMaximumFrequencies;

                //Depending on the window size and sr select the higher power of 2
                int numSamples=(int)Math.Ceiling(((configuration._FeatureWindowSize/1000.0)*samplingRate));      
                configuration._FFTInterpolationPower = Wockets.Utils.Math.NextPower2(numSamples);               
                inputColumnSize = (int)Math.Pow(2, configuration._FFTInterpolationPower);


                //Calculate the number of features for a window
                num_features = inputRowSize; // number of distances
                num_features += 1; //total mean;
                num_features += inputRowSize; // number of variances
                num_features += inputRowSize; // number of ranges
                num_features += 2 * configuration._FFTMaximumFrequencies * inputRowSize; // number of fft magnitudes and frequencies
                num_features += inputRowSize; // number of energies
                num_features += ((inputRowSize * inputRowSize) - inputRowSize) / 2; //correlation coefficients off-di


                //Allocate a window with the number of features
                features = new double[num_features];
                arffAttriburesLabels = new string[num_features];
                standardized = new double[sensorCount * 3][];

                for (int i = 0; (i < inputRowSize); i++)                
                    standardized[i] = new double[inputColumnSize];                
                
                means = new double[inputRowSize];
                meansbp = new double[inputRowSize];
                meanslp = new double[inputRowSize];
                inputFFT = new int[inputColumnSize];
                FFT.Initialize(configuration._FFTInterpolationPower, configuration._FFTMaximumFrequencies);
                //FullFeatureExtractor.wocketsController = wocketsController;

                bpFilters = new BPButterworth[inputRowSize];
                lpFilters = new LPButterworth[inputRowSize];
                for (int i = 0; (i < bpFilters.Length); i++)
                {
                    bpFilters[i] = new BPButterworth(Frequency._1_0Hz, Frequency._20_0Hz, Order.Second, SamplingRates._90Hz, bpa, bpb);
                    lpFilters[i] = new LPButterworth(Frequency._1_0Hz, Order.Second, SamplingRates._90Hz, lpa, lpb);
                }
  

                //Create the ARFF File header
                string arffHeader = "@RELATION wockets\n\n" + GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
                arffHeader += "@ATTRIBUTE activity {";
                for (int i = 0; (i < activities.Count); i++)
                    arffHeader += activities[i]._Name.Replace(' ', '_') + ",";
                arffHeader += "unknown}\n";
                arffHeader += "\n@DATA\n\n";


                //total number of points per interpolated window
                INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, configuration._FFTInterpolationPower); 

                //space between interpolated samples
                INTERPOLATED_SAMPLES_SPACING = (double)configuration._FeatureWindowSize / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


                //EXPECTED_SAMPLING_RATES = new int[extractorSensorCount]; - Calculate during loading
                EXPECTED_WINDOW_SIZES = new int[extractorSensorCount];
                EXPECTED_GOOD_SAMPLING_RATES = new int[extractorSensorCount];
                EXPECTED_SAMPLES_SPACING = new double[extractorSensorCount];

                for (int i = 0; (i < sensorCount); i++)
                {
                    EXPECTED_WINDOW_SIZES[i] = (int)(inputColumnSize * (configuration._FeatureWindowSize / 1000.0));
                    EXPECTED_GOOD_SAMPLING_RATES[i] = EXPECTED_WINDOW_SIZES[i] - (int)(configuration._MaximumNonconsecutivePacketLoss * EXPECTED_WINDOW_SIZES[i]);
                    EXPECTED_SAMPLES_SPACING[i] = (double)configuration._FeatureWindowSize / EXPECTED_WINDOW_SIZES[i];
                }


                //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
                data = new double[extractorSensorCount * 3][]; // 1 row for each axis
                lpData = new double[sensorCount * 3][];
                bpData = new double[sensorCount * 3][];

                // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
                // No need to interpolate with BT, use the actual signal
                //interpolated_data = new double[extractorSensorCount * 3][];

                // array to store the y location for each axes as data is received
                // will be different for every sensor of course
                y_index = new int[extractorSensorCount];


                //Initialize expected data array
                for (int i = 0; (i < sensorCount); i++)
                {
                    for (int j = 0; (j < 3); j++)
                    {
                        int index=(i * 3) +j;
                        data[index] = new double[EXPECTED_WINDOW_SIZES[i]];                        
                        //Start using data from 513
                        lpData[index] = new double[EXPECTED_WINDOW_SIZES[i]];
                        bpData[index] = new double[EXPECTED_WINDOW_SIZES[i]];                      

                        for (int k = 0; (k < data[index].Length); k++)
                        {
                            data[index][k] = 0;                        
                            lpData[index][k] = 0;
                            bpData[index][k] = 0;
                        }
                    }
                }


      

                tail = new int[extractorSensorCount];
                tailUnixtimestamp = new double[extractorSensorCount];
                //Initialize y index for each sensor
                for (int i = 0; (i < extractorSensorCount); i++)
                {
                    y_index[i] = 0;
                    tail[i] = 0;
                    tailUnixtimestamp[i] = 0.0;
                }


                

                _Initialized = true;
            }
        }
#endif
        public static void Initialize(WocketsController wocketsController, WocketsConfiguration configuration, ActivityList activities)
        {
            if (!_Initialized)
            {
                FullFeatureExtractor.configuration = configuration;
                //window counters and delimiters
                next_window_end = 0;
                total_window_count = 0;
                num_feature_windows = 0;

                //data quality variables
                isAcceptableLossRate = true;
                isAcceptableConsecutiveLoss = true;
                unacceptable_window_count = 0;
                unacceptable_consecutive_window_loss_count = 0;


                //Upgrade to handle HR
                extractorSensorCount = wocketsController._Sensors.Count;
                inputRowSize = wocketsController._Sensors.Count * 3;
                fftInterpolationPower = configuration._FFTInterpolationPower;
                fftMaximumFrequencies = configuration._FFTMaximumFrequencies;
                inputColumnSize = (int)Math.Pow(2, configuration._FFTInterpolationPower);

                num_features = inputRowSize; // number of distances
                num_features += 1; //total mean;
                num_features += inputRowSize; // number of variances
                num_features += inputRowSize; // number of ranges
                num_features += 2 * configuration._FFTMaximumFrequencies * inputRowSize; // number of fft magnitudes and frequencies
                num_features += inputRowSize; // number of energies
                num_features += ((inputRowSize * inputRowSize) - inputRowSize) / 2; //correlation coefficients off-di


                features = new double[num_features];
                arffAttriburesLabels = new string[num_features];

                standardized = new double[wocketsController._Sensors.Count * 3][];
                for (int i = 0; (i < inputRowSize); i++)
                    standardized[i] = new double[inputColumnSize];//input[0].Length];

                means = new double[inputRowSize];

                inputFFT = new int[inputColumnSize];
                FFT.Initialize(configuration._FFTInterpolationPower, configuration._FFTMaximumFrequencies);
                FullFeatureExtractor.wocketsController = wocketsController;

                //Create the ARFF File header
                string arffHeader = "@RELATION wockets\n\n" + GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
                arffHeader += "@ATTRIBUTE activity {";
                for (int i = 0; (i < activities.Count); i++)
                    arffHeader += activities[i]._Name.Replace(' ', '_') + ",";
                arffHeader += "unknown}\n";
                arffHeader += "\n@DATA\n\n";


                //total number of points per interpolated window
                INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, configuration._FFTInterpolationPower); //128;  

                //space between interpolated samples
                INTERPOLATED_SAMPLES_SPACING = (double)configuration._FeatureWindowSize / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


                //EXPECTED_SAMPLING_RATES = new int[extractorSensorCount]; - Calculate during loading
                EXPECTED_WINDOW_SIZES = new int[extractorSensorCount];
                EXPECTED_GOOD_SAMPLING_RATES = new int[extractorSensorCount];
                EXPECTED_SAMPLES_SPACING = new double[extractorSensorCount];

                for (int i = 0; (i < wocketsController._Sensors.Count); i++)
                {
                    EXPECTED_WINDOW_SIZES[i] = (int)(wocketsController._Sensors[i]._SamplingRate * (configuration._FeatureWindowSize / 1000.0));
                    EXPECTED_GOOD_SAMPLING_RATES[i] = EXPECTED_WINDOW_SIZES[i] - (int)(configuration._MaximumNonconsecutivePacketLoss * EXPECTED_WINDOW_SIZES[i]);
                    EXPECTED_SAMPLES_SPACING[i] = (double)configuration._FeatureWindowSize / EXPECTED_WINDOW_SIZES[i];
                }


                //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
                data = new double[extractorSensorCount * 4][]; // 1 row for each axis

                // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
                interpolated_data = new double[extractorSensorCount * 3][];

                // array to store the y location for each axes as data is received
                // will be different for every sensor of course
                y_index = new int[extractorSensorCount];


                //Initialize expected data array
                for (int i = 0; (i < wocketsController._Sensors.Count); i++)
                {
                    for (int j = 0; j < 4; j++)
                    {
                        data[(i * 4) + j] = new double[EXPECTED_WINDOW_SIZES[i]];
                        for (int k = 0; (k < EXPECTED_WINDOW_SIZES[i]); k++)
                            data[(i * 4) + j][k] = 0;
                    }
                }


                //Here it is equal across all sensors, so we do not need to consider
                //the sampling rate of each sensor separately
                for (int i = 0; (i < (extractorSensorCount * 3)); i++)
                {
                    interpolated_data[i] = new double[INTERPOLATED_SAMPLING_RATE_PER_WINDOW];
                    for (int j = 0; (j < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); j++)
                        interpolated_data[i][j] = 0;
                }

                tail = new int[extractorSensorCount];
                tailUnixtimestamp = new double[extractorSensorCount];
                //Initialize y index for each sensor
                for (int i = 0; (i < extractorSensorCount); i++)
                {
                    y_index[i] = 0;
                    tail[i] = 0;
                    tailUnixtimestamp[i] = 0.0;
                }


                _Initialized = true;
            }
        }

#if (PocketPC)
        public static double StoreWocketsWindow()
        {
            double unixtimestamp = 0.0;


            for (int i = 0; (i < sdata.Length); i++)
            {

                shead[i].Read(head, 0, 4);
                int currentHead = BitConverter.ToInt32(head, 0);
                shead[i].Seek(0, System.IO.SeekOrigin.Begin);

                int tail = _DecoderTails[i];

                while (tail != currentHead)
                {
                    int x = 0, y = 0, z = 0;
                    sdata[i].Read(timestamp, 0, sizeof(double));
                    unixtimestamp = BitConverter.ToDouble(timestamp, 0);
                    sdata[i].Read(acc, 0, sizeof(short));
                    x = BitConverter.ToInt16(acc, 0);
                    sdata[i].Read(acc, 0, sizeof(short));
                    y = BitConverter.ToInt16(acc, 0);
                    sdata[i].Read(acc, 0, sizeof(short));
                    z = BitConverter.ToInt16(acc, 0);


                    if (tail >= (Wockets.Decoders.Accelerometers.WocketsDecoder.BUFFER_SIZE - 1))
                    {
                        tail = 0;
                        sdata[i].Seek(0, System.IO.SeekOrigin.Begin);
                    }
                    else
                        tail++;

                    int sensorIndex = i * 4;
                    // store the values in the current frame in the correct column based of the EXPECTED_WINDOW data array
                    // on the y_index for the sensor
                    FullFeatureExtractor.data[sensorIndex][FullFeatureExtractor.y_index[i]] = x;
                    FullFeatureExtractor.data[sensorIndex + 1][FullFeatureExtractor.y_index[i]] = y;
                    FullFeatureExtractor.data[sensorIndex + 2][FullFeatureExtractor.y_index[i]] = z;
                    FullFeatureExtractor.data[sensorIndex + 3][FullFeatureExtractor.y_index[i]] = unixtimestamp;

                    //increment the y_index for the sensor and wrap around if needed
                       
                    FullFeatureExtractor.y_index[i] = (FullFeatureExtractor.y_index[i] + 1) % FullFeatureExtractor.EXPECTED_WINDOW_SIZES[i];

                }

                _DecoderTails[i] = currentHead;
            }


            return unixtimestamp;

        }

        //Call this window when there is a new full window ready for analysis
        //the window should belong to consecutive data
        //Ensure you are copying the sliding window
        public static void StoreWocketsWindow3()
       {
           int decoderIndex = 0;
            for (int i = 0; (i <CurrentWockets._Controller._Decoders.Count); i++)
            {
                int sensorIndex = i * 3;
                int start = CurrentWockets._Controller._Decoders[i]._Head-1-EXPECTED_WINDOW_SIZES[i];
                if (start < 0)
                    start = CurrentWockets._Controller._Decoders[i]._BufferSize + start;
                decoderIndex = start;
                for (int j =0; (j < EXPECTED_WINDOW_SIZES[i]);j++)
                {


                    FullFeatureExtractor.data[sensorIndex][j] = ((AccelerationData)CurrentWockets._Controller._Decoders[i]._Data[decoderIndex]).X;
                    FullFeatureExtractor.data[sensorIndex + 1][j] = ((AccelerationData)CurrentWockets._Controller._Decoders[i]._Data[decoderIndex]).Y;
                    FullFeatureExtractor.data[sensorIndex + 2][j] = ((AccelerationData)CurrentWockets._Controller._Decoders[i]._Data[decoderIndex]).Z;
                    decoderIndex++;
                    if (decoderIndex >= CurrentWockets._Controller._Decoders[i]._BufferSize)
                        decoderIndex = 0;
                }                
            }            

        }

#else
       
        public static double StoreWocketsWindow()
        {
            double unixtimestamp = 0.0;

          //  for (int i = 0; i < FullFeatureExtractor.wocketsController._Decoders.Count; i++)
           //     for (int j=0;(j<FullFeatureExtractor.wocketsController._Decoders[i]._Size);j++)
            

            for (int i = 0; i < FullFeatureExtractor.wocketsController._Decoders.Count; i++)
            {            
                AccelerationData datum = ((AccelerationData) FullFeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]); 
                int currentHead=FullFeatureExtractor.wocketsController._Decoders[i]._Head;
                while ((tail[i] != currentHead) && (datum.UnixTimeStamp > 0) && (datum.UnixTimeStamp >= tailUnixtimestamp[i]))
               
                {
                    int  x = 0, y = 0, z = 0;                    
                    x = (int)((AccelerationData)FullFeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).X;
                    y = (int)((AccelerationData)FullFeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).Y;
                    z = (int)((AccelerationData)FullFeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).Z;
                    unixtimestamp = ((AccelerationData)FullFeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).UnixTimeStamp;
                    tailUnixtimestamp[i] = unixtimestamp;
                    if (tail[i] >= (FullFeatureExtractor.wocketsController._Decoders[i]._Data.Length - 1))
                        tail[i] = 0;
                    else
                        tail[i]++;

                    int sensorIndex = i*4;
                    // store the values in the current frame in the correct column based of the EXPECTED_WINDOW data array
                    // on the y_index for the sensor
                    FullFeatureExtractor.data[sensorIndex][FullFeatureExtractor.y_index[i]] = x;
                    FullFeatureExtractor.data[sensorIndex + 1][FullFeatureExtractor.y_index[i]] = y;
                    FullFeatureExtractor.data[sensorIndex + 2][FullFeatureExtractor.y_index[i]] = z;
                    FullFeatureExtractor.data[sensorIndex + 3][FullFeatureExtractor.y_index[i]] = unixtimestamp;
                    //if (unixtimestamp < 1000)
                     //   throw new Exception("BUG");

                    //increment the y_index for the sensor and wrap around if needed
                    FullFeatureExtractor.y_index[i] = (FullFeatureExtractor.y_index[i] + 1) % FullFeatureExtractor.EXPECTED_WINDOW_SIZES[i];
                    datum = ((AccelerationData)FullFeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]); 
                }

            }

            return unixtimestamp;

        }
#endif

        static TextWriter tw=null;
        //Call this only when enough samples are recorded
        public static void GenerateFeatureVector3()
        {

            
            // Go through each sensor and extract the collected data within 
            // the current time window
            for (int i = 0; (i < FullFeatureExtractor.data.Length); i++)
            {

                //bpData[i] = bpFilters[i].Filter(FullFeatureExtractor.data[i]);
                //lpData[i] = lpFilters[i].Filter(FullFeatureExtractor.data[i]);                       
            }

            //At this point data, bpdata and lpdata have the unfiltered and filtered window
            //Extract3(lpData, bpData);
            
            /*tw = new StreamWriter("FilteredDataBP.csv",true);
            for (int j = 0; (j < EXPECTED_WINDOW_SIZES[0]); j++)
            {
                string line = "";
                for (int i = 0; (i < FullFeatureExtractor.data.Length); i++)
                {
                    line += FullFeatureExtractor.data[i][j] + "," + bpData[i][j] + "," + lpData[i][j];
                    if (i < FullFeatureExtractor.data.Length - 1)
                        line += ",";

                }
                tw.WriteLine(line);
            }
            tw.Close();*/
        }

        public static bool GenerateFeatureVector(double lastTimeStamp)
        {

            // Generate a feature vector only, if the next window end has
            // passed based on the configuration parameters (window size and overlap)
            // otherwise return false
            if (lastTimeStamp < next_window_end)
                return false;

            // the last time stamp is more than the next expected window end
            // At this point, we have a complete window ready for feature calculation

            //compute the boundaries for the current window
            double window_start_time = lastTimeStamp - configuration._FeatureWindowSize;
            double window_end_time = lastTimeStamp;
            double current_time = window_end_time;
            //compute the end of the next overlapping window
            next_window_end = window_end_time + (configuration._FeatureWindowSize * configuration._FeatureWindowOverlap);

            #region sensors window grabbing and interpolation

            // Go through each sensor and extract the collected data within 
            // the current time window
            for (int j = 0; (j < extractorSensorCount); j++)
            {

                // Check that the previous sensor in the loop did not report
                // deteriorated quality for its data
                #region sensors window quality
                if (isAcceptableLossRate == false)
                    break;

                // check if earlier axes reported excessive consecutive loss of data frames
                if (isAcceptableConsecutiveLoss == false)
                {
                    discardedConsecutiveLossWindows++;
                    break;
                }
                #endregion sensors window quality

                // determine the base index for the current sensor in data array, each sensor has 4 rows (x,y,z,timestamp)
                int sensor_index = j * 4;
                int time_index = sensor_index + 3;

                // determine the last read data sample for the current sensor
                // by looking at its index
                int last_sample = 0;
                if (y_index[j] == 0)
                    last_sample = EXPECTED_WINDOW_SIZES[j] - 1;
                else
                    last_sample = y_index[j] - 1;

                //              int total_data_points = 0, distinct_data_points = 0;
                int distinct_data_points = 0;

                //Grab the readings for each axis of a sensor and smoothen it
                #region sensor window grabbing and interpolation
                // Go through each axis of the current sensor and smooth
                // it using the cubic spline
                for (int axes_num = 0; (axes_num < 3); axes_num++)
                {

                    //calculate the exact index based on the 
                    // base sensor index and the axis number
                    int axes_index = sensor_index + axes_num;  //for data array
                    int interpolated_axes_index = j * 3 + axes_num; //for interpolated data array

                    // create 2 arrays to store x and y values for the cubic spline
                    // it is sufficient to have an array of expected sampling rate window size
                    // for 3 mites that would be 180/60
                    double[] xvals = new double[EXPECTED_WINDOW_SIZES[j]];
                    double[] yvals = new double[EXPECTED_WINDOW_SIZES[j]];

                    //point to the last sample that was read and get its time
                    int sample_index = last_sample;
                    current_time = data[time_index][sample_index];


                    distinct_data_points = 0;

                    //Grab the values for a specific sensor axes between
                    //window start and window end
                    #region window grabbing
                    // Start going back from the current time (window end) till the start of the window
                    // without exceeding the expected sampling rate and fill in the data in the signal
                    // value for the axis in yvals and the relative time value from the window start
                    while ((current_time >= window_start_time) && (current_time <= window_end_time)
                         && (distinct_data_points < EXPECTED_WINDOW_SIZES[j]))
                    {


                        //some time stamps from the mites are identical
                        // for interpolation that will cause an error
                        // simply take the first value for a time point and ignore the
                        // rest, another strategy would be to average over these values
                        // we decided, we will spread them out evenly as long as
                        // no excessive loss is experienced
                        // done down in the code
                        xvals[distinct_data_points] = (int)(current_time - window_start_time);
                        //signal value for the current sample and current axis.
                        yvals[distinct_data_points] = data[axes_index][sample_index];

                        //Get the time of the new sample
                        current_time = data[time_index][sample_index];

                        //Point to the previous sample in the current window
                        if (sample_index == 0)
                            sample_index = EXPECTED_WINDOW_SIZES[j] - 1;
                        else
                            sample_index--;


                        //Point to the next entry in the interpolation array
                        distinct_data_points++;

                    }
                    #endregion window grabbing

                    //Check if the captured window has acceptable loss rate
                    #region window quality checks
                    //Do not proceed if there was excessive consecutive loss of data frames
                    if (isAcceptableConsecutiveLoss == false)
                        break;

                    // all data for a specific sensor axis for the current window are stored
                    // in xvals and yvals
                    // check if the data is admissible for feature calculation according to the following
                    // criteria:
                    // 1- total lost data frames are within the loss rate
                    // 2- the number of consecutive lost packets is within our maximum_consecutive_loss parameter
                    if (distinct_data_points < FullFeatureExtractor.EXPECTED_GOOD_SAMPLING_RATES[j]) //discard this whole window of data
                    {
                        discardedLossRateWindows++;
                        isAcceptableLossRate = false;
                        unacceptable_window_count++;
                        break;
                    }

                    #endregion window quality checks

                    //smoothen the axis values and store them in interpolated data array
                    #region window interpolation

                    //create 2 arrays with the exact size of the data points for interpolation
                    double[] admissible_xvals = new double[distinct_data_points];
                    double[] admissible_yvals = new double[distinct_data_points];
                    double expectedSpacing = configuration._FeatureWindowSize / (double)distinct_data_points;
                    double startTime = 0.0;
                    for (int k = 0; (k < distinct_data_points); k++)
                    {
                        admissible_xvals[k] = startTime + k * expectedSpacing;//xvals[distinct_data_points - k - 1];
                        admissible_yvals[k] = yvals[distinct_data_points - k - 1];
                    }


                    // smooth it using a cubic spline
                    CubicSpline cs = new CubicSpline(admissible_xvals, admissible_yvals);

                    // shrink or expand the data window using interpolation                
                    for (int k = 0; (k < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); k++)
                    {
                        interpolated_data[interpolated_axes_index][k] = cs.interpolate(k * INTERPOLATED_SAMPLES_SPACING);
                        //check that the intrepolated values make sense.
                        //if ((interpolated_data[interpolated_axes_index][k] <= 0) || (interpolated_data[interpolated_axes_index][k] > 1024))
                        if ((interpolated_data[interpolated_axes_index][k] <= -6000) || (interpolated_data[interpolated_axes_index][k] > 6000))
                            return false;
                    }


                    #endregion window interpolation
                }
                #endregion sensor window grabbing and interpolation


            }
            #endregion sensors window grabbing and interpolation

            //If the data is of acceptable quality, calculate the features
            #region Calculate Feature Vector

            if ((isAcceptableLossRate == true) && (isAcceptableConsecutiveLoss == true))
            {
                //Extract the features from the interpolated data
                //FullFeatureExtractor.Extract(interpolated_data);
                Extract(interpolated_data);
                return true;
            }
            else  //the window is of poor quality, reinitialize and continue
            {
                isAcceptableConsecutiveLoss = true;
                isAcceptableLossRate = true;
                return false;
            }

            #endregion Calculate Feature Vector

        }


        //Extract expects data from a low and band pass filter
        public static void Extract3(double[][] lp, double[][] bp)
        {

            int j = 0, i = 0;
            double sumlp = 0,sumbp=0, min = 0, max = 0, total = 0, variance = 0;

            int distanceIndex = 0;//number of means on every row + 1 for total mean, 0 based index
            int varianceIndex = distanceIndex + inputRowSize + 1; // add number of distances
            int rangeIndex = varianceIndex + inputRowSize;
            int fftIndex = rangeIndex + inputRowSize;
            int energyIndex = fftIndex + (2 * fftMaximumFrequencies * inputRowSize);
            int correlationIndex = energyIndex + inputRowSize; //add number of variances         


            for (i = 0; (i < features.Length); i++)
                features[i] = 0;

            //for good cache locality go through the rows then columns
            for (i = 0; (i < inputRowSize); i++)
            {
                min = 999999999.0;
                max = -999999999.0;

                for (j = 0; (j < inputColumnSize); j++)
                {
                    if (bp[i][j] < min)
                        min = bp[i][j];
                    if (bp[i][j] > max)
                        max = bp[i][j];
                    inputFFT[j] = (int)(bp[i][j]);
                    sumbp += bp[i][j];
                    sumlp += lp[i][j];
                }

                meansbp[i] = sumbp / inputColumnSize;   //mean
                meanslp[i] = sumlp / inputColumnSize;   //mean
                total += meansbp[i];  //total mean

                if ((i + 1) % 3 == 0)
                {
                    features[distanceIndex++] = meanslp[i - 2] - meanslp[i - 1];
                    features[distanceIndex++] = meanslp[i - 2] - meanslp[i];
                    features[distanceIndex++] = meanslp[i - 1] - meanslp[i];
                }



                //fill variance
                variance = 0;
                for (j = 0; (j < inputColumnSize); j++)
                {
                    variance += Math.Pow(bp[i][j] - meansbp[i], 2);
                    //***mean subtracted
                    standardized[i][j] = bp[i][j] - meansbp[i]; //mean subtracted

                }
                features[varianceIndex++] = variance / (inputColumnSize - 1);

                //calculate the range
                features[rangeIndex++] = Math.Abs(max - min);

                //calculate FFT                
                FFT.Calculate(inputFFT);


                features[energyIndex++] = FFT.Energy;
                double[] maxFreqs = FFT.MaximumFrequencies;

                for (int k = 0; (k < maxFreqs.Length); k++)
                {
                    features[fftIndex++] = maxFreqs[k++];
                    features[fftIndex++] = maxFreqs[k];
                }


                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    for (int w = 0; (w < inputColumnSize); w++)
                        features[correlationIndex] += standardized[i][w] * standardized[k][w];
                    features[correlationIndex] /= (inputColumnSize - 1);
                    features[correlationIndex] /= Math.Sqrt(features[varianceIndex - 1]);  // ith std deviation
                    features[correlationIndex] /= Math.Sqrt(features[varianceIndex - 1 - (i - k)]);  //kth std deviation 
                    correlationIndex++;
                }

            }

            features[inputRowSize] = total;
        }





        //input is a 2D array 3*SensorCount X 2^ FFT Interpolation Power e.g. for 3 MITes INT power=7  9 X 128
        public static void Extract(double[][] input)//,int fftInterpolationPower, int fftMaximumFrequencies)
        {

            int j = 0, i = 0;
            double sum = 0, min = 0, max = 0, total = 0, variance = 0;

            int distanceIndex = 0;//number of means on every row + 1 for total mean, 0 based index
            int varianceIndex = distanceIndex + inputRowSize + 1; // add number of distances
            int rangeIndex = varianceIndex + inputRowSize;
            int fftIndex = rangeIndex + inputRowSize;
            int energyIndex = fftIndex + (2 * fftMaximumFrequencies * inputRowSize);
            int correlationIndex = energyIndex + inputRowSize; //add number of variances         


            for (i = 0; (i < features.Length); i++)
                features[i] = 0;

            //for good cache locality go through the rows then columns
            for (i = 0; (i < inputRowSize); i++)
            {
                min = 999999999.0;
                max = -999999999.0;
                sum = 0;

                for (j = 0; (j < inputColumnSize); j++)
                {
                    if (input[i][j] < min)
                        min = input[i][j];
                    if (input[i][j] > max)
                        max = input[i][j];
                    inputFFT[j] = (int)(input[i][j]);
                    sum += input[i][j];
                }

                means[i] = sum / inputColumnSize;   //mean
                total += means[i];  //total mean

                if ((i + 1) % 3 == 0)
                {
                    features[distanceIndex++] = means[i - 2] - means[i - 1];
                    features[distanceIndex++] = means[i - 2] - means[i];
                    features[distanceIndex++] = means[i - 1] - means[i];
                }



                //fill variance
                variance = 0;
                for (j = 0; (j < inputColumnSize); j++)
                {
                    variance += Math.Pow(input[i][j] - means[i], 2);
                    //***mean subtracted
                    standardized[i][j] = input[i][j] - means[i]; //mean subtracted

                }
                features[varianceIndex++] = variance / (inputColumnSize - 1);

                //calculate the range
                features[rangeIndex++] = Math.Abs(max - min);

                //calculate FFT                
                FFT.Calculate(inputFFT);


                features[energyIndex++] = FFT.Energy;
                double[] maxFreqs = FFT.MaximumFrequencies;

                for (int k = 0; (k < maxFreqs.Length); k++)
                {
                    features[fftIndex++] = maxFreqs[k++];
                    features[fftIndex++] = maxFreqs[k];
                }


                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    for (int w = 0; (w < inputColumnSize); w++)
                        features[correlationIndex] += standardized[i][w] * standardized[k][w];
                    features[correlationIndex] /= (inputColumnSize - 1);
                    features[correlationIndex] /= Math.Sqrt(features[varianceIndex - 1]);  // ith std deviation
                    features[correlationIndex] /= Math.Sqrt(features[varianceIndex - 1 - (i - k)]);  //kth std deviation 
                    correlationIndex++;
                }

            }

            features[inputRowSize] = total;
        }

        public static void Cleanup()
        {
            if (_Initialized)
            {
                FFT.Cleanup();
                _Initialized = false;
            }
        }

        public static string GetArffHeader()
        {
            string DISTANCE_ATTRIBUTES = "";
            string TOTAL_ATTRIBUTE = "";
            string VARIANCE_ATTRIBUTES = "";
            string RANGE_ATTRIBUTES = "";
            string FFT_ATTRIBUTES = "";
            string ENERGY_ATTRIBUTES = "";
            string CORRELATION_ATTRIBUTES = "";

            int distanceIndex = 0;//number of means on every row + 1 for total mean, 0 based index
            int varianceIndex = distanceIndex + inputRowSize + 1; // add number of distances
            int rangeIndex = varianceIndex + inputRowSize;
            int fftIndex = rangeIndex + inputRowSize;
            int energyIndex = fftIndex + (2 * fftMaximumFrequencies * inputRowSize);
            int correlationIndex = energyIndex + inputRowSize; //add number of variances   

            for (int i = 0; (i < inputRowSize); i++)
            {
                if ((i + 1) % 3 == 0)
                {
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 2) + "_Mean" + (i - 1) + " NUMERIC\n";
                    arffAttriburesLabels[distanceIndex++] = "Dist_Mean" + (i - 2) + "_Mean" + (i - 1);
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 2) + "_Mean" + (i) + " NUMERIC\n";
                    arffAttriburesLabels[distanceIndex++] = "Dist_Mean" + (i - 2) + "_Mean" + (i);
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 1) + "_Mean" + (i) + " NUMERIC\n";
                    arffAttriburesLabels[distanceIndex++] = "Dist_Mean" + (i - 1) + "_Mean" + (i);
                }


                VARIANCE_ATTRIBUTES += "@ATTRIBUTE Variance_" + i + " NUMERIC\n";
                arffAttriburesLabels[varianceIndex++] = "Variance_" + i;


                RANGE_ATTRIBUTES += "@ATTRIBUTE RANGE_" + i + " NUMERIC\n";
                arffAttriburesLabels[rangeIndex++] = "RANGE_" + i;

                for (int k = 0; (k < (fftMaximumFrequencies * 2)); k++)
                {
                    k++;
                    FFT_ATTRIBUTES += "@ATTRIBUTE FFT_MAX_FREQ" + i + "_" + k + " NUMERIC\n";
                    arffAttriburesLabels[fftIndex++] = "FFT_MAX_FREQ" + i + "_" + k;

                    FFT_ATTRIBUTES += "@ATTRIBUTE FFT_MAX_MAG" + i + "_" + k + " NUMERIC\n";
                    arffAttriburesLabels[fftIndex++] = "FFT_MAX_MAG" + i + "_" + k;

                }

                ENERGY_ATTRIBUTES += "@ATTRIBUTE ENERGY_" + i + " NUMERIC\n";
                arffAttriburesLabels[energyIndex++] = "ENERGY_" + i;


                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    CORRELATION_ATTRIBUTES += "@ATTRIBUTE CORRELATION_" + k + "_" + i + " NUMERIC\n";
                    arffAttriburesLabels[correlationIndex++] = "CORRELATION_" + k + "_" + i;
                }
            }

            TOTAL_ATTRIBUTE += "@ATTRIBUTE TotalMean NUMERIC\n";
            arffAttriburesLabels[distanceIndex] = "TotalMean";

            return DISTANCE_ATTRIBUTES + TOTAL_ATTRIBUTE + VARIANCE_ATTRIBUTES + RANGE_ATTRIBUTES +
               FFT_ATTRIBUTES + ENERGY_ATTRIBUTES + CORRELATION_ATTRIBUTES;
        }

        public static string toString()
        {
            string s = "";
            int i = 0;

            for (i = 0; (i < features.Length - 1); i++)
                s += features[i].ToString("F2") + ",";
            s += features[i].ToString("F2");
            return s;

        }

    }
}
