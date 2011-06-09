using System;
using System.Collections.Generic;
using System.Text;
using WocketsWeka.core;
using WocketsWeka.Utils;
using Wockets;
using Wockets.Data.Classifiers;
using Wockets.Data.Annotation;
using Wockets.Data.Accelerometers;
using System.IO;

namespace ExtractorPerformance
{
    public class FeatureExtractor
    {
        private static int extractorSensorCount = 0;
        private static int inputRowSize;
        private static int inputColumnSize;
        private static int fftInterpolationPower;
        private static int fftMaximumFrequencies;
        private static int num_features = 0;

        private static double[] features;
        private static double[][] standardized;
        private static double[] means;
        private static double[] variances;
        private static int[] inputFFT;
        private static string[] arffAttriburesLabels;

        private static WocketsController wocketsController;
        private static ClassifierConfiguration configuration;

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

        public static string[] ArffAttributeLabels
        {
            get
            {
                return FeatureExtractor.arffAttriburesLabels;
            }
        }

        public static double[] Features
        {
            get
            {
                return FeatureExtractor.features;
            }
        }
        public static void Initialize(WocketsController wocketsController, ClassifierConfiguration configuration, ActivityList activities)
        {

            FeatureExtractor.configuration = configuration;
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
            fftInterpolationPower = configuration._FFTInterpolatedPower;
            fftMaximumFrequencies = configuration._FFTMaximumFrequencies;
            inputColumnSize = (int)Math.Pow(2, configuration._FFTInterpolatedPower);

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
            FFT.Initialize(configuration._FFTInterpolatedPower, configuration._FFTMaximumFrequencies);
            FeatureExtractor.wocketsController = wocketsController;

            //Create the ARFF File header
            string arffHeader = "@RELATION wockets\n\n" + GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
            arffHeader += "@ATTRIBUTE activity {";
            for (int i = 0; (i < activities.Count); i++)
                arffHeader += activities[i]._Name.Replace(' ', '_') + ",";
            arffHeader += "unknown}\n";
            arffHeader += "\n@DATA\n\n";


            //total number of points per interpolated window
            INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, configuration._FFTInterpolatedPower); //128;  

            //space between interpolated samples
            INTERPOLATED_SAMPLES_SPACING = (double)configuration._WindowTime / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


            //EXPECTED_SAMPLING_RATES = new int[extractorSensorCount]; - Calculate during loading
            EXPECTED_WINDOW_SIZES = new int[extractorSensorCount];
            EXPECTED_GOOD_SAMPLING_RATES = new int[extractorSensorCount];
            EXPECTED_SAMPLES_SPACING = new double[extractorSensorCount];

            for (int i = 0; (i < wocketsController._Sensors.Count); i++)
            {
                EXPECTED_WINDOW_SIZES[i] = (int)(wocketsController._Sensors[i]._SamplingRate * (configuration._WindowTime / 1000.0));
                EXPECTED_GOOD_SAMPLING_RATES[i] = EXPECTED_WINDOW_SIZES[i] - (int)(configuration._MaximumNonconsecutiveFrameLoss * EXPECTED_WINDOW_SIZES[i]);
                EXPECTED_SAMPLES_SPACING[i] = (double)configuration._WindowTime / EXPECTED_WINDOW_SIZES[i];
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




        }









        static double[][] LP1Hz_xv, LP1Hz_yv;
        static int LP1Hz_NZER0S = 2;
        static int LP1Hz_NPOLES = 2;
        static double LP1Hz_GAIN = 1.717988320e+03;

        static double[][] BPpt1_20Hz_xv, BPpt1_20Hz_yv;
        static int BPpt1_20Hz_NZER0S = 4;
        static int BPpt1_20Hz_NPOLES = 4;
        static double BPpt1_20Hz_GAIN = 7.042672448e+00;

        private static double[] fv;

        public static bool DCMean = false;
        static int DCMeanIndex = 0;

        public static bool DCMeanTotal = false;
        static int DCMeanTotalIndex = 0;

        public static bool DCArea = false;
        static int DCAreaIndex = 0;

        public static bool DCAreaSensor = false;
        static int DCAreaSensorIndex = 0;

        public static bool DCPostureDist = false;
        static int DCPostureDistIndex = 0;

        public static bool ACAbsMean = false;
        static int ACAbsMeanIndex = 0;

        public static bool ACAbsArea = false;
        static int ACAbsAreaIndex = 0;

        public static bool ACAbsAreaSensor = false;
        static int ACAbsAreaSensorIndex = 0;

        public static bool ACTotalAbsArea = false;
        static int ACTotalAbsAreaIndex = 0;

        public static bool ACSVM = false;
        static int ACSVMIndex = 0;

        public static bool ACTotalSVM = false;
        static int ACTotalSVMIndex = 0;

        public static bool SpectralContent = false;
        static int NumberFrequencies = 5;
        static int ACFFTFreqsIndex = 0;
        static int ACFFTMagsIndex = 0;

        public static bool ACEntropy = false;
        static int ACEntropyIndex = 0;

        public static bool ACEnergy = false;
        static int ACEnergyIndex = 0;

        public static bool ACSkew = false;
        static int ACSkewIndex = 0;

        public static bool ACKur = false;
        static int ACKurIndex = 0;

        public static bool ACQuartiles = false;
        static int ACQuartilesIndex = 0;

        public static bool ACVar = false;
        static int ACVarIndex = 0;

        public static bool ACAbsCV = false;
        static int ACAbsCVIndex = 0;

        public static bool ACIQR = false;
        static int ACIQRIndex = 0;

        public static bool ACRange = false;
        static int ACRangeIndex = 0;


        public static bool ACBandEnergy = false;
        static int ACBandEnergyIndex = 0;

        public static bool ACLowEnergy = false;
        static int ACLowEnergyIndex = 0;

        public static bool ACModVigEnergy = false;
        static int ACModVigEnergyIndex = 0;

        public static bool ACPitch = false;
        static int ACPitchIndex = 0;

        public static bool ACMCR = false;
        static int ACMCRIndex = 0;

        public static bool ACCorr = false;
        static int ACCorrIndex = 0;

        public static bool ACSF = false;
        static int ACSFIndex = 0;
        static double TotalMass = 62.0;
        static double TrunkMass = 0.497; //(Hip)
        static double ArmMass = 0.0500; //(Arm)
        static double LegMass = 0.1610; //(Leg)

        static double[] limbs = new double[5] { TrunkMass, ArmMass, ArmMass, LegMass, LegMass };
        //0 HR, 1 Hip, 4 DA, 7 DW, 8 NDA, 11 DT, 14 DArm, 17 NDW
        static int[] limbsIndex = new int[5] { 1, 3, 7, 2, 4 };


        public static bool ACTotalSF = false;
        static int ACTotalSFIndex = 0;

        //private static double[] features;

        private static double[] meanslp;
        private static double[] meansbp;

        private static int[] EXPECTED_SAMPLING_RATES;
        //private static int[] EXPECTED_WINDOW_SIZES;
        //private static int[] EXPECTED_GOOD_SAMPLING_RATES;
        //private static double[] EXPECTED_SAMPLES_SPACING;

        public static void InitializeOptional(WocketsController wocketsController, ClassifierConfiguration configuration, ActivityList activities)//(MITesDecoder aMITesDecoder, string aDataDirectory,
//AXML.Annotation aannotation, SXML.SensorAnnotation sannotation, GeneralConfiguration configuration)//, string masterDirectory)
        {
            int numFeatures = 0;
            int currentIndex = 0;
            FeatureExtractor.configuration = configuration;
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
            fftInterpolationPower = configuration._FFTInterpolatedPower;
            fftMaximumFrequencies = configuration._FFTMaximumFrequencies;
            inputColumnSize = (int)Math.Pow(2, configuration._FFTInterpolatedPower);

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
            FFT.Initialize(configuration._FFTInterpolatedPower, configuration._FFTMaximumFrequencies);
            FeatureExtractor.wocketsController = wocketsController;

            //Create the ARFF File header
          /*  string arffHeader = "@RELATION wockets\n\n" + GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
            arffHeader += "@ATTRIBUTE activity {";
            for (int i = 0; (i < activities.Count); i++)
                arffHeader += activities[i]._Name.Replace(' ', '_') + ",";
            arffHeader += "unknown}\n";
            arffHeader += "\n@DATA\n\n";
*/

            //total number of points per interpolated window
            INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, configuration._FFTInterpolatedPower); //128;  

            //space between interpolated samples
            INTERPOLATED_SAMPLES_SPACING = (double)configuration._WindowTime / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


            //EXPECTED_SAMPLING_RATES = new int[extractorSensorCount]; - Calculate during loading
            EXPECTED_WINDOW_SIZES = new int[extractorSensorCount];
            EXPECTED_GOOD_SAMPLING_RATES = new int[extractorSensorCount];
            EXPECTED_SAMPLES_SPACING = new double[extractorSensorCount];

            for (int i = 0; (i < wocketsController._Sensors.Count); i++)
            {
                EXPECTED_WINDOW_SIZES[i] = (int)(wocketsController._Sensors[i]._SamplingRate * (configuration._WindowTime / 1000.0));
                EXPECTED_GOOD_SAMPLING_RATES[i] = EXPECTED_WINDOW_SIZES[i] - (int)(configuration._MaximumNonconsecutiveFrameLoss * EXPECTED_WINDOW_SIZES[i]);
                EXPECTED_SAMPLES_SPACING[i] = (double)configuration._WindowTime / EXPECTED_WINDOW_SIZES[i];
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


            FeatureExtractor.DCMean = true;
            FeatureExtractor.DCMeanTotal = true;
            FeatureExtractor.DCArea = true;
            FeatureExtractor.DCAreaSensor = true;
            FeatureExtractor.DCPostureDist = true;
            FeatureExtractor.ACAbsMean = true;
            FeatureExtractor.ACAbsArea = true;
            FeatureExtractor.ACAbsAreaSensor = true;
            FeatureExtractor.ACTotalAbsArea = true;
            FeatureExtractor.ACSVM = true;
            FeatureExtractor.ACTotalSVM = true;
            FeatureExtractor.SpectralContent = true;
            FeatureExtractor.ACEntropy = true;
            FeatureExtractor.ACEnergy = true;
            FeatureExtractor.ACSkew = true;
            FeatureExtractor.ACKur = true;
            FeatureExtractor.ACQuartiles = true;
            FeatureExtractor.ACVar = true;
            FeatureExtractor.ACAbsCV = true;
            FeatureExtractor.ACIQR = true;
            FeatureExtractor.ACRange = true;
            FeatureExtractor.ACBandEnergy = true;
            FeatureExtractor.ACBandEnergy = true;
            FeatureExtractor.ACLowEnergy = true;
            FeatureExtractor.ACModVigEnergy = true;
            FeatureExtractor.ACPitch = true;
            FeatureExtractor.ACMCR = true;
            FeatureExtractor.ACCorr = true;
            FeatureExtractor.ACSF = true;
            FeatureExtractor.ACTotalSF = true;

            //DCMean
            if (DCMean)
            {
                numFeatures += extractorSensorCount * 3;
                DCMeanIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (DCMeanTotal)
            {
                numFeatures += 1;
                DCMeanTotalIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (DCArea)
            {
                numFeatures += extractorSensorCount * 3;
                DCAreaIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (DCAreaSensor)
            {
                numFeatures += extractorSensorCount;
                DCAreaSensorIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (DCPostureDist)
            {
                numFeatures += extractorSensorCount * 3;
                DCPostureDistIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACAbsMean)
            {
                numFeatures += extractorSensorCount * 3;
                ACAbsMeanIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACAbsArea)
            {
                numFeatures += extractorSensorCount * 3;
                ACAbsAreaIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACAbsAreaSensor)
            {
                numFeatures += extractorSensorCount;
                ACAbsAreaSensorIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACTotalAbsArea)
            {
                numFeatures += 1;
                ACTotalAbsAreaIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACSVM)
            {
                numFeatures += extractorSensorCount;
                ACSVMIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACTotalSVM)
            {
                numFeatures += 1;
                ACTotalSVMIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (SpectralContent)
            {
                numFeatures += NumberFrequencies * 3 * extractorSensorCount;
                ACFFTFreqsIndex += currentIndex;
                currentIndex = numFeatures;

                numFeatures += NumberFrequencies * 3 * extractorSensorCount;
                ACFFTMagsIndex += currentIndex;
                currentIndex = numFeatures;

                if (ACEntropy)
                {
                    numFeatures += 3 * extractorSensorCount;
                    ACEntropyIndex += currentIndex;
                    currentIndex = numFeatures;
                }

                if (ACEnergy)
                {
                    numFeatures += 3 * extractorSensorCount;
                    ACEnergyIndex += currentIndex;
                    currentIndex = numFeatures;
                }
            }

            if (ACSkew)
            {
                numFeatures += 3 * extractorSensorCount;
                ACSkewIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACKur)
            {
                numFeatures += 3 * extractorSensorCount;
                ACKurIndex = currentIndex;
                currentIndex = numFeatures;
            }
            if (ACQuartiles)
            {
                numFeatures += 3 * 3 * extractorSensorCount;
                ACQuartilesIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACVar)
            {
                numFeatures += 3 * extractorSensorCount;
                ACVarIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACAbsCV)
            {
                numFeatures += 3 * extractorSensorCount;
                ACAbsCVIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACIQR)
            {
                numFeatures += 3 * extractorSensorCount;
                ACIQRIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACRange)
            {
                numFeatures += 3 * extractorSensorCount;
                ACRangeIndex = currentIndex;
                currentIndex = numFeatures;
            }



            if (ACBandEnergy)
            {
                numFeatures += 3 * extractorSensorCount;
                ACBandEnergyIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACLowEnergy)
            {
                numFeatures += 3 * extractorSensorCount;
                ACLowEnergyIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACModVigEnergy)
            {
                numFeatures += 3 * extractorSensorCount;
                ACModVigEnergyIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACPitch)
            {
                numFeatures += 3 * extractorSensorCount;
                ACPitchIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACMCR)
            {
                numFeatures += 3 * extractorSensorCount;
                ACMCRIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACCorr)
            {
                numFeatures += ((FeatureExtractor.inputRowSize * FeatureExtractor.inputRowSize) - FeatureExtractor.inputRowSize) / 2;
                ACCorrIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACSF)
            {
                numFeatures += extractorSensorCount;
                ACSFIndex = currentIndex;
                currentIndex = numFeatures;
            }

            if (ACTotalSF)
            {
                numFeatures += 1;
                ACTotalSFIndex = currentIndex;
                currentIndex = numFeatures;
            }

            FFT.isComputeActivityBand = true;
            FFT.isComputeLowEnergy = true;
            FFT.isComputeModerateEnergy = true;
            FFT.isComputeRatioEnergy = true;

            //Initialize Filters
            //Low Pass Filter - 1 Hz
            LP1Hz_xv = new double[extractorSensorCount * 3][];//[LP1Hz_NZER0S+1];
            LP1Hz_yv = new double[extractorSensorCount * 3][];//[LP1Hz_NPOLES+1];
            BPpt1_20Hz_xv = new double[extractorSensorCount * 3][];
            BPpt1_20Hz_yv = new double[extractorSensorCount * 3][];

            for (int i = 0; (i < (extractorSensorCount * 3)); i++)
            {
                LP1Hz_xv[i] = new double[LP1Hz_NZER0S + 1];
                LP1Hz_yv[i] = new double[LP1Hz_NPOLES + 1];

                BPpt1_20Hz_xv[i] = new double[BPpt1_20Hz_NZER0S + 1];
                BPpt1_20Hz_yv[i] = new double[BPpt1_20Hz_NPOLES + 1];
            }


            FeatureExtractor.num_features = numFeatures;
            fv = new double[numFeatures];



            //CHANGE: gathers training samples based on the first category only 
            /*FeatureExtractor.trainingTime = new Hashtable();//int[((AXML.Category)FeatureExtractor.aannotation.Categories[0]).Labels.Count];
            foreach (AXML.Label label in ((AXML.Category)FeatureExtractor.aannotation.Categories[0]).Labels)
                FeatureExtractor.trainingTime.Add(label.Name, 0);
            FeatureExtractor.trainingCompleted = false;*/




            //FeatureExtractor.features = new double[FeatureExtractor.num_features];
           // FeatureExtractor.arffAttriburesLabels = new string[FeatureExtractor.num_features];
            //FeatureExtractor.attributeLocation = new Hashtable();

            FeatureExtractor.standardized = new double[inputRowSize][];
            for (int i = 0; (i < inputRowSize); i++)
                FeatureExtractor.standardized[i] = new double[FeatureExtractor.inputColumnSize];

            FeatureExtractor.means = new double[inputRowSize];
            FeatureExtractor.meansbp = new double[inputRowSize];
            FeatureExtractor.meanslp = new double[inputRowSize];

            inputFFT = new int[FeatureExtractor.inputColumnSize];
            FFT.Initialize(fftInterpolationPower, NumberFrequencies);
            //FeatureExtractor.aMITesDecoder = aMITesDecoder;

            //Create the ARFF File header
           /* string arffHeader = "@RELATION wockets\n\n" + FeatureExtractor.GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
            arffHeader += "@ATTRIBUTE activity {";
            foreach (AXML.Label label in ((AXML.Category)FeatureExtractor.aannotation.Categories[0]).Labels)
                arffHeader += label.Name.Replace(' ', '_') + ",";
            arffHeader += "unknown}\n";
            arffHeader += "\n@DATA\n\n";*/

            //Calculating windowing parameters

            //total number of points per interpolated window
            FeatureExtractor.INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, FeatureExtractor.configuration._FFTInterpolatedPower); //128;  

            //space between interpolated samples
            FeatureExtractor.INTERPOLATED_SAMPLES_SPACING = (double)FeatureExtractor.configuration._WindowTime / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


            //expected sampling rate per MITes
            //FeatureExtractor.EXPECTED_SAMPLING_RATE = dconfiguration.ExpectedSamplingRate / sannotation.Sensors.Count; //samples per second
            //expected samples per window
            //FeatureExtractor.EXPECTED_WINDOW_SIZE = (int)(EXPECTED_SAMPLING_RATE * (dconfiguration.WindowTime / 1000.0)); // expectedSamplingRate per window
            //what would be considered a good sampling rate
            //FeatureExtractor.EXPECTED_GOOD_SAMPLING_RATE = EXPECTED_WINDOW_SIZE - (int)(dconfiguration.MaximumNonconsecutiveFrameLoss * EXPECTED_WINDOW_SIZE); //number of packets lost per second                      
            //space between samples
            //FeatureExtractor.EXPECTED_SAMPLES_SPACING = (double)dconfiguration.WindowTime / EXPECTED_WINDOW_SIZE;
            FeatureExtractor.EXPECTED_SAMPLING_RATES = new int[FeatureExtractor.extractorSensorCount];
            FeatureExtractor.EXPECTED_WINDOW_SIZES = new int[FeatureExtractor.extractorSensorCount];
            FeatureExtractor.EXPECTED_GOOD_SAMPLING_RATES = new int[FeatureExtractor.extractorSensorCount];
            FeatureExtractor.EXPECTED_SAMPLES_SPACING = new double[FeatureExtractor.extractorSensorCount];

            //foreach (SXML.Sensor sensor in sannotation.Sensors)
/*            foreach (DictionaryEntry sensorEntry in FeatureExtractor)
            {
                //Get the channel and index in data array for only
                // extractor sensors (sensors that will be used to compute
                // features i.e. accelerometers)
                int channel = (int)sensorEntry.Key;
                int sensorIndex = (int)sensorEntry.Value;
                SXML.Sensor sensor = ((SXML.Sensor)sannotation.Sensors[(int)sannotation.SensorsIndex[channel]]);
                int receiverID = Convert.ToInt32(sensor.Receiver);

                if (channel == MITesDecoder.MAX_CHANNEL)  //Built in sensor
                    FeatureExtractor.EXPECTED_SAMPLING_RATES[sensorIndex] = sensor.SamplingRate; //used sensor sampling rate
                else
                    FeatureExtractor.EXPECTED_SAMPLING_RATES[sensorIndex] = FeatureExtractor.configuration.ExpectedSamplingRate / sannotation.NumberSensors[receiverID];

                FeatureExtractor.EXPECTED_WINDOW_SIZES[sensorIndex] = (int)(FeatureExtractor.EXPECTED_SAMPLING_RATES[sensorIndex] * (FeatureExtractor.configuration.WindowTime / 1000.0));
                FeatureExtractor.EXPECTED_GOOD_SAMPLING_RATES[sensorIndex] = FeatureExtractor.EXPECTED_WINDOW_SIZES[sensorIndex] - (int)(FeatureExtractor.configuration.MaximumNonconsecutiveFrameLoss * FeatureExtractor.EXPECTED_WINDOW_SIZES[sensorIndex]);
                FeatureExtractor.EXPECTED_SAMPLES_SPACING[sensorIndex] = (double)FeatureExtractor.configuration.WindowTime / FeatureExtractor.EXPECTED_WINDOW_SIZES[sensorIndex];
            }*/



            //window counters and delimiters
            FeatureExtractor.next_window_end = 0;
            FeatureExtractor.total_window_count = 0;
            FeatureExtractor.num_feature_windows = 0;

            //data quality variables
            FeatureExtractor.isAcceptableLossRate = true;
            FeatureExtractor.isAcceptableConsecutiveLoss = true;
            FeatureExtractor.unacceptable_window_count = 0;
            FeatureExtractor.unacceptable_consecutive_window_loss_count = 0;


            //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
            FeatureExtractor.data = new double[FeatureExtractor.extractorSensorCount * 4][]; // 1 row for each axis

            // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
            FeatureExtractor.interpolated_data = new double[FeatureExtractor.extractorSensorCount * 3][];

            // array to store the y location for each axes as data is received
            // will be different for every sensor of course
            FeatureExtractor.y_index = new int[FeatureExtractor.extractorSensorCount];


            //Initialize expected data array

           /* foreach (DictionaryEntry sensorEntry in FeatureExtractor.sensorIndicies)
            {
                //Get the channel and index in data array for only
                // extractor sensors (sensors that will be used to compute
                // features i.e. accelerometers)
                int channel = (int)sensorEntry.Key;
                int sensorIndex = (int)sensorEntry.Value;
                int adjusted_sensor_index = sensorIndex * 4;

                //Initialize 4 rows x,y,z timestamp
                for (int j = 0; j < 4; j++)
                {
                    FeatureExtractor.data[adjusted_sensor_index] = new double[EXPECTED_WINDOW_SIZES[sensorIndex]];
                    for (int k = 0; (k < EXPECTED_WINDOW_SIZES[sensorIndex]); k++)
                        FeatureExtractor.data[adjusted_sensor_index][k] = 0;
                    adjusted_sensor_index++;
                }

            }*/


            //Here it is equal across all sensors, so we do not need to consider
            //the sampling rate of each sensor separately
            for (int j = 0; (j < (FeatureExtractor.extractorSensorCount * 3)); j++)
            {
                FeatureExtractor.interpolated_data[j] = new double[INTERPOLATED_SAMPLING_RATE_PER_WINDOW];
                for (int k = 0; (k < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); k++)
                    FeatureExtractor.interpolated_data[j][k] = 0;
            }

            //Initialize y index for each sensor
            for (int j = 0; (j < FeatureExtractor.extractorSensorCount); j++)
                FeatureExtractor.y_index[j] = 0;

        }

        public static int ComputeDistance(string s, string t)
        {
            int n = s.Length;
            int m = t.Length;
            int[,] d = new int[n + 1, m + 1]; // matrix

            // Step 1
            if (n == 0)
            {
                return m;
            }

            if (m == 0)
            {
                return n;
            }

            // Step 2
            for (int i = 0; i <= n; d[i, 0] = i++)
            {
            }

            for (int j = 0; j <= m; d[0, j] = j++)
            {
            }

            // Step 3
            for (int i = 1; i <= n; i++)
            {
                //Step 4
                for (int j = 1; j <= m; j++)
                {
                    // Step 5
                    int cost = (t[j - 1] == s[i - 1]) ? 0 : 1;

                    // Step 6
                    d[i, j] = Math.Min(
                        Math.Min(d[i - 1, j] + 1, d[i, j - 1] + 1),
                        d[i - 1, j - 1] + cost);
                }
            }
            // Step 7
            return d[n, m];
        }

        public static double LevenshteinDistance(int[] s, int[] t, bool useDistanceCost, bool normalize)
        {

            double half = Math.Floor(s.Length / 2.0);
            double upperLimit = half;
            if (useDistanceCost)
            {
                if ((s.Length % 2) == 1) //even
                    upperLimit = half * (half + 1);
                else //odd
                    upperLimit = half * half;
            }

            int[][] d = new int[s.Length + 1][];

            for (int i = 0; (i < (s.Length + 1)); i++)
                d[i] = new int[t.Length + 1];

            for (int i = 0; (i < d.Length); i++)
                d[i][0] = i; //deletion
            for (int j = 0; (j < d[0].Length); j++)
                d[0][j] = j; //insertion

            for (int j = 1; (j <= t.Length); j++)
                for (int i = 1; (i <= s.Length); i++)
                {
                    //if (s[i-1] == t[j-1])
                    // d[i][j] = d[i - 1][j - 1];
                    int cost = 0;

                    if (s[i - 1] != t[j - 1])
                        if (useDistanceCost)
                        {
                            for (int k = 0; (k < t.Length); k++)
                            {
                                if (t[k] == s[i - 1])
                                {
                                    cost = Math.Abs(k - i + 1);
                                    break;
                                }
                            }

                        }
                        else
                            cost = 1;


                    // if (useDistanceCost)
                    //     d[i][j] = Math.Min(d[i - 1][j] + Math.Abs(i-1-j), Math.Min(d[i][j - 1] + Math.Abs(i-j+1), d[i - 1][j - 1] + Math.Abs(i-1-j+1)));
                    //else
                    d[i][j] = Math.Min(d[i - 1][j] + 1, Math.Min(d[i][j - 1] + 1, d[i - 1][j - 1] + cost));
                }

            if (normalize)
                return ((double)d[s.Length][t.Length]) / upperLimit;
            else
                return ((double)d[s.Length][t.Length]);
        }




        //LowPass 1Hz Butterworth
        public static double LowPass1Hz(int axis, double input)
        {
            LP1Hz_xv[axis][0] = LP1Hz_xv[axis][1];
            LP1Hz_xv[axis][1] = LP1Hz_xv[axis][2];
            LP1Hz_xv[axis][2] = input / LP1Hz_GAIN;

            LP1Hz_yv[axis][0] = LP1Hz_yv[axis][1];
            LP1Hz_yv[axis][1] = LP1Hz_yv[axis][2];
            LP1Hz_yv[axis][2] = (LP1Hz_xv[axis][0] + LP1Hz_xv[axis][2]) + 2 * LP1Hz_xv[axis][1] + (-0.9329347318 * LP1Hz_yv[axis][0]) + (1.9306064272 * LP1Hz_yv[axis][1]);
            return LP1Hz_yv[axis][2];

            //return input;
        }


        //BandPass 0.1Hz-20Hz Butterworth
        public static double BandPasspt1_20Hz_(int axis, double input)
        {
            BPpt1_20Hz_xv[axis][0] = BPpt1_20Hz_xv[axis][1];
            BPpt1_20Hz_xv[axis][1] = BPpt1_20Hz_xv[axis][2];
            BPpt1_20Hz_xv[axis][2] = BPpt1_20Hz_xv[axis][3];
            BPpt1_20Hz_xv[axis][3] = BPpt1_20Hz_xv[axis][4];
            BPpt1_20Hz_xv[axis][4] = input / BPpt1_20Hz_GAIN;

            BPpt1_20Hz_yv[axis][0] = BPpt1_20Hz_yv[axis][1];
            BPpt1_20Hz_yv[axis][1] = BPpt1_20Hz_yv[axis][2];
            BPpt1_20Hz_yv[axis][2] = BPpt1_20Hz_yv[axis][3];
            BPpt1_20Hz_yv[axis][3] = BPpt1_20Hz_yv[axis][4];

            BPpt1_20Hz_yv[axis][4] = (BPpt1_20Hz_xv[axis][0] + BPpt1_20Hz_xv[axis][4]) - 2 * BPpt1_20Hz_xv[axis][2]
                                        + (-0.2610321874 * BPpt1_20Hz_yv[axis][0]) + (1.2245774774 * BPpt1_20Hz_yv[axis][1])
                                        + (-2.6621991985 * BPpt1_20Hz_yv[axis][2]) + (2.6986404043 * BPpt1_20Hz_yv[axis][3]);
            return BPpt1_20Hz_yv[axis][4];
            //return input;
        }
        public static void ExtractOverhead(double[][] input)//,int fftInterpolationPower, int fftMaximumFrequencies)
        {


            int j = 0, i = 0;
            double min = 0, max = 0, total = 0, variance = 0;
            double sumbp = 0, sumlp = 0, sum = 0;
            double sumACAbsArea = 0;
            double[][] lpvalue = new double[input.Length][];
            double[][] bpvalue = new double[input.Length][];
            double[] bpValues = new double[FeatureExtractor.inputColumnSize];

            TextWriter overhead = new StreamWriter("Overhead.csv");

            for (i = 0; (i < inputRowSize); i++)
            {
                lpvalue[i] = new double[input[0].Length];
                bpvalue[i] = new double[input[0].Length];
            }

            //Overhead of Low Pass Filtering

            double startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        lpvalue[i][j] = LowPass1Hz(i, input[i][j]);
            double endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            double difference = endTime - startTime;
            double cost = difference;
            overhead.WriteLine("Low Pass 1Hz," + cost.ToString("0.00"));


            //Overhead of Band Pass Filtering
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        bpvalue[i][j] = BandPasspt1_20Hz_(i, input[i][j]);
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Band Pass 1-20Hz," + cost.ToString("0.00"));



            int meanIndex = DCMeanIndex;
            double meanlp = 0, meanbp = 0, mean = 0;
            double acAbsMean = 0;

            double meanTotal = 0;
            double acAbsSum = 0;
            double acTotalAbsArea = 0;
            double[] acSVMSensor = new double[FeatureExtractor.inputColumnSize];
            double acTotalSVM = 0;
            double acTotalSF = 0;


            int dcMeanIndex = DCMeanIndex;
            int dcMeanTotalIndex = DCMeanTotalIndex;
            int dcAreaIndex = DCAreaIndex;
            int dcAreaSensorIndex = DCAreaSensorIndex;
            int dcPostureDistIndex = DCPostureDistIndex;
            int acAbsMeanIndex = ACAbsMeanIndex;
            int acAbsAreaIndex = ACAbsAreaIndex;
            int acAbsAreaSensorIndex = ACAbsAreaSensorIndex;
            int acTotalAbsAreaIndex = ACTotalAbsAreaIndex;
            int acSVMIndex = ACSVMIndex;
            int acTotalSVMIndex = ACTotalSVMIndex;
            int acFFTFreqsIndex = ACFFTFreqsIndex;
            int acFFTMagsIndex = ACFFTMagsIndex;
            int acEntropyIndex = ACEntropyIndex;
            int acEnergyIndex = ACEnergyIndex;
            int acSkewIndex = ACSkewIndex;
            int acKurIndex = ACKurIndex;
            int acQuartilesIndex = ACQuartilesIndex;
            int acVarIndex = ACVarIndex;
            int acAbsCVIndex = ACAbsCVIndex;
            int acIQRIndex = ACIQRIndex;
            int acRangeIndex = ACRangeIndex;
            int acBandEnergyIndex = ACBandEnergyIndex;
            int acLowEnergyIndex = ACLowEnergyIndex;
            int acModVigEnergyIndex = ACModVigEnergyIndex;
            int acPitchIndex = ACPitchIndex;
            int acMCRIndex = ACMCRIndex;
            int acCorrIndex = ACCorrIndex;
            int acSFIndex = ACSFIndex;
            int acTotalSFIndex = ACTotalSFIndex;


            //Overhead of Means
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        sumbp += bpvalue[i][j];
                    meanbp = sumbp / FeatureExtractor.inputColumnSize;
                    meansbp[i] = meanbp;
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Means," + cost.ToString("0.00"));




            //Overhead of Range
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                    {
                        if (bpvalue[i][j] < min)
                            min = bpvalue[i][j];
                        if (bpvalue[i][j] > max)
                            max = bpvalue[i][j];
                    }
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Range," + cost.ToString("0.00"));


            //Overhead of Pitch
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    sumlp = 0;
                    sum = 0;
                    sumbp = 0;
                    acAbsSum = 0;
                    min = 999999999.0;
                    max = -999999999.0;
                    double cubicSum = 0;
                    double squaredSum = 0;
                    double fourthSum = 0;
                    double acfSum = 0;
                    double[] acf = new double[FeatureExtractor.inputColumnSize];


                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        sumbp += bpvalue[i][j];
                    meanbp = sumbp / FeatureExtractor.inputColumnSize;
                    meansbp[i] = meanbp;

                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                    {
                        sumbp += bpvalue[i][j];
                        bpValues[j] = bpvalue[i][j];
                        squaredSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 2.0);
                    }
                    meanbp = sumbp / FeatureExtractor.inputColumnSize;
                    meansbp[i] = meanbp;

                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                    {

                        acfSum = 0;
                        for (int k = 0; (k < (FeatureExtractor.inputColumnSize - j)); k++)
                            acfSum += (bpvalue[i][k] - meansbp[i]) * (bpvalue[i][k + j] - meansbp[i]);
                        acf[j] = acfSum;

                    }
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        acf[j] /= squaredSum;

                    //pick the first minimum
                    double minACF = 99999999.0;
                    int minK = 0;
                    for (int k = 0; (k < FeatureExtractor.inputColumnSize); k++)
                        if (acf[k] < minACF)
                        {
                            minK = k;
                            minACF = acf[k];
                            if (minACF < 0.001)
                                break;
                        }

                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Pitch," + cost.ToString("0.00"));



            //Overhead of Skewness
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {

                    double cubicSum = 0;
                    double squaredSum = 0;

                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        sumbp += bpvalue[i][j];
                    meanbp = sumbp / FeatureExtractor.inputColumnSize;
                    meansbp[i] = meanbp;
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                    {
                        squaredSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 2.0);
                        cubicSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 3.0);
                    }
                    double skew = (cubicSum * Math.Sqrt(FeatureExtractor.inputColumnSize)) / Math.Pow(squaredSum, 1.5);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Skewness," + cost.ToString("0.00"));


            //Overhead of Kurtosis
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {

                    double fourthSum = 0;
                    double squaredSum = 0;
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        sumbp += bpvalue[i][j];
                    meanbp = sumbp / FeatureExtractor.inputColumnSize;
                    meansbp[i] = meanbp;
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                    {
                        squaredSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 2.0);
                        fourthSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 4.0);
                    }
                    double kurtosis = ((fourthSum * FeatureExtractor.inputColumnSize) / Math.Pow(squaredSum, 2.0));
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Kurtosis," + cost.ToString("0.00"));

            //overhead of FFT Mags
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateFFTMags(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTMags," + cost.ToString("0.00"));

            //overhead of FFT Energy
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateFFTEnergy(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTEnergy," + cost.ToString("0.00"));

            //overhead of FFT Entropy
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateFFTEntropy(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTEntropy," + cost.ToString("0.00"));


            //overhead of FFT Entropy
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateLowEnergy(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTLowEnergy," + cost.ToString("0.00"));


            //overhead of FFT Activity Band
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateActivityBand(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTActivityBand," + cost.ToString("0.00"));

            //overhead of FFT Moderate Energy
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateModerateEnergy(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTModerateEnergy," + cost.ToString("0.00"));

            //overhead of FFT RatioEnergy
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateRatioEnergy(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTRatioEnergy," + cost.ToString("0.00"));

            //overhead of FFT RatioEnergy
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        inputFFT[j] = (int)(bpvalue[i][j] * 1000.0);
                    FFT.CalculateMaximumFrequencies(inputFFT);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("FFTMaximumFrequencies," + cost.ToString("0.00"));



            //Overhead of Variance
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {

                    double squaredSum = 0;
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        sumbp += bpvalue[i][j];
                    meanbp = sumbp / FeatureExtractor.inputColumnSize;
                    meansbp[i] = meanbp;
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                    {
                        squaredSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 2.0);
                    }
                    double var = squaredSum / (FeatureExtractor.inputColumnSize - 1);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Variance," + cost.ToString("0.00"));



            //Overhead of SVM
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {

                    double squaredSum = 0;
                    for (j = 0; (j < FeatureExtractor.inputColumnSize); j++)
                        acSVMSensor[j] += Math.Pow(bpvalue[i][j], 2.0);

                    double totalSVM = 0;
                    for (int k = 0; (k < FeatureExtractor.inputColumnSize); k++)
                    {
                        totalSVM += Math.Sqrt(acSVMSensor[k]);
                        acSVMSensor[k] = 0;
                    }
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("SVM," + cost.ToString("0.00"));

            //Overhead of Quartile
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    Wockets.Utils.QuickSort.Sort(bpValues, 0, bpValues.Length - 1);
                }
            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Quartiles," + cost.ToString("0.00"));



            //Overhead of Crossings
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {

                    int numCrossings = 0;
                    for (int k = 1; (k < FeatureExtractor.inputColumnSize); k++)
                        if (((bpValues[k] > meansbp[i]) && (bpValues[k - 1] <= meansbp[i])) ||
                             ((bpValues[k] < meansbp[i]) && (bpValues[k - 1] >= meansbp[i])))
                            numCrossings++;
                }


            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Crossings," + cost.ToString("0.00"));

            //Overhead of Correlations
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int m = 0; (m < 10); m++)
                for (i = 0; (i < inputRowSize); i++)
                {

                    //***correlation coefficients
                    for (int k = i - 1; k >= 0; k--)
                    {
                        double t = 0;
                        for (int w = 0; (w < FeatureExtractor.inputColumnSize); w++)
                            t += standardized[i][w] * standardized[k][w];
                        t /= (FeatureExtractor.inputColumnSize - 1);
                        t /= Math.Sqrt(fv[acVarIndex - 1]);  // ith std deviation
                        t /= Math.Sqrt(fv[acVarIndex - 1 - (i - k)]);  //kth std deviation 
                        acCorrIndex++;
                    }
                }


            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Correlations," + cost.ToString("0.00"));


            //Overhead of Segmental Force
            startTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            for (int z = 0; (z < 10); z++)
                for (i = 0; (i < inputRowSize); i++)
                {
                    int location = i / 3;
                    int currenLimbIndex = -1;
                    for (int m = 0; (m < limbsIndex.Length); m++)
                        if (limbsIndex[m] == location)
                        {
                            currenLimbIndex = m;
                            break;
                        }
                    if (currenLimbIndex >= 0)
                    {
                        double sgForce = limbs[currenLimbIndex] * fv[ACAbsAreaSensorIndex + limbsIndex[currenLimbIndex] - 1];
                        fv[acSFIndex + currenLimbIndex] = sgForce;
                        acTotalSF += fv[acSFIndex + currenLimbIndex];
                    }
                }


            endTime = Wockets.Utils.WocketsTimer.GetUnixTime();
            difference = endTime - startTime;
            cost = difference;
            overhead.WriteLine("Segmental Force," + cost.ToString("0.00"));
            overhead.Close();
            //Environment.Exit(0);


        }


        public static double StoreWocketsWindow()
        {
            double unixtimestamp = 0.0;

            //  for (int i = 0; i < FeatureExtractor.wocketsController._Decoders.Count; i++)
            //     for (int j=0;(j<FeatureExtractor.wocketsController._Decoders[i]._Size);j++)


            for (int i = 0; i < FeatureExtractor.wocketsController._Decoders.Count; i++)
            {
                AccelerationData datum = ((AccelerationData)FeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]);
                int currentHead = FeatureExtractor.wocketsController._Decoders[i]._Head;
                while ((tail[i] != currentHead) && (datum.UnixTimeStamp > 0) && (datum.UnixTimeStamp >= tailUnixtimestamp[i]))
                {
                    int x = 0, y = 0, z = 0;
                    x = (int)((AccelerationData)FeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).X;
                    y = (int)((AccelerationData)FeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).Y;
                    z = (int)((AccelerationData)FeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).Z;
                    unixtimestamp = ((AccelerationData)FeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]).UnixTimeStamp;
                    tailUnixtimestamp[i] = unixtimestamp;
                    if (tail[i] >= (FeatureExtractor.wocketsController._Decoders[i]._Data.Length - 1))
                        tail[i] = 0;
                    else
                        tail[i]++;

                    int sensorIndex = i * 4;
                    // store the values in the current frame in the correct column based of the EXPECTED_WINDOW data array
                    // on the y_index for the sensor
                    FeatureExtractor.data[sensorIndex][FeatureExtractor.y_index[i]] = x;
                    FeatureExtractor.data[sensorIndex + 1][FeatureExtractor.y_index[i]] = y;
                    FeatureExtractor.data[sensorIndex + 2][FeatureExtractor.y_index[i]] = z;
                    FeatureExtractor.data[sensorIndex + 3][FeatureExtractor.y_index[i]] = unixtimestamp;
                    //if (unixtimestamp < 1000)
                    //   throw new Exception("BUG");

                    //increment the y_index for the sensor and wrap around if needed
                    FeatureExtractor.y_index[i] = (FeatureExtractor.y_index[i] + 1) % FeatureExtractor.EXPECTED_WINDOW_SIZES[i];
                    datum = ((AccelerationData)FeatureExtractor.wocketsController._Decoders[i]._Data[tail[i]]);
                }

            }

            return unixtimestamp;

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
            double window_start_time = lastTimeStamp - configuration._WindowTime;
            double window_end_time = lastTimeStamp;
            double current_time = window_end_time;
            //compute the end of the next overlapping window
            next_window_end = window_end_time + (configuration._WindowTime * configuration._WindowOverlap);

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
                    if (distinct_data_points < FeatureExtractor.EXPECTED_GOOD_SAMPLING_RATES[j]) //discard this whole window of data
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
                    double expectedSpacing = configuration._WindowTime / (double)distinct_data_points;
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
                //FeatureExtractor.Extract(interpolated_data);
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
            FFT.Cleanup();
            //for (int i = 0; (i < Extractor.sannotation.Sensors.Count); i++)            
            //   spacingtws[i].Close();            
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
