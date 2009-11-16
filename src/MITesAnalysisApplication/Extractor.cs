using System;
using System.Collections.Generic;
using System.Text;
using WocketsWeka.core;
using System.IO;
using HousenCS.MITes;
using WocketsWeka.Utils;
using WocketsWeka;
using MITesAnalysisApplication.conf;
using System.Collections;
using System.Text.RegularExpressions;

namespace MITesAnalysisApplication
{
    public class Extractor
    {
        private static double[] features;
        private static double[][] standardized;
        private static double[] meanslp;
        private static double[] meansbp;
        private static double[] means;
        private static double[] variances;
        private static int[] inputFFT;

        private static bool autoMode = false;

        private static int num_features = 0;
        private static int inputRowSize;
        private static int inputColumnSize;
        private static int fftInterpolationPower;
        private static int fftMaximumFrequencies;
        //private static int trainingTimePerClass;
        //private static int trainingWaitTime;
        private static MITesDecoder aMITesDecoder;
        private static SXML.SensorAnnotation sannotation;
        private static AXML.Annotation aannotation;
        //private static int lastTrainedActivity = "";
        private static GeneralConfiguration dconfiguration;
        private static string[] arffAttriburesLabels;
        private static Hashtable attributeLocation;

        private static int discardedLossRateWindows = 0;
        private static int discardedConsecutiveLossWindows = 0;
        private static double averageLossRate;

        //Calculating windowing parameters


        //total number of points per interpolated window
        private static int INTERPOLATED_SAMPLING_RATE_PER_WINDOW;
        //space between interpolated samples
        private static double INTERPOLATED_SAMPLES_SPACING;

        /////REPLACED
        //Each MIT may have a different value
        //expected sampling rate per MITes
        //private static int EXPECTED_SAMPLING_RATE;
        //expected samples per window
        //private static int EXPECTED_WINDOW_SIZE;
        //what would be considered a good sampling rate
        //private static int EXPECTED_GOOD_SAMPLING_RATE;
        //space between samples
        //public static double EXPECTED_SAMPLES_SPACING;

        private static int[] EXPECTED_SAMPLING_RATES;
        private static int[] EXPECTED_WINDOW_SIZES;
        private static int[] EXPECTED_GOOD_SAMPLING_RATES;
        private static double[] EXPECTED_SAMPLES_SPACING;

        private static int extractorSensorCount;
        private static Hashtable sensorIndicies;

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


        private static double WINDOWING_START_TIME = 0.0;
        private static double WINDOWING_END_TIME = 0.0;

        //realtime variables
        private static Hashtable trainingTime;
        private static bool trainingCompleted = false;

        public static int DiscardedLossRateWindows
        {
            get
            {
                return Extractor.discardedLossRateWindows;
            }
        }

        public static int DiscardedConsecutiveLossWindows
        {
            get
            {
                return Extractor.discardedConsecutiveLossWindows;
            }
        }

        public static double AverageLossRate
        {
            get
            {
                return Extractor.averageLossRate;
            }
        }
        public static GeneralConfiguration Configuration
        {
            get
            {
                return Extractor.dconfiguration;
            }
        }
        public static bool AutoMode
        {
            set
            {
                Extractor.autoMode = value;
            }
            get
            {
                return Extractor.autoMode;
            }
        }
        public static Hashtable TrainingTime
        {
            get
            {
                return Extractor.trainingTime;
            }

        }

        public static bool IsTrained(string activity)
        {
            if (activity.Equals(""))
                return false;

            //int index = -1;
            //for (int i = 0; (i < ((AXML.Category)aannotation.Categories[0]).Labels.Count); i++)
            //if (((AXML.Label)((AXML.Category)aannotation.Categories[0]).Labels[i]).Name == activity)
            //  index = i;
            //if ((index!=-1) &&(Extractor.trainingTime[index] < Extractor.dconfiguration.TrainingTime))
            if ((int)Extractor.trainingTime[activity] < (Extractor.dconfiguration.TrainingTime * 1000))
                return false;

            return true;
        }



        public static bool IsTrainingCompleted()
        {
            if (trainingCompleted)
                return trainingCompleted;
            else
            {
                //for (int i = 0; (i < Extractor.trainingTime); i++)
                foreach (string activity in Extractor.trainingTime.Keys)
                {
                    if ((int)Extractor.trainingTime[activity] < (Extractor.dconfiguration.TrainingTime * 1000))
                        return false;

                }

                Extractor.trainingCompleted = true;
                return true;
            }
        }

        public static string[] ArffAttributeLabels
        {
            get
            {
                return Extractor.arffAttriburesLabels;
            }
        }

        public static Hashtable AttributeLocation
        {
            get
            {
                return Extractor.attributeLocation;
            }
        }

        public static double[] Features
        {
            get
            {
                return Extractor.features;
            }
        }

        public static void Initialize(int inputRowSize, int fftInterpolationPower, int fftMaximumFrequencies)
        {
            Extractor.inputRowSize = inputRowSize;
            Extractor.fftInterpolationPower = fftInterpolationPower;
            Extractor.fftMaximumFrequencies = fftMaximumFrequencies;
            Extractor.inputColumnSize = (int)Math.Pow(2, Extractor.fftInterpolationPower);


            Extractor.num_features = Extractor.inputRowSize; // number of distances
            Extractor.num_features += 1; //total mean;
            Extractor.num_features += Extractor.inputRowSize; // number of variances
            Extractor.num_features += Extractor.inputRowSize; // number of ranges
            Extractor.num_features += 2 * Extractor.fftMaximumFrequencies * Extractor.inputRowSize; // number of fft magnitudes and frequencies
            Extractor.num_features += Extractor.inputRowSize; // number of energies
            Extractor.num_features += ((Extractor.inputRowSize * Extractor.inputRowSize) - Extractor.inputRowSize) / 2; //correlation coefficients off-di
            Extractor.features = new double[Extractor.num_features];
            Extractor.standardized = new double[inputRowSize][];
            for (int i = 0; (i < inputRowSize); i++)
                Extractor.standardized[i] = new double[Extractor.inputColumnSize];//input[0].Length];

            Extractor.means = new double[inputRowSize];

            inputFFT = new int[Extractor.inputColumnSize];
            FFT.Initialize(fftInterpolationPower, fftMaximumFrequencies);

        }


        public static void SetMITesDecoder(MITesDecoder aMITesDecoder)
        {
            Extractor.aMITesDecoder = aMITesDecoder;
        }
        public static void Initialize(MITesDecoder aMITesDecoder, string aDataDirectory,
            AXML.Annotation aannotation, SXML.SensorAnnotation sannotation, GeneralConfiguration configuration)//, string masterDirectory)
        {

            Extractor.aannotation = aannotation;
            Extractor.sannotation = sannotation;
            Extractor.dconfiguration = configuration;

            // count the sensors for feature extraction and identify their indicies in
            // sensor annotation - at the moment only accelerometers are used
            Extractor.sensorIndicies = new Hashtable();
            Extractor.extractorSensorCount = 0;
            foreach (SXML.Sensor sensor in sannotation.Sensors)
            {
                int channel = Convert.ToInt32(sensor.ID);
                if (channel > 0) // if accelerometer
                {
                    Extractor.sensorIndicies[channel] = extractorSensorCount;
                    Extractor.extractorSensorCount++;
                }
            }




            //load sensor data
            //SXML.Reader sreader = new SXML.Reader(masterDirectory, aDataDirectory);
            //Extractor.sannotation = sreader.parse();

            //load configuration
            //           ConfigurationReader creader = new ConfigurationReader(aDataDirectory);
            //           Extractor.dconfiguration = creader.parse();


            //load annotation data
            //AXML.Reader reader = new AXML.Reader(masterDirectory, aDataDirectory + "\\" + AXML.Reader.DEFAULT_XML_FILE);
            //Extractor.aannotation = reader.parse();          
            //CHANGE: gathers training samples based on the first category only 
            Extractor.trainingTime = new Hashtable();//int[((AXML.Category)Extractor.aannotation.Categories[0]).Labels.Count];
            //for (int i = 0; (i < Extractor.trainingTime.Length); i++)
            foreach (AXML.Label label in ((AXML.Category)Extractor.aannotation.Categories[0]).Labels)
                Extractor.trainingTime.Add(label.Name, 0);
            //Extractor.trainingTime[i] = 0;
            Extractor.trainingCompleted = false;

            Extractor.inputRowSize = Extractor.extractorSensorCount * 3;
            Extractor.fftInterpolationPower = dconfiguration.FFTInterpolatedPower;
            Extractor.fftMaximumFrequencies = dconfiguration.FFTMaximumFrequencies;
            //Extractor.trainingTimePerClass = configuration.TrainingTime;
            //Extractor.trainingWaitTime = configuration.TrainingWaitTime;         
            Extractor.inputColumnSize = (int)Math.Pow(2, Extractor.fftInterpolationPower);


            Extractor.num_features = Extractor.inputRowSize; // number of distances
            Extractor.num_features += 1; //total mean;
            Extractor.num_features += Extractor.inputRowSize; // number of variances
            Extractor.num_features += Extractor.inputRowSize; // number of ranges
            Extractor.num_features += 2 * Extractor.fftMaximumFrequencies * Extractor.inputRowSize; // number of fft magnitudes and frequencies
            Extractor.num_features += Extractor.inputRowSize; // number of energies
            Extractor.num_features += ((Extractor.inputRowSize * Extractor.inputRowSize) - Extractor.inputRowSize) / 2; //correlation coefficients off-di
            Extractor.features = new double[Extractor.num_features];
            Extractor.arffAttriburesLabels = new string[Extractor.num_features];
            Extractor.attributeLocation = new Hashtable();

            Extractor.standardized = new double[inputRowSize][];
            for (int i = 0; (i < inputRowSize); i++)
                Extractor.standardized[i] = new double[Extractor.inputColumnSize];//input[0].Length];

            Extractor.means = new double[inputRowSize];

            inputFFT = new int[Extractor.inputColumnSize];
            FFT.Initialize(fftInterpolationPower, fftMaximumFrequencies);
            Extractor.aMITesDecoder = aMITesDecoder;

            //Create the ARFF File header
            string arffHeader = "@RELATION wockets\n\n" + Extractor.GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
            arffHeader += "@ATTRIBUTE activity {";
            foreach (AXML.Label label in ((AXML.Category)Extractor.aannotation.Categories[0]).Labels)
                arffHeader += label.Name.Replace(' ', '_') + ",";
            arffHeader += "unknown}\n";
            arffHeader += "\n@DATA\n\n";

            //Calculating windowing parameters

            //total number of points per interpolated window
            Extractor.INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, dconfiguration.FFTInterpolatedPower); //128;  

            //space between interpolated samples
            Extractor.INTERPOLATED_SAMPLES_SPACING = (double)dconfiguration.WindowTime / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


            //expected sampling rate per MITes
            //Extractor.EXPECTED_SAMPLING_RATE = dconfiguration.ExpectedSamplingRate / sannotation.Sensors.Count; //samples per second
            //expected samples per window
            //Extractor.EXPECTED_WINDOW_SIZE = (int)(EXPECTED_SAMPLING_RATE * (dconfiguration.WindowTime / 1000.0)); // expectedSamplingRate per window
            //what would be considered a good sampling rate
            //Extractor.EXPECTED_GOOD_SAMPLING_RATE = EXPECTED_WINDOW_SIZE - (int)(dconfiguration.MaximumNonconsecutiveFrameLoss * EXPECTED_WINDOW_SIZE); //number of packets lost per second                      
            //space between samples
            //Extractor.EXPECTED_SAMPLES_SPACING = (double)dconfiguration.WindowTime / EXPECTED_WINDOW_SIZE;
            Extractor.EXPECTED_SAMPLING_RATES = new int[Extractor.extractorSensorCount];
            Extractor.EXPECTED_WINDOW_SIZES = new int[Extractor.extractorSensorCount];
            Extractor.EXPECTED_GOOD_SAMPLING_RATES = new int[Extractor.extractorSensorCount];
            Extractor.EXPECTED_SAMPLES_SPACING = new double[Extractor.extractorSensorCount];

            //foreach (SXML.Sensor sensor in sannotation.Sensors)
            foreach (DictionaryEntry sensorEntry in Extractor.sensorIndicies)
            {
                //Get the channel and index in data array for only
                // extractor sensors (sensors that will be used to compute
                // features i.e. accelerometers)
                int channel = (int)sensorEntry.Key;
                int sensorIndex = (int)sensorEntry.Value;
                SXML.Sensor sensor = ((SXML.Sensor)sannotation.Sensors[(int)sannotation.SensorsIndex[channel]]);
                int receiverID = Convert.ToInt32(sensor.Receiver);

                if (channel == MITesDecoder.MAX_CHANNEL)  //Built in sensor
                    Extractor.EXPECTED_SAMPLING_RATES[sensorIndex] = sensor.SamplingRate; //used sensor sampling rate
                else
                    Extractor.EXPECTED_SAMPLING_RATES[sensorIndex] = dconfiguration.ExpectedSamplingRate / sannotation.NumberSensors[receiverID];

                Extractor.EXPECTED_WINDOW_SIZES[sensorIndex] = (int)(Extractor.EXPECTED_SAMPLING_RATES[sensorIndex] * (dconfiguration.WindowTime / 1000.0));
                Extractor.EXPECTED_GOOD_SAMPLING_RATES[sensorIndex] = Extractor.EXPECTED_WINDOW_SIZES[sensorIndex] - (int)(dconfiguration.MaximumNonconsecutiveFrameLoss * Extractor.EXPECTED_WINDOW_SIZES[sensorIndex]);
                Extractor.EXPECTED_SAMPLES_SPACING[sensorIndex] = (double)dconfiguration.WindowTime / Extractor.EXPECTED_WINDOW_SIZES[sensorIndex];
            }



            //window counters and delimiters
            Extractor.next_window_end = 0;
            Extractor.total_window_count = 0;
            Extractor.num_feature_windows = 0;

            //data quality variables
            Extractor.isAcceptableLossRate = true;
            Extractor.isAcceptableConsecutiveLoss = true;
            Extractor.unacceptable_window_count = 0;
            Extractor.unacceptable_consecutive_window_loss_count = 0;


            //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
            Extractor.data = new double[Extractor.extractorSensorCount * 4][]; // 1 row for each axis

            // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
            Extractor.interpolated_data = new double[Extractor.extractorSensorCount * 3][];

            // array to store the y location for each axes as data is received
            // will be different for every sensor of course
            Extractor.y_index = new int[Extractor.extractorSensorCount];


            //Initialize expected data array

            foreach (DictionaryEntry sensorEntry in Extractor.sensorIndicies)
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
                    Extractor.data[adjusted_sensor_index] = new double[EXPECTED_WINDOW_SIZES[sensorIndex]];
                    for (int k = 0; (k < EXPECTED_WINDOW_SIZES[sensorIndex]); k++)
                        Extractor.data[adjusted_sensor_index][k] = 0;
                    adjusted_sensor_index++;
                }

            }


            //Here it is equal across all sensors, so we do not need to consider
            //the sampling rate of each sensor separately
            for (int j = 0; (j < (Extractor.extractorSensorCount * 3)); j++)
            {
                Extractor.interpolated_data[j] = new double[INTERPOLATED_SAMPLING_RATE_PER_WINDOW];
                for (int k = 0; (k < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); k++)
                    Extractor.interpolated_data[j][k] = 0;
            }

            //Initialize y index for each sensor
            for (int j = 0; (j < Extractor.extractorSensorCount); j++)
                Extractor.y_index[j] = 0;

        }









        public static double StoreBuiltinData(GenericAccelerometerData polledData)
        {
            int sensorIndex = (int)Extractor.sensorIndicies[polledData.ChannelID];
            int adjusted_sensor_index = sensorIndex * 4;
            Extractor.data[adjusted_sensor_index][Extractor.y_index[sensorIndex]] = polledData.X;
            Extractor.data[adjusted_sensor_index + 1][Extractor.y_index[sensorIndex]] = polledData.Y;
            Extractor.data[adjusted_sensor_index + 2][Extractor.y_index[sensorIndex]] = polledData.Z;
            Extractor.data[adjusted_sensor_index + 3][Extractor.y_index[sensorIndex]] = polledData.Unixtimestamp;

            //increment the y_index for the sensor and wrap around if needed
            Extractor.y_index[sensorIndex] = (Extractor.y_index[sensorIndex] + 1) % Extractor.EXPECTED_WINDOW_SIZES[sensorIndex];

            return polledData.Unixtimestamp;
        }

        //start collecting features from MITes decoder, do windowing plus calculate features
        public static double StoreMITesWindow()
        {
            double unixtimestamp = 0.0;

            for (int i = 0; i < Extractor.aMITesDecoder.someMITesDataIndex; i++)
            {
                if ((aMITesDecoder.someMITesData[i].channel == MITesDecoder.MAX_CHANNEL) ||  //built in
                    ((aMITesDecoder.someMITesData[i].type != (int)MITesTypes.NOISE) &&
                     (aMITesDecoder.someMITesData[i].type == (int)MITesTypes.ACCEL)))
                {
                    int channel = 0, x = 0, y = 0, z = 0;
                    channel = (int)aMITesDecoder.someMITesData[i].channel;
                    x = (int)aMITesDecoder.someMITesData[i].x;
                    y = (int)aMITesDecoder.someMITesData[i].y;
                    z = (int)aMITesDecoder.someMITesData[i].z;
                    unixtimestamp = aMITesDecoder.someMITesData[i].unixTimeStamp;

                    // skip channels that are not in the extractor expected
                    // sensor channels
                    if (Extractor.sensorIndicies.Contains(channel) == false)
                        continue;

                    int sensorIndex = (int)Extractor.sensorIndicies[channel];
                    //calculate the x index in the data array for this particular sensor
                    int adjusted_sensor_index = sensorIndex * 4; //base row for storing x,y,z,timestamp for this channel

                    // store the values in the current frame in the correct column based of the EXPECTED_WINDOW data array
                    // on the y_index for the sensor
                    Extractor.data[adjusted_sensor_index][Extractor.y_index[sensorIndex]] = x;
                    Extractor.data[adjusted_sensor_index + 1][Extractor.y_index[sensorIndex]] = y;
                    Extractor.data[adjusted_sensor_index + 2][Extractor.y_index[sensorIndex]] = z;
                    Extractor.data[adjusted_sensor_index + 3][Extractor.y_index[sensorIndex]] = unixtimestamp;

                    //increment the y_index for the sensor and wrap around if needed
                    Extractor.y_index[sensorIndex] = (Extractor.y_index[sensorIndex] + 1) % Extractor.EXPECTED_WINDOW_SIZES[sensorIndex];

                }

            }

            return unixtimestamp;

        }

        public static bool GenerateFeatureVector(double lastTimeStamp)
        {

            // Generate a feature vector only, if the next window end has
            // passed based on the configuration parameters (window size and overlap)
            // otherwise return false
            if (lastTimeStamp < Extractor.next_window_end)
                return false;

            // the last time stamp is more than the next expected window end
            // At this point, we have a complete window ready for feature calculation

            //compute the boundaries for the current window
            double window_start_time = lastTimeStamp - Extractor.dconfiguration.WindowTime;
            double window_end_time = lastTimeStamp;
            double current_time = window_end_time;
            //compute the end of the next overlapping window
            next_window_end = window_end_time + (Extractor.dconfiguration.WindowTime * Extractor.dconfiguration.WindowOverlap);

            #region sensors window grabbing and interpolation

            // Go through each sensor and extract the collected data within 
            // the current time window
            for (int j = 0; (j < Extractor.extractorSensorCount); j++)
            {

                // Check that the previous sensor in the loop did not report
                // deteriorated quality for its data
                #region sensors window quality
                if (isAcceptableLossRate == false)
                    break;

                // check if earlier axes reported excessive consecutive loss of data frames
                if (isAcceptableConsecutiveLoss == false)
                {
                    Extractor.discardedConsecutiveLossWindows++;
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
                    last_sample = Extractor.EXPECTED_WINDOW_SIZES[j] - 1;
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
                    double[] xvals = new double[Extractor.EXPECTED_WINDOW_SIZES[j]];
                    double[] yvals = new double[Extractor.EXPECTED_WINDOW_SIZES[j]];

                    //point to the last sample that was read and get its time
                    int sample_index = last_sample;
                    current_time = data[time_index][sample_index];

                    //copy samples in the last time window
                    //                    total_data_points = 0;
                    distinct_data_points = 0;
                    //                    double previous_time = 0;
                    //Grab the values for a specific sensor axes between
                    //window start and window end
                    #region window grabbing
                    // Start going back from the current time (window end) till the start of the window
                    // without exceeding the expected sampling rate and fill in the data in the signal
                    // value for the axis in yvals and the relative time value from the window start
                    while ((current_time >= window_start_time) && (current_time <= window_end_time)
                         && (distinct_data_points < Extractor.EXPECTED_WINDOW_SIZES[j]))
                    {

                        //some time stamps from the mites are identical
                        // for interpolation that will cause an error
                        // simply take the first value for a time point and ignore the
                        // rest, another strategy would be to average over these values
                        //if (current_time == previous_time)
                        //{
                        //    //Get the time of the previous sample and skip the sample
                        //    if (sample_index == 0)
                        //        sample_index = EXPECTED_WINDOW_SIZE - 1;
                        //    else
                        //        sample_index--;
                        //    current_time = data[time_index][sample_index];
                        //    total_data_points++;
                        //    continue;
                        //}

                        // Quality Control
                        // check the time between consecutive data frames and make sure it does
                        // not exceed maximum_consecutive_loss, do not do that for the first
                        // entry of the window
                        // Not suitable for the phone due to time resolution
                        //if (distinct_data_points > 0)
                        //{
                        //    int consecutive_lost_packets = (int)((previous_time - current_time) / EXPECTED_SAMPLES_SPACING);
                        //    if (consecutive_lost_packets > Extractor.dconfiguration.MaximumConsecutiveFrameLoss)
                        //    {
                        //        Extractor.discardedConsecutiveLossWindows++;      
                        //        unacceptable_consecutive_window_loss_count++;
                        //        isAcceptableConsecutiveLoss = false;
                        //        break;
                        //    }
                        //}



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


                        //Point to the previous sample in the current window
                        if (sample_index == 0)
                            sample_index = Extractor.EXPECTED_WINDOW_SIZES[j] - 1;
                        else
                            sample_index--;

                        //store the previous sample time
                        //                        previous_time = current_time;

                        //Get the time of the new sample
                        current_time = data[time_index][sample_index];

                        //Point to the next entry in the interpolation array
                        distinct_data_points++;

                        //                        total_data_points++;
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
                    if (distinct_data_points < Extractor.EXPECTED_GOOD_SAMPLING_RATES[j]) //discard this whole window of data
                    {
                        Extractor.discardedLossRateWindows++;
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
                    double expectedSpacing = Extractor.dconfiguration.WindowTime / (double)distinct_data_points;
                    double startTime = 0.0;
                    for (int k = 0; (k < distinct_data_points); k++)
                    {
                        admissible_xvals[k] = startTime + k * expectedSpacing;//xvals[distinct_data_points - k - 1];
                        admissible_yvals[k] = yvals[distinct_data_points - k - 1];
                    }
                    //if (spacingtws == null)
                    // {
                    //     spacingtws = new TextWriter[Extractor.sannotation.Sensors.Count];
                    //     for (int i = 0; (i < Extractor.sannotation.Sensors.Count); i++)
                    //    {
                    //        spacingtws[i] = new StreamWriter("\\test\\" + "SensorSpacing" + i + ".txt");
                    //    }
                    // }

                    // smooth it using a cubic spline
                    CubicSpline cs = new CubicSpline(admissible_xvals, admissible_yvals);

                    //startval = xvals[distinct_data_points - 1].ToString("00.00");
                    // shrink or expand the data window using interpolation                
                    for (int k = 0; (k < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); k++)
                    {
                        interpolated_data[interpolated_axes_index][k] = cs.interpolate(k * INTERPOLATED_SAMPLES_SPACING);
                        //check that the intrepolated values make sense.
                        //if ((interpolated_data[interpolated_axes_index][k] <= 0) || (interpolated_data[interpolated_axes_index][k] > 1024))
                        if ((interpolated_data[interpolated_axes_index][k] <= -6000) || (interpolated_data[interpolated_axes_index][k] > 6000))
                        {
                            //  errorFlag = 1;
                            return false;
                        }
                    }


                    #endregion window interpolation
                }
                #endregion sensor window grabbing and interpolation

                //spacingtws[j].WriteLine(startval);

            }
            #endregion sensors window grabbing and interpolation

            //If the data is of acceptable quality, calculate the features
            #region Calculate Feature Vector

            if ((isAcceptableLossRate == true) && (isAcceptableConsecutiveLoss == true))
            {
                //Extract the features from the interpolated data
                //Extractor.Extract(interpolated_data);
                //Extractor.Extract(interpolated_data);
                Extractor.ExtractOptional(interpolated_data);


                //Output the data to the ARFF file
                // tw.WriteLine(Extractor.toString() + "," + current_activity);
                //num_feature_windows++;
                // make sure the values of the features make sense... for example distance can 
                // only be -1024---- or so
                return true;
            }
            else  //the window is of poor quality, reinitialize and continue
            {
                isAcceptableConsecutiveLoss = true;
                isAcceptableLossRate = true;
                //errorFlag = 2;
                return false;
            }

            #endregion Calculate Feature Vector



        }
#if (!PocketPC)
        public static void toARFF(string aDataDirectory, string masterDirectory, int maxControllers, string sourceFile, int annotators, string[] filter)
        {
            int featureVectorIndex = 0;
            MITesDecoder aMITesDecoder = new MITesDecoder();
            MITesLoggerReader aMITesLoggerReader = new MITesLoggerReader(aMITesDecoder, aDataDirectory);
            SXML.SensorAnnotation sannotation = null;
            GeneralConfiguration configuration = null;

            AXML.Annotation[] aannotation = new AXML.Annotation[annotators];
            AXML.Reader[] readers = new AXML.Reader[annotators];
            AXML.Annotation intersection = null;
            AXML.Annotation[] difference = new AXML.Annotation[annotators];
            AXML.Annotation realtimeAnnotation = new AXML.Reader(masterDirectory, aDataDirectory).parse();
            realtimeAnnotation.RemoveData(filter);



            for (int i = 0; (i < annotators); i++)
            {
                readers[i] = new AXML.Reader(masterDirectory, aDataDirectory, sourceFile + i + ".xml");
                aannotation[i] = readers[i].parse();
                aannotation[i].RemoveData(filter);
                aannotation[i].DataDirectory = aDataDirectory;
                if (intersection == null)
                    intersection = aannotation[i];
                else
                    intersection = intersection.Intersect(aannotation[i]);
            }


            for (int i = 0; (i < annotators); i++)
                difference[i] = aannotation[i].Difference(intersection);




            SXML.Reader sreader = new SXML.Reader(masterDirectory, aDataDirectory);
            sannotation = sreader.parse(maxControllers);

            ConfigurationReader creader = new ConfigurationReader(aDataDirectory);
            configuration = creader.parse();

            Extractor.Initialize(aMITesDecoder, aDataDirectory, aannotation[0], sannotation, configuration);


            TextWriter tw = new StreamWriter(aDataDirectory + "\\output-" + sourceFile + ".arff");
            tw.WriteLine("@RELATION wockets");
            tw.WriteLine(Extractor.GetArffHeader());


            tw.WriteLine("@ATTRIBUTE INDEX NUMERIC");
            tw.WriteLine("@ATTRIBUTE ANNOTATORS_AGREE NUMERIC");

            Hashtable recorded_activities = new Hashtable();
            for (int k = 0; (k < annotators); k++)
            {
                //tw.Write("@ATTRIBUTE annotator"+k+" {unknown");
                //tw.Write("@ATTRIBUTE annotator" + k + " {");

                for (int i = 0; (i < aannotation[k].Data.Count); i++)
                {
                    AXML.AnnotatedRecord record = ((AXML.AnnotatedRecord)aannotation[k].Data[i]);
                    string activity = "";
                    for (int j = 0; (j < record.Labels.Count); j++)
                    {
                        if (j == record.Labels.Count - 1)
                            activity += ((AXML.Label)record.Labels[j]).Name;
                        else
                            activity += ((AXML.Label)record.Labels[j]).Name + "_";
                    }
                    activity = activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                    activity = Regex.Replace(activity, "[_]+", "_");
                    activity = Regex.Replace(activity, "^[_]+", "");
                    activity = Regex.Replace(activity, "[_]+$", "");
                    //only output activity labels that have not been seen
                    if (recorded_activities.Contains(activity) == false)
                    {
                        //tw.Write("," + activity);
                        recorded_activities[activity] = activity;
                    }
                }

            }


            for (int k = 0; (k < annotators); k++)
            {
                tw.Write("@ATTRIBUTE annotator" + k + " {unknown,flapping,rocking,flaprock}\n");
                //foreach ( DictionaryEntry de in recorded_activities )
                //   tw.Write("," + (string) de.Key); 
                //tw.WriteLine("}");
            }

            tw.Write("@ATTRIBUTE realtime {unknown,flapping,rocking,flaprock}\n");
            //foreach (DictionaryEntry de in recorded_activities)
            //   tw.Write("," + (string)de.Key);
            //tw.WriteLine("}");

            tw.WriteLine("@DATA");

            bool isData = aMITesLoggerReader.GetSensorData(10);
            int channel = 0, x = 0, y = 0, z = 0;
            double unixtimestamp = 0.0;

            int[] differenceIndex = new int[annotators];
            AXML.AnnotatedRecord[] annotatedRecord = new AXML.AnnotatedRecord[annotators];
            int intersectionIndex = 0;
            string intersection_activity = "unknown";
            AXML.AnnotatedRecord intersectionRecord = ((AXML.AnnotatedRecord)intersection.Data[intersectionIndex]);
            string[] current_activity = new string[annotators];
            string realtime_activity = "unknown";
            int realtimeIndex = 0;
            AXML.AnnotatedRecord realtimeRecord = ((AXML.AnnotatedRecord)realtimeAnnotation.Data[realtimeIndex]);
            for (int i = 0; (i < annotators); i++)
            {
                differenceIndex[i] = 0;
                annotatedRecord[i] = ((AXML.AnnotatedRecord)difference[i].Data[differenceIndex[i]]);
                current_activity[i] = "unknown";
            }


            do
            {
                //decode the frame
                channel = aMITesDecoder.GetSomeMITesData()[0].channel;
                x = aMITesDecoder.GetSomeMITesData()[0].x;
                y = aMITesDecoder.GetSomeMITesData()[0].y;
                z = aMITesDecoder.GetSomeMITesData()[0].z;
                unixtimestamp = aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp;
                double lastTimeStamp = Extractor.StoreMITesWindow();

                for (int i = 0; (i < annotators); i++)
                {
                    if (unixtimestamp > annotatedRecord[i].EndUnix)
                    {
                        current_activity[i] = "unknown";
                        if (differenceIndex[i] < difference[i].Data.Count - 1)
                        {
                            differenceIndex[i] = differenceIndex[i] + 1;
                            annotatedRecord[i] = ((AXML.AnnotatedRecord)difference[i].Data[differenceIndex[i]]);
                        }
                    }
                }


                if (unixtimestamp > realtimeRecord.EndUnix)
                {
                    realtime_activity = "unknown";
                    realtimeIndex++;
                    if (realtimeIndex < realtimeAnnotation.Data.Count)
                        realtimeRecord = ((AXML.AnnotatedRecord)realtimeAnnotation.Data[realtimeIndex]);
                }


                if (unixtimestamp > intersectionRecord.EndUnix)
                {

                    intersection_activity = "unknown";
                    if (intersectionIndex < intersection.Data.Count - 1)
                    {
                        intersectionIndex = intersectionIndex + 1;
                        intersectionRecord = ((AXML.AnnotatedRecord)intersection.Data[intersectionIndex]);
                    }
                }

                for (int i = 0; (i < annotators); i++)
                {
                    if ((lastTimeStamp >= annotatedRecord[i].StartUnix) &&
                         (lastTimeStamp <= annotatedRecord[i].EndUnix) && current_activity[i].Equals("unknown"))
                    {
                        current_activity[i] = "";
                        for (int j = 0; (j < annotatedRecord[i].Labels.Count); j++)
                        {
                            if (j == annotatedRecord[i].Labels.Count - 1)
                                current_activity[i] += ((AXML.Label)annotatedRecord[i].Labels[j]).Name;
                            else
                                current_activity[i] += ((AXML.Label)annotatedRecord[i].Labels[j]).Name + "_";
                        }
                        current_activity[i] = current_activity[i].Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                        current_activity[i] = Regex.Replace(current_activity[i], "[_]+", "_");
                        current_activity[i] = Regex.Replace(current_activity[i], "^[_]+", "");
                        current_activity[i] = Regex.Replace(current_activity[i], "[_]+$", "");
                    }
                    else if (lastTimeStamp > annotatedRecord[i].EndUnix)
                        current_activity[i] = "unknown";

                }

                if ((lastTimeStamp >= realtimeRecord.StartUnix) &&
                       (lastTimeStamp <= realtimeRecord.EndUnix) && realtime_activity.Equals("unknown"))
                {
                    realtime_activity = "";
                    for (int j = 0; (j < realtimeRecord.Labels.Count); j++)
                    {
                        if (j == realtimeRecord.Labels.Count - 1)
                            realtime_activity += ((AXML.Label)realtimeRecord.Labels[j]).Name;
                        else
                            realtime_activity += ((AXML.Label)realtimeRecord.Labels[j]).Name + "_";
                    }
                    realtime_activity = realtime_activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                    realtime_activity = Regex.Replace(realtime_activity, "[_]+", "_");
                    realtime_activity = Regex.Replace(realtime_activity, "^[_]+", "");
                    realtime_activity = Regex.Replace(realtime_activity, "[_]+$", "");
                }
                else if (lastTimeStamp > realtimeRecord.EndUnix)
                    realtime_activity = "unknown";



                if ((lastTimeStamp >= intersectionRecord.StartUnix) &&
                     (lastTimeStamp <= intersectionRecord.EndUnix) && intersection_activity.Equals("unknown"))
                {
                    intersection_activity = "";
                    for (int j = 0; (j < intersectionRecord.Labels.Count); j++)
                    {
                        if (j == intersectionRecord.Labels.Count - 1)
                            intersection_activity += ((AXML.Label)intersectionRecord.Labels[j]).Name;
                        else
                            intersection_activity += ((AXML.Label)intersectionRecord.Labels[j]).Name + "_";
                    }
                    intersection_activity = intersection_activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                    intersection_activity = Regex.Replace(intersection_activity, "[_]+", "_");
                    intersection_activity = Regex.Replace(intersection_activity, "^[_]+", "");
                    intersection_activity = Regex.Replace(intersection_activity, "[_]+$", "");
                }



                if ((Extractor.GenerateFeatureVector(lastTimeStamp)))
                {

                    string activity_suffix = "," + featureVectorIndex;


                    if (intersection_activity.Equals("unknown") == true) //disagreement or agreement unknown
                    {


                        if ((current_activity[0] == "unknown") && (current_activity[1] == "unknown"))
                            activity_suffix += ",1";
                        else
                            activity_suffix += ",0";
                        for (int i = 0; (i < annotators); i++)
                            activity_suffix += "," + current_activity[i];
                    }
                    else
                    {
                        activity_suffix += ",1";
                        for (int i = 0; (i < annotators); i++)
                            activity_suffix += "," + intersection_activity;
                    }

                    string arffSample = Extractor.toString() + activity_suffix;
                    //if (activity_suffix.Contains("unknown") == false)
                    //{
                    tw.WriteLine(arffSample + "," + realtime_activity);
                    featureVectorIndex++;
                    //}


                }


            } while (isData = aMITesLoggerReader.GetSensorData(10));

            tw.Close();
        }

        public static void toARFF(string aDataDirectory, string masterDirectory, int maxControllers, string[] filter)
        {
            MITesDecoder aMITesDecoder = new MITesDecoder();
            MITesLoggerReader aMITesLoggerReader = new MITesLoggerReader(aMITesDecoder, aDataDirectory);
            AXML.Annotation aannotation = null;
            SXML.SensorAnnotation sannotation = null;
            GeneralConfiguration configuration = new ConfigurationReader(aDataDirectory).parse();
            AXML.Reader reader = new AXML.Reader(masterDirectory, aDataDirectory);
            // if (reader.validate() == false)            
            //    throw new Exception("Error Code 0: XML format error - activities.xml does not match activities.xsd!");            
            //else
            // {
            aannotation = reader.parse();
            aannotation.RemoveData(filter);
            aannotation.DataDirectory = aDataDirectory;

            SXML.Reader sreader = new SXML.Reader(masterDirectory, aDataDirectory);
            //  if (sreader.validate() == false)               
            //      throw new Exception("Error Code 0: XML format error - sensors.xml does not match sensors.xsd!");               
            // else                
            sannotation = sreader.parse(maxControllers);

            //}

            //Extractor.Initialize(aMITesDecoder, aDataDirectory, aannotation, sannotation, configuration);
            Extractor.DCMean = true;
            Extractor.DCMeanTotal = true;
            Extractor.DCArea = true;
            Extractor.DCAreaSensor = true;
            Extractor.DCPostureDist = true;
            Extractor.ACAbsMean = true;
            Extractor.ACAbsArea = true;
            Extractor.ACAbsAreaSensor = true;
            Extractor.ACTotalAbsArea = true;
            Extractor.ACSVM = true;
            Extractor.ACTotalSVM = true;
            Extractor.SpectralContent = true;
            Extractor.ACEntropy = true;
            Extractor.ACEnergy = true;
            Extractor.ACSkew = true;
            Extractor.ACKur = true;
            Extractor.ACQuartiles = true;
            Extractor.ACVar = true;
            Extractor.ACAbsCV = true;
            Extractor.ACIQR = true;
            Extractor.ACRange = true;
            Extractor.ACBandEnergy = true;
            Extractor.ACBandEnergy = true;
            Extractor.ACLowEnergy = true;
            Extractor.ACModVigEnergy = true;
            Extractor.ACPitch = true;
            Extractor.ACMCR = true;
            Extractor.ACCorr = true;
            Extractor.ACSF = true;
            Extractor.ACTotalSF = true;



            
            Extractor.InitializeOptional(aMITesDecoder, aDataDirectory, aannotation, sannotation, configuration);


            TextWriter tw = new StreamWriter(aDataDirectory + "\\realtime-output.arff");
            tw.WriteLine("@RELATION wockets");
            //tw.WriteLine(Extractor.GetArffHeader());
            tw.WriteLine(Extractor.GetArffHeaderOptional());
            tw.Write("@ATTRIBUTE activity {unknown");
            Hashtable recorded_activities = new Hashtable();
            for (int i = 0; (i < aannotation.Data.Count); i++)
            {
                AXML.AnnotatedRecord record = ((AXML.AnnotatedRecord)aannotation.Data[i]);
                string activity = "";
                for (int j = 0; (j < record.Labels.Count); j++)
                {
                    if (j == record.Labels.Count - 1)
                        activity += ((AXML.Label)record.Labels[j]).Name;
                    else
                        activity += ((AXML.Label)record.Labels[j]).Name + "_";
                }
                activity = activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                activity = Regex.Replace(activity, "[_]+", "_");
                activity = Regex.Replace(activity, "^[_]+", "");
                activity = Regex.Replace(activity, "[_]+$", "");
                //only output activity labels that have not been seen
                if (recorded_activities.Contains(activity) == false)
                {
                    tw.Write("," + activity);
                    recorded_activities[activity] = activity;
                }
            }
            tw.WriteLine("}");
            tw.WriteLine("@DATA");

            bool isData = aMITesLoggerReader.GetSensorData(10);
            int channel = 0, x = 0, y = 0, z = 0;
            double unixtimestamp = 0.0;
            int activityIndex = 0;
            AXML.AnnotatedRecord annotatedRecord = ((AXML.AnnotatedRecord)aannotation.Data[activityIndex]);
            string current_activity = "unknown";
            TextWriter tww = new StreamWriter("test.csv");
            do
            {
                //decode the frame
                channel = aMITesDecoder.GetSomeMITesData()[0].channel;
                x = aMITesDecoder.GetSomeMITesData()[0].x;
                y = aMITesDecoder.GetSomeMITesData()[0].y;
                z = aMITesDecoder.GetSomeMITesData()[0].z;
                unixtimestamp = aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp;
                tww.WriteLine(unixtimestamp + "," + x + "," + y + "," + z);
                double lastTimeStamp = Extractor.StoreMITesWindow();
                //DateTime dt = new DateTime(1970, 1, 1, 0, 0, 0, 0);
                //dt=dt.AddMilliseconds(unixtimestamp);
                //DateTime dt2 = new DateTime(1970, 1, 1, 0, 0, 0, 0);
                //dt2 = dt2.AddMilliseconds(annotatedRecord.EndUnix);
                if (unixtimestamp > annotatedRecord.EndUnix)
                {
                    current_activity = "unknown";
                    if (activityIndex < aannotation.Data.Count - 1)
                    {
                        activityIndex++;
                        annotatedRecord = ((AXML.AnnotatedRecord)aannotation.Data[activityIndex]);
                    }
                }

                if ((lastTimeStamp >= annotatedRecord.StartUnix) &&
                     (lastTimeStamp <= annotatedRecord.EndUnix) && current_activity.Equals("unknown"))
                {
                    current_activity = "";
                    for (int j = 0; (j < annotatedRecord.Labels.Count); j++)
                    {
                        if (j == annotatedRecord.Labels.Count - 1)
                            current_activity += ((AXML.Label)annotatedRecord.Labels[j]).Name;
                        else
                            current_activity += ((AXML.Label)annotatedRecord.Labels[j]).Name + "_";
                    }
                    current_activity = current_activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                    current_activity = Regex.Replace(current_activity, "[_]+", "_");
                    current_activity = Regex.Replace(current_activity, "^[_]+", "");
                    current_activity = Regex.Replace(current_activity, "[_]+$", "");
                }

                //if (lastTimeStamp>=
                //if (current_activity.Equals("unknown") == false)
                //{
                if ((Extractor.GenerateFeatureVector(lastTimeStamp)))
                {
                    string arffSample = Extractor.toString() + "," + current_activity;
                    tw.WriteLine(arffSample);

                }
                //}

            } while (isData = aMITesLoggerReader.GetSensorData(10));

            tww.Close();
            tw.Close();
        }
#endif
        /*
        public static void toARFF(string aDataDirectory,string masterDirectory, string labelsFile,int maxControllers)
        {
            Hashtable arffClasses = new Hashtable();
            #region Initialization
            //true as long as there is data
            bool isData = true;

            //load annotation data
            AXML.Reader reader = new AXML.Reader(masterDirectory,aDataDirectory);
            Extractor.aannotation = reader.parse();


            //load sensor data
            SXML.Reader sreader = new SXML.Reader(masterDirectory,aDataDirectory);
            Extractor.sannotation = sreader.parse(maxControllers);



            //load decision learning parameters such as interpolation size, maximum frequencies included
            ConfigurationReader creader = new ConfigurationReader(aDataDirectory);
            GeneralConfiguration configuration = creader.parse();

            //Initialize the feature extractor based on the above parameters
            if (sannotation.IsHR)
                Extractor.Initialize((sannotation.Sensors.Count-1) * 3, configuration.FFTInterpolatedPower, configuration.FFTMaximumFrequencies);
            else
                Extractor.Initialize(sannotation.Sensors.Count * 3, configuration.FFTInterpolatedPower, configuration.FFTMaximumFrequencies);


            //Create the ARFF File header
            string arffHeader = "@RELATION wockets\n\n" + Extractor.GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
            arffHeader += "@ATTRIBUTE activity {";
            //foreach (AXML.Label label in ((AXML.Category)Extractor.aannotation.Categories[0]).Labels)
            //    arffHeader += label.Name.Replace(' ', '_') + ",";
            //arffHeader += "unknown}\n";
            //arffHeader += "\n@DATA\n\n";


            //Calculating windowing parameters
            
            //total number of points per interpolated window
            INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, configuration.FFTInterpolatedPower); //128;  
            //expected sampling rate per MITes
            EXPECTED_SAMPLING_RATE = 44;// configuration.ExpectedSamplingRate / sannotation.Sensors.Count; //samples per second
            //expected samples per window
            EXPECTED_WINDOW_SIZE = 44;//(int)(EXPECTED_SAMPLING_RATE * (configuration.WindowTime / 1000.0)); // expectedSamplingRate per window
            //what would be considered a good sampling rate
            EXPECTED_GOOD_SAMPLING_RATE = EXPECTED_WINDOW_SIZE - (int)(configuration.MaximumNonconsecutiveFrameLoss * EXPECTED_WINDOW_SIZE); //number of packets lost per second                      
            //space between samples
            EXPECTED_SAMPLES_SPACING = (double)configuration.WindowTime / EXPECTED_WINDOW_SIZE;
            //space between interpolated samples
            INTERPOLATED_SAMPLES_SPACING = (double)configuration.WindowTime / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;

            //window counters and delimiters
            next_window_end = 0;
            total_window_count = 0;
            num_feature_windows = 0;

            //data quality variables
            isAcceptableLossRate = true;
            isAcceptableConsecutiveLoss = true;
            unacceptable_window_count = 0;
            unacceptable_consecutive_window_loss_count = 0;

            //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
            data = new double[sannotation.Sensors.Count * 4][]; // 1 row for each axis

            // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
            interpolated_data = new double[sannotation.Sensors.Count * 3][];

            // array to store the y location for each axes as data is received
            // will be different for every sensor of course
            y_index = new int[sannotation.Sensors.Count];

            //Initialize expected data array
            for (int j = 0; (j < (sannotation.Sensors.Count * 4)); j++)
            {
                data[j] = new double[EXPECTED_WINDOW_SIZE];
                for (int k = 0; (k < EXPECTED_WINDOW_SIZE); k++)
                    data[j][k] = 0;
            }

            //Initialize interpolated data array
            for (int j = 0; (j < (sannotation.Sensors.Count * 3)); j++)
            {
                interpolated_data[j] = new double[INTERPOLATED_SAMPLING_RATE_PER_WINDOW];
                for (int k = 0; (k < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); k++)
                    interpolated_data[j][k] = 0;
            }

            //Initialize y index for each sensor
            for (int j = 0; (j < sannotation.Sensors.Count); j++)
                y_index[j] = 0;




            //Initialize the first window start and the last window end time
            int i;  //offline data
            i = 0;
            WINDOWING_START_TIME = ((AXML.AnnotatedRecord)Extractor.aannotation.Data[0]).StartUnix;
            WINDOWING_END_TIME = ((AXML.AnnotatedRecord)Extractor.aannotation.Data[Extractor.aannotation.Data.Count - 1]).EndUnix;


            //Initialize the MITes decoder for the passed directory
            MITesDecoder aMITesDecoder = new MITesDecoder();
            MITesLoggerReaderMR aMITesLoggerReaderMR = new MITesLoggerReaderMR(aMITesDecoder, aDataDirectory);

            //Read the first annotation
            AXML.AnnotatedRecord annotatedRecord = (AXML.AnnotatedRecord)Extractor.aannotation.Data[i];
            int samples = 0;
            int otherSamples = 0;



            for (int j = 0; j < MITesData.MAX_MITES_CHANNELS; j++)
                MITesDataFilterer.MITesPerformanceTracker[j] = new MITesPerformanceStats(0);
            //based on how many receivers and to what channels they are listening adjust the good sampling rate
            foreach (SXML.Sensor sensor in sannotation.Sensors)
            {
                int sensor_id = Convert.ToInt32(sensor.ID);
                int receiver_id = Convert.ToInt32(sensor.Receiver);
                if (sensor_id == 0) //HR sensor
                {
                    MITesDataFilterer.MITesPerformanceTracker[sensor_id].GoodRate = (int)(60 * 0.8);
                    MITesDataFilterer.MITesPerformanceTracker[sensor_id].PerfectRate = 60;
                }
                else
                {
                    int goodSamplingRate = (int)((configuration.ExpectedSamplingRate * (1 - configuration.MaximumNonconsecutiveFrameLoss)) / sannotation.NumberSensors[receiver_id]);
                    MITesDataFilterer.MITesPerformanceTracker[sensor_id].GoodRate = goodSamplingRate;
                    MITesDataFilterer.MITesPerformanceTracker[sensor_id].PerfectRate = (int)((configuration.ExpectedSamplingRate) / sannotation.NumberSensors[receiver_id]);
                }
            }

            #endregion Initialization

            //Create the ARFF File
            TextWriter tw = new StreamWriter("output.arff");
            tw.WriteLine(arffHeader);

            // Loop through the MITes data in the directory
            // do not go beyond the last annotated record

            //Get the the first <=10 frames
            isData = aMITesLoggerReaderMR.GetSensorData(10);
            while ((isData) && (i < Extractor.aannotation.Data.Count))
            {

                
                #region Read MITes data until current time point passes
                // To calculate the features for at a specific Time point t
                // make sure that all frames from different sensors with time
                // t or less have been received
                // keep grabbing frames until t has passed
                // assumption: frames are timestamped in order                
                int channel = 0, x = 0, y = 0, z = 0;
                double unixtimestamp = 0.0;
                int x_index = 0;
                do
                {
                    //decode the frame
                    channel = aMITesDecoder.GetSomeMITesData()[0].channel;
                    x = aMITesDecoder.GetSomeMITesData()[0].x;
                    y = aMITesDecoder.GetSomeMITesData()[0].y;
                    z = aMITesDecoder.GetSomeMITesData()[0].z;
                    unixtimestamp = aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp;
                    x_index = -1;

                    

                    //CHANGE To pick the right index for any size
                    //determine the index of the sensor in the sensorData file
                    for(int ii=0;(ii<sannotation.Sensors.Count);ii++)
                    {
                        if (channel == Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[ii]).ID))
                        {
                            x_index = ii;
                            break;
                        }
                    }
                    if (x_index == -1)//ignore mites data that do not belong to the setup
                        continue;

                   // if (channel == Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[0]).ID))
                   //     x_index = 0;
                   // else if (channel == Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[1]).ID))
                   //    x_index = 1;
                   // else if (channel == Convert.ToInt32(((SXML.Sensor)sannotation.Sensors[2]).ID))
                   //     x_index = 2;
                   // else //ignore mites data that do not belong to the setup
                   //     continue;


                    //calculate the x index in the data array for this particular sensor
                    int adjusted_x_index=0;
                    if (sannotation.IsHR)
                        adjusted_x_index = x_index * (sannotation.Sensors.Count );
                    else
                        adjusted_x_index = x_index * (sannotation.Sensors.Count+1);
            

                    // store the values in the current frame in the correct column based of the EXPECTED_WINDOW data array
                    // on the y_index for the sensor
                  //  data[adjusted_x_index][y_index[x_index]] = x;
                  //  data[adjusted_x_index + 1][y_index[x_index]] = y;
                  //  data[adjusted_x_index + 2][y_index[x_index]] = z;
                  //  data[adjusted_x_index + 3][y_index[x_index]] = unixtimestamp;
                    
                    //increment the y_index for the sensor and wrap around if needed
                   // y_index[x_index] = (y_index[x_index] + 1) % EXPECTED_WINDOW_SIZE;

                    //continue while there is data and while the time stamp for previous sample and the current are the same
                    //typically when starting to read data or to make sure that all data from different sensors for
                    // a specific time stamp have been collected
                } while ((isData = aMITesLoggerReaderMR.GetSensorData(10)) && (unixtimestamp == aMITesDecoder.GetSomeMITesData()[0].unixTimeStamp));

                #endregion Read MITes data until current time point passes

                //Check if there is no more data, if so break from the data collection loop
                if (!isData)
                    break;


                // Here ALL data from all sensors <=time t have been collected, you can now attempt to
                // calculate the features for the window at time t


                #region Check if window captured and calculate features


                //If an annotation just ended, go to the next annotation
                if (unixtimestamp >= annotatedRecord.EndUnix)
                //Check if the passed time point has concluded an activity
                {
                    Console.WriteLine(((AXML.Label)annotatedRecord.Labels[0]).Name + " " + annotatedRecord.StartUnix +
                        " " + annotatedRecord.EndUnix + " " + samples);
                    i++;
                    samples = 0;
                    
                    if (i < Extractor.aannotation.Data.Count)
                        annotatedRecord = (AXML.AnnotatedRecord)Extractor.aannotation.Data[i];
                }
                // We calculate the features at the end of each window
                // If the passed time point is:
                // 1- within the starting of the first activity and the end of the last activity
                // 2- is equal or exceeds the end of the next expected window
                // then calculate the features

                else if ((unixtimestamp >= WINDOWING_START_TIME) && (unixtimestamp < WINDOWING_END_TIME)
                    && (unixtimestamp >= next_window_end))
                //Check if a time point is within an activity
                {

                    //compute the boundaries for the current window
                    double window_start_time = unixtimestamp - configuration.WindowTime;
                    double window_end_time = unixtimestamp;
                    double current_time = window_end_time;
                    //compute the end of the next overlapping window
                    next_window_end = window_end_time + (configuration.WindowTime * configuration.WindowOverlap);

                    //increment window counter
                    total_window_count++;


                    //for all sensors grab their data windows and smoothen them
                    #region sensors window grabbing and interpolation

                    // Go through each sensor and extract the collected data within 
                    // the current time window
                    for (int j = 0; (j < sannotation.Sensors.Count); j++)
                    {

                        // Check that the previous sensor in the loop did not report
                        // deteriorated quality for its data
                        #region sensors window quality
                        if (isAcceptableLossRate == false)
                            break;
                        // check if earlier axes reported excessive consecutive loss of data frames
                        if (isAcceptableConsecutiveLoss == false)
                            break;
                        #endregion sensors window quality


                        // determine the base index for the current sensor, each sensor has 4 rows (x,y,z,timestamp)
                        int sensor_index = j * (sannotation.Sensors.Count + 1);
                        int time_index = sensor_index + 3;

                        // determine the last read data sample for the current sensor
                        // by looking at its index
                        int last_sample = 0;
                        if (y_index[j] == 0)
                            last_sample = EXPECTED_WINDOW_SIZE - 1;
                        else
                            last_sample = y_index[j] - 1;
                        int total_data_points = 0, distinct_data_points = 0;

                        //Grab the readings for each axis of a sensor and smoothen it
                        #region sensor window grabbing and interpolation
                        // Go through each axis of the current sensor and smooth
                        // it using the cubic spline
                        for (int axes_num = 0; (axes_num < 3); axes_num++)
                        {

                            //calculate the exact index based on the 
                            // base sensor index and the axis number
                            int axes_index = sensor_index + axes_num;  //for data array
                            int interpolated_axes_index = j * (sannotation.Sensors.Count) + axes_num; //for interpolated data array

                            // create 2 arrays to store x and y values for the cubic spline
                            // it is sufficient to have an array of expected sampling rate window size
                            // for 3 mites that would be 180/60
                            double[] xvals = new double[EXPECTED_WINDOW_SIZE];
                            double[] yvals = new double[EXPECTED_WINDOW_SIZE];

                            //point to the last sample that was read and get its time
                            int sample_index = last_sample;
                            current_time = data[time_index][sample_index];
                            //copy samples in the last time window
                            total_data_points = 0;
                            distinct_data_points = 0;
                            double previous_time = 0;


                            //Grab the values for a specific sensor axes between
                            //window start and window end
                            #region window grabbing
                            // Start going back from the current time (window end) till the start of the window
                            // without exceeding the expected sampling rate and fill in the data in the signal
                            // value for the axis in yvals and the relative time value from the window start
                            while ((current_time >= window_start_time) && (current_time <= window_end_time)
                                && (total_data_points < EXPECTED_WINDOW_SIZE) && (distinct_data_points < EXPECTED_WINDOW_SIZE))
                            {

                                //some time stamps from the mites are identical
                                // for interpolation that will cause an error
                                // simply take the first value for a time point and ignore the
                                // rest, another strategy would be to average over these values
                                if (current_time == previous_time)
                                {
                                    //Get the time of the previous sample and skip the sample
                                    if (sample_index == 0)
                                        sample_index = EXPECTED_WINDOW_SIZE - 1;
                                    else
                                        sample_index--;
                                    current_time = data[time_index][sample_index];
                                    total_data_points++;
                                    continue;
                                }

                                // Quality Control
                                // check the time between consecutive data frames and make sure it does
                                // not exceed maximum_consecutive_loss, do not do that for the first
                                // entry of the window
                                if (distinct_data_points > 0)
                                {
                                    int consecutive_lost_packets = (int)((previous_time - current_time) / EXPECTED_SAMPLES_SPACING);
                                    if (consecutive_lost_packets > configuration.MaximumConsecutiveFrameLoss)
                                    {
                                        unacceptable_consecutive_window_loss_count++;
                                        isAcceptableConsecutiveLoss = false;
                                        break;
                                    }
                                }



                                //relative time value from window start
                                xvals[distinct_data_points] = (int)(current_time - window_start_time);
                                //signal value for the current sample and current axis.
                                yvals[distinct_data_points] = data[axes_index][sample_index];


                                //Point to the previous sample in the current window
                                if (sample_index == 0)
                                    sample_index = EXPECTED_WINDOW_SIZE - 1;
                                else
                                    sample_index--;

                                //store the previous sample time
                                previous_time = current_time;

                                //Get the time of the new sample
                                current_time = data[time_index][sample_index];
             
                                //Point to the next entry in the interpolation array
                                distinct_data_points++;

                                total_data_points++;
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
                            if (distinct_data_points < EXPECTED_GOOD_SAMPLING_RATE) //discard this whole window of data
                            {
                                isAcceptableLossRate = false;
                                unacceptable_window_count++;
                                break;
                            }

                            #endregion window quality checks

                            //smoothen the axis values and store them in interpolated data array
                            #region window interpolation
                            
                            //create 2 arrays with the exact size of the data points for interpolation
                            //create 2 arrays with the exact size of the data points for interpolation
                            double[] admissible_xvals = new double[distinct_data_points];
                            double[] admissible_yvals = new double[distinct_data_points];
                            double expectedSpacing = Extractor.dconfiguration.WindowTime / (double)distinct_data_points;
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
                                interpolated_data[interpolated_axes_index][k] = cs.interpolate(k * INTERPOLATED_SAMPLES_SPACING);
                                                        

                            #endregion window interpolation

                        }
                        #endregion sensor window grabbing and interpolation



                    }
                    #endregion  sensors window grabbing and interpolation


                    //If the data is of acceptable quality, calculate the features
                    #region Calculate Feature Vector

                    if ((isAcceptableLossRate == true) && (isAcceptableConsecutiveLoss == true))
                    {

                        //If the current activity is annotated pick it otherwise pick unknown
                        string current_activity = "unknown";
                        if ((unixtimestamp >= annotatedRecord.StartUnix) && (unixtimestamp < annotatedRecord.EndUnix))
                        {
                            current_activity = "";
                            for (int j=0;(j<aannotation.Categories.Count);j++)
                                current_activity += ((AXML.Label)(annotatedRecord.Labels[j])).Name+"_";
                        }
                        
                        //Extract the features from the interpolated data
                        Extractor.Extract(interpolated_data);

                        //current_activity = current_activity.Replace(' ', '_');
                        //int aIndex = (int)activityIndex[current_activity];
                        //featuresData[aIndex].Add(Extractor.toString());
                        //labelData[aIndex].Add(current_activity.Replace(' ', '_'));
                        //sampleCounters[aIndex] += 1;
                        
                        //Output the data to the ARFF file
                        tw.WriteLine(Extractor.toString() + "," + current_activity);

                        if (((string)arffClasses[current_activity]).Equals(current_activity))
                        {
                            arffHeader += current_activity.Replace(' ', '_') + ",";
                            arffClasses[current_activity] = current_activity;
                        }
                        //foreach (AXML.Label label in ((AXML.Category)Extractor.aannotation.Categories[0]).Labels)
                        //    arffHeader += label.Name.Replace(' ', '_') + ",";
                        //arffHeader += "unknown}\n";
                        //arffHeader += "\n@DATA\n\n";
                        num_feature_windows++;
                    }
                    else  //the window is of poor quality, reinitialize and continue
                    {
                        isAcceptableConsecutiveLoss = true;
                        isAcceptableLossRate = true;
                    }

                    #endregion Calculate Feature Vector


                }
                else
                    otherSamples++;

                #endregion Check if window captured and calculate features


                //here we have the x,y,z data stored in the first elements
                //of aMitesDecoder.someData with a time stamp

            }


            // Close the ARFF file and release resources
            arffHeader += "unknown}\n";
            arffHeader += "\n@DATA\n\n";
            tw.WriteLine(arffHeader);
            tw.Close();
            Extractor.Cleanup();

          
            Console.WriteLine("Total Windows Count:" + total_window_count);
            Console.WriteLine("Inadmissible Windows Count (loss rate):" + unacceptable_window_count);
            Console.WriteLine("Inadmissible Windows Count (consecutive loss):" + unacceptable_consecutive_window_loss_count);
            Console.WriteLine("Admissible Feature Windows:" + num_feature_windows);
        }

       */
        public static void Cleanup()
        {
            FFT.Cleanup();
            //for (int i = 0; (i < Extractor.sannotation.Sensors.Count); i++)            
            //   spacingtws[i].Close();            
        }

/* Butterworth LowPass Filter at 1 Hz
 * 
 * 
#define NZEROS 2
#define NPOLES 2
#define GAIN   1.717988320e+03

static float xv[NZEROS+1], yv[NPOLES+1];

static void filterloop()
  { for (;;)
      { xv[0] = xv[1]; xv[1] = xv[2]; 
        xv[2] = next input value / GAIN;
        yv[0] = yv[1]; yv[1] = yv[2]; 
        yv[2] =   (xv[0] + xv[2]) + 2 * xv[1]
                     + ( -0.9329347318 * yv[0]) + (  1.9306064272 * yv[1]);
        next output value = yv[2];
      }
  }
*/

        static double[][] LP1Hz_xv, LP1Hz_yv;
        static int LP1Hz_NZER0S=2;
        static int LP1Hz_NPOLES=2;
        static double LP1Hz_GAIN=1.717988320e+03;

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

        public static bool ACSkew= false;
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
        static double TotalMass = 100.0;
        static double TrunkMass = 0.497; //(Hip)
        static double ArmMass = 0.0500; //(Arm)
        static double LegMass = 0.1610; //(Leg)

        static double[] limbs = new double[5]{TrunkMass,ArmMass,ArmMass,LegMass,LegMass};


        public static bool ACTotalSF = false;
        static int ACTotalSFIndex = 0;



        public static void InitializeOptional(MITesDecoder aMITesDecoder, string aDataDirectory,
AXML.Annotation aannotation, SXML.SensorAnnotation sannotation, GeneralConfiguration configuration)//, string masterDirectory)
        {
            int numFeatures = 0;
            int currentIndex = 0;



            Extractor.aannotation = aannotation;
            Extractor.sannotation = sannotation;
            Extractor.dconfiguration = configuration;

            // count the sensors for feature extraction and identify their indicies in
            // sensor annotation - at the moment only accelerometers are used
            Extractor.sensorIndicies = new Hashtable();
            Extractor.extractorSensorCount = 0;
            foreach (SXML.Sensor sensor in sannotation.Sensors)
            {
                int channel = Convert.ToInt32(sensor.ID);
                if (channel > 0) // if accelerometer
                {
                    Extractor.sensorIndicies[channel] = extractorSensorCount;
                    Extractor.extractorSensorCount++;
                }
            }


            Extractor.inputRowSize = Extractor.extractorSensorCount * 3;
            Extractor.fftInterpolationPower = dconfiguration.FFTInterpolatedPower;
            Extractor.fftMaximumFrequencies = dconfiguration.FFTMaximumFrequencies;
            Extractor.inputColumnSize = (int)Math.Pow(2, Extractor.fftInterpolationPower);

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
                numFeatures += ((Extractor.inputRowSize * Extractor.inputRowSize) - Extractor.inputRowSize) / 2;
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


            Extractor.num_features = numFeatures;
            fv = new double[numFeatures];


        
            //CHANGE: gathers training samples based on the first category only 
            Extractor.trainingTime = new Hashtable();//int[((AXML.Category)Extractor.aannotation.Categories[0]).Labels.Count];
            foreach (AXML.Label label in ((AXML.Category)Extractor.aannotation.Categories[0]).Labels)
                Extractor.trainingTime.Add(label.Name, 0);            
            Extractor.trainingCompleted = false;


                       
            
            //Extractor.features = new double[Extractor.num_features];
            Extractor.arffAttriburesLabels = new string[Extractor.num_features];
            Extractor.attributeLocation = new Hashtable();

            Extractor.standardized = new double[inputRowSize][];
            for (int i = 0; (i < inputRowSize); i++)
                Extractor.standardized[i] = new double[Extractor.inputColumnSize];

            Extractor.means = new double[inputRowSize];
            Extractor.meansbp = new double[inputRowSize];
            Extractor.meanslp = new double[inputRowSize];

            inputFFT = new int[Extractor.inputColumnSize];
            FFT.Initialize(fftInterpolationPower, NumberFrequencies);
            Extractor.aMITesDecoder = aMITesDecoder;

            //Create the ARFF File header
            string arffHeader = "@RELATION wockets\n\n" + Extractor.GetArffHeader();//sannotation.Sensors.Count * 3, configuration.FFTMaximumFrequencies);
            arffHeader += "@ATTRIBUTE activity {";
            foreach (AXML.Label label in ((AXML.Category)Extractor.aannotation.Categories[0]).Labels)
                arffHeader += label.Name.Replace(' ', '_') + ",";
            arffHeader += "unknown}\n";
            arffHeader += "\n@DATA\n\n";

            //Calculating windowing parameters

            //total number of points per interpolated window
            Extractor.INTERPOLATED_SAMPLING_RATE_PER_WINDOW = (int)Math.Pow(2, dconfiguration.FFTInterpolatedPower); //128;  

            //space between interpolated samples
            Extractor.INTERPOLATED_SAMPLES_SPACING = (double)dconfiguration.WindowTime / INTERPOLATED_SAMPLING_RATE_PER_WINDOW;


            //expected sampling rate per MITes
            //Extractor.EXPECTED_SAMPLING_RATE = dconfiguration.ExpectedSamplingRate / sannotation.Sensors.Count; //samples per second
            //expected samples per window
            //Extractor.EXPECTED_WINDOW_SIZE = (int)(EXPECTED_SAMPLING_RATE * (dconfiguration.WindowTime / 1000.0)); // expectedSamplingRate per window
            //what would be considered a good sampling rate
            //Extractor.EXPECTED_GOOD_SAMPLING_RATE = EXPECTED_WINDOW_SIZE - (int)(dconfiguration.MaximumNonconsecutiveFrameLoss * EXPECTED_WINDOW_SIZE); //number of packets lost per second                      
            //space between samples
            //Extractor.EXPECTED_SAMPLES_SPACING = (double)dconfiguration.WindowTime / EXPECTED_WINDOW_SIZE;
            Extractor.EXPECTED_SAMPLING_RATES = new int[Extractor.extractorSensorCount];
            Extractor.EXPECTED_WINDOW_SIZES = new int[Extractor.extractorSensorCount];
            Extractor.EXPECTED_GOOD_SAMPLING_RATES = new int[Extractor.extractorSensorCount];
            Extractor.EXPECTED_SAMPLES_SPACING = new double[Extractor.extractorSensorCount];

            //foreach (SXML.Sensor sensor in sannotation.Sensors)
            foreach (DictionaryEntry sensorEntry in Extractor.sensorIndicies)
            {
                //Get the channel and index in data array for only
                // extractor sensors (sensors that will be used to compute
                // features i.e. accelerometers)
                int channel = (int)sensorEntry.Key;
                int sensorIndex = (int)sensorEntry.Value;
                SXML.Sensor sensor = ((SXML.Sensor)sannotation.Sensors[(int)sannotation.SensorsIndex[channel]]);
                int receiverID = Convert.ToInt32(sensor.Receiver);

                if (channel == MITesDecoder.MAX_CHANNEL)  //Built in sensor
                    Extractor.EXPECTED_SAMPLING_RATES[sensorIndex] = sensor.SamplingRate; //used sensor sampling rate
                else
                    Extractor.EXPECTED_SAMPLING_RATES[sensorIndex] = dconfiguration.ExpectedSamplingRate / sannotation.NumberSensors[receiverID];

                Extractor.EXPECTED_WINDOW_SIZES[sensorIndex] = (int)(Extractor.EXPECTED_SAMPLING_RATES[sensorIndex] * (dconfiguration.WindowTime / 1000.0));
                Extractor.EXPECTED_GOOD_SAMPLING_RATES[sensorIndex] = Extractor.EXPECTED_WINDOW_SIZES[sensorIndex] - (int)(dconfiguration.MaximumNonconsecutiveFrameLoss * Extractor.EXPECTED_WINDOW_SIZES[sensorIndex]);
                Extractor.EXPECTED_SAMPLES_SPACING[sensorIndex] = (double)dconfiguration.WindowTime / Extractor.EXPECTED_WINDOW_SIZES[sensorIndex];
            }



            //window counters and delimiters
            Extractor.next_window_end = 0;
            Extractor.total_window_count = 0;
            Extractor.num_feature_windows = 0;

            //data quality variables
            Extractor.isAcceptableLossRate = true;
            Extractor.isAcceptableConsecutiveLoss = true;
            Extractor.unacceptable_window_count = 0;
            Extractor.unacceptable_consecutive_window_loss_count = 0;


            //2 D array that stores Sensor axes + time stamps on each row  X expected WINDOW SIZE
            Extractor.data = new double[Extractor.extractorSensorCount * 4][]; // 1 row for each axis

            // 2D array that stores Sensor axes X INTERPOLATED WINDOW SIZE
            Extractor.interpolated_data = new double[Extractor.extractorSensorCount * 3][];

            // array to store the y location for each axes as data is received
            // will be different for every sensor of course
            Extractor.y_index = new int[Extractor.extractorSensorCount];


            //Initialize expected data array

            foreach (DictionaryEntry sensorEntry in Extractor.sensorIndicies)
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
                    Extractor.data[adjusted_sensor_index] = new double[EXPECTED_WINDOW_SIZES[sensorIndex]];
                    for (int k = 0; (k < EXPECTED_WINDOW_SIZES[sensorIndex]); k++)
                        Extractor.data[adjusted_sensor_index][k] = 0;
                    adjusted_sensor_index++;
                }

            }


            //Here it is equal across all sensors, so we do not need to consider
            //the sampling rate of each sensor separately
            for (int j = 0; (j < (Extractor.extractorSensorCount * 3)); j++)
            {
                Extractor.interpolated_data[j] = new double[INTERPOLATED_SAMPLING_RATE_PER_WINDOW];
                for (int k = 0; (k < INTERPOLATED_SAMPLING_RATE_PER_WINDOW); k++)
                    Extractor.interpolated_data[j][k] = 0;
            }

            //Initialize y index for each sensor
            for (int j = 0; (j < Extractor.extractorSensorCount); j++)
                Extractor.y_index[j] = 0;

        }


        //LowPass 1Hz Butterworth
        public static double LowPass1Hz(int axis,double input)
        {
            LP1Hz_xv[axis][0] = LP1Hz_xv[axis][1];
            LP1Hz_xv[axis][1] = LP1Hz_xv[axis][2];
            LP1Hz_xv[axis][2] = input / LP1Hz_GAIN;

            LP1Hz_yv[axis][0] = LP1Hz_yv[axis][1];
            LP1Hz_yv[axis][1] = LP1Hz_yv[axis][2];
            LP1Hz_yv[axis][2] = (LP1Hz_xv[axis][0] + LP1Hz_xv[axis][2]) + 2 * LP1Hz_xv[axis][1] + (-0.9329347318 * LP1Hz_yv[axis][0]) + (1.9306064272 * LP1Hz_yv[axis][1]);
            return LP1Hz_yv[axis][2];
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

            BPpt1_20Hz_yv[axis][4] = ( BPpt1_20Hz_xv[axis][0] +  BPpt1_20Hz_xv[axis][4])- 2*  BPpt1_20Hz_xv[axis][2]
                                        + (-0.2610321874 * BPpt1_20Hz_yv[axis][0]) + (1.2245774774 * BPpt1_20Hz_yv[axis][1])
                                        + (-2.6621991985 * BPpt1_20Hz_yv[axis][2]) + (2.6986404043 * BPpt1_20Hz_yv[axis][3]);
            return BPpt1_20Hz_yv[axis][4];
        }

        /*
         *
         * http://access.feld.cvut.cz/view.php?cisloclanku=2009060001
         * Pitch is the value of i that results in the maximum R[i]
         * public void autoCorrelation(int size){
    float[] R = new R[size];
    float sum;

    for (int i=0;i<size;i++) {
        sum=0;
        for (int j=0;j<size-i;j++) {
            sum+=x[j]*x[j+i];
        }
        R[i]=sum;
    }
}
*/
        static int  ocount = 0;
   
        public static void ExtractOptional(double[][] input)//,int fftInterpolationPower, int fftMaximumFrequencies)
        {


            int j = 0, i = 0;
            double  min = 0, max = 0, total = 0, variance = 0;
            double sumbp = 0,sumlp=0,sum=0;
            double sumACAbsArea = 0;
            double[][] lpvalue = new double[input.Length][];
            double[][] bpvalue = new double[input.Length][];
            double[] bpValues = new double[Extractor.inputColumnSize];

            //filter the data
            for (i = 0; (i < inputRowSize); i++)
            {
                lpvalue[i] = new double[input[0].Length];
                bpvalue[i] = new double[input[0].Length];
                for (j = 0; (j < Extractor.inputColumnSize); j++)
                {
                    lpvalue[i][j] = LowPass1Hz(i, input[i][j]);
                    bpvalue[i][j] = BandPasspt1_20Hz_(i, input[i][j]);
                }
                
            }

            //Measures of Body Posture including DCMean, DCTotalMean, DCArea, DCPostureDist
            //Mean average over the signal window after low-pass filtering the acceleration at 1Hz
            if ((DCMean) || (DCMeanTotal) || (DCArea) || (DCPostureDist))
            {
                int meanIndex = DCMeanIndex;     
                double meanlp = 0,meanbp=0,mean=0;
                double acAbsMean = 0;
                
                double meanTotal=0;
                double acAbsSum = 0;          
                double acTotalAbsArea = 0;
                double[] acSVMSensor = new double[Extractor.inputColumnSize];
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


                //int acAbsMeanIndex = 0;
                //int aucIndex = DCAreaIndex;
                //int sensorAucIndex = DCAreaSensorIndex;
               // int postureIndex = DCPostureDistIndex;
                if (ocount == 50)
                    Console.Write("tt");


                //Calculate DCMean               
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
                    double[] acf = new double[Extractor.inputColumnSize];

                    for (j = 0; (j < Extractor.inputColumnSize); j++)
                    {
                        // double lpvalue=LowPass1Hz(i, input[i][j]);
                        sumlp += lpvalue[i][j];
                        sumbp += bpvalue[i][j];
                        sum += input[i][j];
                        bpValues[j] = bpvalue[i][j];

                       // standardized[i][j] = bpvalue[i][j] - meansbp[i]; //mean subtracted


                        //double bpvalue=BandPasspt1_20Hz_(i, input[i][j]);
                        acAbsSum += Math.Abs(bpvalue[i][j]);
                        acSVMSensor[j] += Math.Pow(bpvalue[i][j], 2.0);
                        inputFFT[j] = (int)(bpvalue[i][j]);
                       
                        if (ACRange)
                        {
                            if (bpvalue[i][j] < min)
                                min = bpvalue[i][j];
                            if (bpvalue[i][j] > max)
                                max = bpvalue[i][j];
                        }


                        if (ACPitch)
                        {
                            acfSum = 0;
                            for (int k = 0; (k < (Extractor.inputColumnSize - j)); k++)
                                acfSum += bpvalue[i][k] * bpvalue[i][k + j];
                            acf[j] = acfSum;
                        }
                    }
                    
                    meanlp=sumlp / Extractor.inputColumnSize;
                    meanbp = sumbp/ Extractor.inputColumnSize;
                    mean= sum/Extractor.inputColumnSize;

                    acAbsMean = acAbsSum / Extractor.inputColumnSize;
                    
                    if (DCMean)
                        fv[meanIndex++] = mean;
                    
                    means[i] = mean;
                    meansbp[i] = meanbp;
                    meanslp[i] = meanlp;

                    for (j = 0; (j < Extractor.inputColumnSize); j++)
                    {
                        if (ACSkew || ACKur || ACVar)
                        {
                            squaredSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 2.0);
                            cubicSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 3.0);
                            fourthSum += Math.Pow((bpvalue[i][j] - meansbp[i]), 4.0);
                        }

                        standardized[i][j] = bpvalue[i][j] - meansbp[i];
                    }


                    if (DCMeanTotal)
                        meanTotal += mean;

                    if (DCArea)
                        fv[dcAreaIndex++] = sum;

                    if (ACAbsMean)
                        fv[acAbsMeanIndex++] = acAbsMean;

                    if (ACAbsArea)
                    {
                        fv[acAbsAreaIndex++] = acAbsSum;
                        acTotalAbsArea += acAbsSum;
                    }


                    if (((i + 1) % 3 == 0))
                    {
                        if (DCPostureDist)
                        {
                            fv[dcPostureDistIndex++] = meanslp[i - 2] - meanslp[i - 1];
                            fv[dcPostureDistIndex++] = meanslp[i - 2] - meanslp[i];
                            fv[dcPostureDistIndex++] = meanslp[i - 1] - meanslp[i];
                        }

                        if (DCAreaSensor)
                            fv[dcAreaSensorIndex++] = fv[dcAreaIndex - 1] + fv[dcAreaIndex - 2] + fv[dcAreaIndex - 3];

                        if (ACAbsAreaSensor)
                            fv[acAbsAreaSensorIndex++] = fv[acAbsAreaIndex - 1] + fv[acAbsAreaIndex - 2] + fv[acAbsAreaIndex - 3];

                        if (ACSVM)
                        {
                            double totalSVM = 0;
                            for (int k = 0; (k < Extractor.inputColumnSize); k++)
                            {
                                totalSVM += Math.Sqrt(acSVMSensor[k]);
                                acSVMSensor[k] = 0;
                            }
                            fv[acSVMIndex++] = totalSVM/Extractor.inputColumnSize;
                            //acTotalSVM += fv[ACSVMIndex - 1];
                        }


                        if (ACSF)
                        {
                            int location = i % 3;
                            fv[acSFIndex + location] = limbs[location] * fv[acAbsAreaSensorIndex - 1];
                            acTotalSF += fv[acSFIndex + location];

                        }

                    }

   

                    if (SpectralContent)
                    {
                        //calculate FFT                
                        FFT.Calculate(inputFFT);
                       
                        //features[energyIndex++] = FFT.Energy;
                        double[] maxFreqsMags = FFT.MaximumFrequencies;
                        for (int k = 0; (k < NumberFrequencies); k++)
                        {
                            fv[acFFTFreqsIndex++] = maxFreqsMags[k++];
                            fv[acFFTMagsIndex++] = maxFreqsMags[k++];                            
                        }

                        
                        if (ACEntropy)                        
                            fv[acEntropyIndex++]=FFT.Entropy;
                        if (ACEnergy)
                            fv[acEnergyIndex++] = FFT.Energy;
                        if (ACBandEnergy)
                            fv[acBandEnergyIndex++] = FFT.ActivityBandEnergy;

                        if (ACLowEnergy)
                            fv[acLowEnergyIndex++] = FFT.LowIntensityEnergy;

                        if (ACModVigEnergy)
                            fv[acModVigEnergyIndex++] = FFT.ModVigIntensityEnergy;
                    }

           
                    if (ACSkew)
                        fv[acSkewIndex++] = (cubicSum * Math.Sqrt(Extractor.inputColumnSize)) / Math.Pow(squaredSum, 1.5);
                    if (ACKur)
                        fv[acKurIndex++] = ((fourthSum * Extractor.inputColumnSize) / Math.Pow(squaredSum, 2.0)) - 3.0;
                     if (ACVar)
                         fv[acVarIndex++] = squaredSum / (Extractor.inputColumnSize - 1);
                     if (ACAbsCV)
                         fv[acAbsCVIndex++] = (Math.Sqrt(fv[acVarIndex - 1]) / meansbp[i]) * 100.0;

                    if (ACQuartiles)
                    {
                        Wockets.Utils.QuickSort.Sort(bpValues, 0, bpValues.Length - 1);
                        fv[acQuartilesIndex++] = bpValues[bpValues.Length / 4];
                        fv[acQuartilesIndex++] = bpValues[bpValues.Length / 2];
                        fv[acQuartilesIndex++] = bpValues[(bpValues.Length *3)/ 4];

                        if (ACIQR)
                            fv[acIQRIndex++] = fv[acQuartilesIndex - 1] - fv[acQuartilesIndex - 3];
                    }

                    if (ACRange)                    
                        fv[acRangeIndex++] = Math.Abs(max - min);

                    if (ACPitch)
                    {
                        double maxACF=-99999999.0;
                        int maxK=0;
                        for (int k=0;(k<Extractor.inputColumnSize);k++)
                            if (acf[k] > maxACF)
                            {
                                maxK = k;
                                maxACF = acf[k];
                            }

                        fv[acPitchIndex++] = maxK;
                    }

                    if (ACMCR)
                    {
                        int numCrossings=0;
                        for (int k = 1; (k < Extractor.inputColumnSize); k++)
                            if (((bpValues[k] > meansbp[i]) && (bpValues[k - 1] <= meansbp[i])) ||
                                 ((bpValues[k] < meansbp[i]) && (bpValues[k - 1] >= meansbp[i])))
                                numCrossings++;
                        fv[acMCRIndex++] = numCrossings;

                    }

                    if (ACCorr)
                    {
                        //***correlation coefficients
                        for (int k = i - 1; k >= 0; k--)
                        {
                            for (int w = 0; (w < Extractor.inputColumnSize); w++)
                                fv[acCorrIndex] += standardized[i][w] * standardized[k][w];
                            fv[acCorrIndex] /= (Extractor.inputColumnSize - 1);
                            fv[acCorrIndex] /= Math.Sqrt(fv[acVarIndex - 1]);  // ith std deviation
                            fv[acCorrIndex] /= Math.Sqrt(fv[acVarIndex - 1 - (i - k)]);  //kth std deviation 
                            acCorrIndex++;
                        }
                    }

                   
            
                }


                if (DCMeanTotal)
                    fv[dcMeanTotalIndex] = meanTotal;
                if (ACTotalAbsArea)
                    fv[acTotalAbsAreaIndex] = acTotalAbsArea;
                if (ACTotalSVM)
                    fv[acTotalSVMIndex] = acTotalSVM;
                if (ACTotalSF)
                    fv[acTotalSFIndex] = acTotalSF;
            }

            ocount++;
           
            
            if (ocount == 50)
            {
                TextWriter iwriter = new StreamWriter("input.csv");
                TextWriter lpwriter = new StreamWriter("lpinput.csv");
                TextWriter bpwriter = new StreamWriter("bpinput.csv");
                TextWriter fvwriter = new StreamWriter("fv.csv");
                for (i = 0; (i < inputRowSize); i++)
                {
                    for (j = 0; (j < inputColumnSize); j++)
                    {
                        if (j == inputColumnSize - 1)
                        {
                            iwriter.WriteLine(input[i][j]);
                            lpwriter.WriteLine(lpvalue[i][j]);
                            bpwriter.WriteLine(bpvalue[i][j]);
                        }
                        else
                        {
                            iwriter.Write(input[i][j]+",");
                            lpwriter.Write(lpvalue[i][j] + ",");
                            bpwriter.Write(bpvalue[i][j] + ",");
                        }                      
                    }

                }
                for (i = 0; (i < fv.Length); i++)
                    fvwriter.Write(fv[i] + ",");

                iwriter.Close();
                lpwriter.Close();
                bpwriter.Close();
                fvwriter.Close();
            }
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

                for (j = 0; (j < Extractor.inputColumnSize); j++)
                {
                    if (input[i][j] < min)
                        min = input[i][j];
                    if (input[i][j] > max)
                        max = input[i][j];
                    inputFFT[j] = (int)(input[i][j]);
                    sum += input[i][j];
                }

                means[i] = sum / Extractor.inputColumnSize;   //mean
                total += means[i];  //total mean

                if ((i + 1) % 3 == 0)
                {
                    features[distanceIndex++] = means[i - 2] - means[i - 1];
                    features[distanceIndex++] = means[i - 2] - means[i];
                    features[distanceIndex++] = means[i - 1] - means[i];
                }



                //fill variance
                variance = 0;
                for (j = 0; (j < Extractor.inputColumnSize); j++)
                {
                    variance += Math.Pow(input[i][j] - means[i], 2);
                    //***mean subtracted
                    standardized[i][j] = input[i][j] - means[i]; //mean subtracted

                }
                features[varianceIndex++] = variance / (Extractor.inputColumnSize - 1);

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

                //JFFT jfft = new JFFT(128);
                //jfft.transform(inputFFTD);       //check if this instruction corrupts values of data
                //double[] jreal = jfft.getReal();
                //double[] jim = jfft.getImaginary();               //imaginary part is the negative of the matlab result
                //jfft.computeMagnitudeAngle();
                //double[] jmag = jfft.getMagnitude();
                //double[] mymag = FFT.Magnitudes;


                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    for (int w = 0; (w < Extractor.inputColumnSize); w++)
                        features[correlationIndex] += standardized[i][w] * standardized[k][w];
                    features[correlationIndex] /= (Extractor.inputColumnSize - 1);
                    features[correlationIndex] /= Math.Sqrt(features[varianceIndex - 1]);  // ith std deviation
                    features[correlationIndex] /= Math.Sqrt(features[varianceIndex - 1 - (i - k)]);  //kth std deviation 
                    correlationIndex++;
                }

            }

            features[inputRowSize] = total;
        }






        public static string GetArffHeaderOptional()
        {

            string DCMean_ATTRIBUTES = "";
            string DCMeanTotal_ATTRIBUTES = "";
            string DCArea_ATTRIBUTES = "";
            string DCAreaSensor_ATTRIBUTES = "";
            string DCPostureDist_ATTRIBUTES = "";
            string ACAbsMean_ATTRIBUTES = "";
            string ACAbsArea_ATTRIBUTES = "";
            string ACAbsAreaSensor_ATTRIBUTES = "";
            string ACTotalAbsArea_ATTRIBUTES = "";
            string ACSVM_ATTRIBUTES = "";
            string ACTotalSVM_ATTRIBUTES = "";
            string ACFFTFreqs_ATTRIBUTES = "";
            string ACFFTMags_ATTRIBUTES = "";
            string ACEntropy_ATTRIBUTES = "";
            string ACEnergy_ATTRIBUTES = "";
            string ACSkew_ATTRIBUTES = "";
            string ACKur_ATTRIBUTES = "";
            string ACQuartiles_ATTRIBUTES = "";
            string ACVar_ATTRIBUTES = "";
            string ACAbsCV_ATTRIBUTES = "";
            string ACIQR_ATTRIBUTES = "";
            string ACRange_ATTRIBUTES = "";
            string ACBandEnergy_ATTRIBUTES = "";
            string ACLowEnergy_ATTRIBUTES = "";
            string ACModVigEnergy_ATTRIBUTES = "";
            string ACPitch_ATTRIBUTES = "";
            string ACMCR_ATTRIBUTES = "";
            string ACCorr_ATTRIBUTES = "";
            string ACSF_ATTRIBUTES = "";
            string ACTotalSF_ATTRIBUTES = "";

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


            for (int i = 0; (i < inputRowSize); i++)
            {
                if (DCMean)
                {
                    DCMean_ATTRIBUTES += "@ATTRIBUTE DCMean" + i + " NUMERIC\n";
                    arffAttriburesLabels[dcMeanIndex++] = "DCMean" + i;
                }
                if (DCArea)
                {
                    DCArea_ATTRIBUTES += "@ATTRIBUTE DCArea" + i + " NUMERIC\n";
                    arffAttriburesLabels[dcAreaIndex++] = "DCArea" + i;
                }

                if (ACAbsMean)
                {
                    ACAbsMean_ATTRIBUTES += "@ATTRIBUTE ACAbsMean" + i + " NUMERIC\n";
                    arffAttriburesLabels[acAbsMeanIndex++] = "ACAbsMean" + i;
                }

                if (ACAbsArea)
                {
                    ACAbsArea_ATTRIBUTES += "@ATTRIBUTE ACAbsArea" + i + " NUMERIC\n";
                    arffAttriburesLabels[acAbsAreaIndex++] = "ACAbsArea" + i;
                }

                if (SpectralContent)
                {
                    for (int j = 0; (j < NumberFrequencies); j++)
                    {
                        ACFFTFreqs_ATTRIBUTES += "@ATTRIBUTE ACFFTFreqs" + i + "_Max" + j + " NUMERIC\n";
                        arffAttriburesLabels[acFFTFreqsIndex++] = "ACFFTFreqs" + i + "_Max" + j;

                        ACFFTMags_ATTRIBUTES += "@ATTRIBUTE ACFFTMags" + i + "_Max" + j + " NUMERIC\n";
                        arffAttriburesLabels[acFFTMagsIndex++] = "ACFFTFreqs" + i + "_Max" + j;
                    }
                }

                if (ACEntropy)
                {
                    ACEntropy_ATTRIBUTES += "@ATTRIBUTE ACEntropy" + i + " NUMERIC\n";
                    arffAttriburesLabels[acEntropyIndex++] = "ACEntropy" + i;
                }

                if (ACEnergy)
                {
                    ACEnergy_ATTRIBUTES += "@ATTRIBUTE ACEnergy" + i + " NUMERIC\n";
                    arffAttriburesLabels[acEnergyIndex++] = "ACEnergy" + i;
                }

                if (ACSkew)
                {
                    ACSkew_ATTRIBUTES += "@ATTRIBUTE ACSkew" + i + " NUMERIC\n";
                    arffAttriburesLabels[acSkewIndex++] = "ACSkew" + i;
                }

                if (ACKur)
                {
                    ACKur_ATTRIBUTES += "@ATTRIBUTE ACKur" + i + " NUMERIC\n";
                    arffAttriburesLabels[acKurIndex++] = "ACKur" + i;
                }

                if (ACQuartiles)
                {
                    for (int j = 0; (j < 3); j++)
                    {
                        ACQuartiles_ATTRIBUTES += "@ATTRIBUTE ACQuartiles" + i + "_Quartile" + j + " NUMERIC\n";
                        arffAttriburesLabels[acQuartilesIndex++] = "ACQuartiles" + i + "_Quartile" + j;
                    }
                }

                if (ACVar)
                {
                    ACVar_ATTRIBUTES += "@ATTRIBUTE ACVar" + i + " NUMERIC\n";
                    arffAttriburesLabels[acVarIndex++] = "ACVar" + i;
                }

                if (ACAbsCV)
                {
                    ACAbsCV_ATTRIBUTES += "@ATTRIBUTE ACAbsCV" + i + " NUMERIC\n";
                    arffAttriburesLabels[acAbsCVIndex++] = "ACAbsCV" + i;
                }

                if (ACIQR)
                {
                    ACIQR_ATTRIBUTES += "@ATTRIBUTE ACIQR" + i + " NUMERIC\n";
                    arffAttriburesLabels[acIQRIndex++] = "ACIQR" + i;
                }


                if (ACRange)
                {
                    ACRange_ATTRIBUTES += "@ATTRIBUTE ACRange" + i + " NUMERIC\n";
                    arffAttriburesLabels[acRangeIndex++] = "ACRange" + i;
                }

                if (ACBandEnergy)
                {
                    ACBandEnergy_ATTRIBUTES += "@ATTRIBUTE ACBandEnergy" + i + " NUMERIC\n";
                    arffAttriburesLabels[acBandEnergyIndex++] = "ACBandEnergy" + i;
                }

                if (ACLowEnergy)
                {
                    ACLowEnergy_ATTRIBUTES += "@ATTRIBUTE ACLowEnergy" + i + " NUMERIC\n";
                    arffAttriburesLabels[acLowEnergyIndex++] = "ACLowEnergy" + i;
                }

                if (ACModVigEnergy)
                {
                    ACModVigEnergy_ATTRIBUTES += "@ATTRIBUTE ACModVigEnergy" + i + " NUMERIC\n";
                    arffAttriburesLabels[acModVigEnergyIndex++] = "ACModVigEnergy" + i;
                }

                if (ACPitch)
                {
                    ACPitch_ATTRIBUTES += "@ATTRIBUTE ACPitch" + i + " NUMERIC\n";
                    arffAttriburesLabels[acPitchIndex++] = "ACPitch" + i;
                }

                if (ACMCR)
                {
                    ACMCR_ATTRIBUTES += "@ATTRIBUTE ACMCR" + i + " NUMERIC\n";
                    arffAttriburesLabels[acMCRIndex++] = "ACMCR" + i;
                }

                if (ACCorr)
                {
                    //***correlation coefficients
                    for (int k = i - 1; k >= 0; k--)
                    {
                        ACCorr_ATTRIBUTES += "@ATTRIBUTE ACCorr" + i +"_"+k+ " NUMERIC\n";
                        arffAttriburesLabels[acCorrIndex++] = "ACCorr" + i + "_" + k;              
                    }
                }
            }

            for (int i = 0; (i < extractorSensorCount); i++)
            {
                if (DCAreaSensor)
                {
                    DCAreaSensor_ATTRIBUTES += "@ATTRIBUTE DCAreaSensor" + i + " NUMERIC\n";
                    arffAttriburesLabels[dcAreaSensorIndex++] = "DCArea" + i;
                }

                if (DCPostureDist)
                {
                    DCPostureDist_ATTRIBUTES += "@ATTRIBUTE DCPostureDist" + i + "_MeanX_MeanY NUMERIC\n";
                    arffAttriburesLabels[dcPostureDistIndex++] = "DCPostureDist" + i + "_MeanX_MeanY";
                    DCPostureDist_ATTRIBUTES += "@ATTRIBUTE DCPostureDist" + i + "_MeanX_MeanZ NUMERIC\n";
                    arffAttriburesLabels[dcPostureDistIndex++] = "DCPostureDist" + i + "_MeanX_MeanZ";
                    DCPostureDist_ATTRIBUTES += "@ATTRIBUTE DCPostureDist" + i + "_MeanY_MeanZ NUMERIC\n";
                    arffAttriburesLabels[dcPostureDistIndex++] = "DCPostureDist" + i + "_MeanY_MeanZ";
                }

                if (ACAbsAreaSensor)
                {
                    ACAbsAreaSensor_ATTRIBUTES += "@ATTRIBUTE ACAbsAreaSensor" + i + " NUMERIC\n";
                    arffAttriburesLabels[acAbsAreaSensorIndex++] = "ACAbsAreaSensor" + i;
                }


                if (ACSVM)
                {
                    ACSVM_ATTRIBUTES += "@ATTRIBUTE ACSVM" + i + " NUMERIC\n";
                    arffAttriburesLabels[acSVMIndex++] = "ACSVM" + i;
                }

                if (ACSF)
                {
                    ACSF_ATTRIBUTES += "@ATTRIBUTE ACSF" + i + " NUMERIC\n";
                    arffAttriburesLabels[acSFIndex++] = "ACSF" + i;
                }
            }

            if (DCMeanTotal)
            {
                DCMeanTotal_ATTRIBUTES = "@ATTRIBUTE DCMeanTotal NUMERIC\n";
                arffAttriburesLabels[dcMeanTotalIndex] = "DCMeanTotal";
            }

            if (ACTotalAbsArea)
            {
                ACTotalAbsArea_ATTRIBUTES = "@ATTRIBUTE ACTotalAbsArea NUMERIC\n";
                arffAttriburesLabels[acTotalAbsAreaIndex] = "ACTotalAbsArea";
            }

            if (ACTotalSVM)
            {
                ACTotalSVM_ATTRIBUTES = "@ATTRIBUTE ACTotalSVM NUMERIC\n";
                arffAttriburesLabels[acTotalSVMIndex] = "ACTotalSVM";
            }

            if (ACTotalSF)
            {
                ACTotalSF_ATTRIBUTES = "@ATTRIBUTE ACTotalSF NUMERIC\n";
                arffAttriburesLabels[acTotalSFIndex] = "ACTotalSF";
            }

            string allAttributes = "";
            
            if (DCMean)
                allAttributes += DCMean_ATTRIBUTES;
            if (DCMeanTotal)
                allAttributes += DCMeanTotal_ATTRIBUTES;
            if (DCArea)
                allAttributes += DCArea_ATTRIBUTES;
            if (DCAreaSensor)
                allAttributes += DCAreaSensor_ATTRIBUTES;
            if (DCPostureDist)
                allAttributes += DCPostureDist_ATTRIBUTES;
            if (ACAbsMean)
                allAttributes += ACAbsMean_ATTRIBUTES;
            if (ACAbsArea)
                allAttributes += ACAbsArea_ATTRIBUTES;
            if (ACAbsAreaSensor)
                allAttributes += ACAbsAreaSensor_ATTRIBUTES;
            if (ACTotalAbsArea)
                allAttributes += ACTotalAbsArea_ATTRIBUTES;
            if (ACSVM)
                allAttributes += ACSVM_ATTRIBUTES;
            if (ACTotalSVM)
                allAttributes += ACTotalSVM_ATTRIBUTES;
            if (SpectralContent)
                allAttributes +=ACFFTFreqs_ATTRIBUTES + ACFFTMags_ATTRIBUTES;
            if (ACEntropy)
                allAttributes += ACEntropy_ATTRIBUTES;
            if (ACEnergy)
                allAttributes += ACEnergy_ATTRIBUTES;
            if (ACSkew)
                allAttributes += ACSkew_ATTRIBUTES;
            if (ACKur)
                allAttributes += ACKur_ATTRIBUTES;
            if (ACQuartiles)
                allAttributes += ACQuartiles_ATTRIBUTES;
            if (ACVar)
                allAttributes += ACVar_ATTRIBUTES;
            if (ACAbsCV)
                allAttributes += ACAbsCV_ATTRIBUTES;
            if (ACIQR)
                allAttributes += ACIQR_ATTRIBUTES;
            if (ACRange)
                allAttributes += ACRange_ATTRIBUTES;
            if (ACBandEnergy)
                allAttributes += ACBandEnergy_ATTRIBUTES;
            if (ACLowEnergy)
                allAttributes += ACLowEnergy_ATTRIBUTES;
            if (ACModVigEnergy)
                allAttributes += ACModVigEnergy_ATTRIBUTES;
            if (ACPitch)
                allAttributes += ACPitch_ATTRIBUTES;
            if (ACMCR)
                allAttributes += ACMCR_ATTRIBUTES;
            if (ACCorr)
                allAttributes += ACCorr_ATTRIBUTES;
            if (ACSF)
                allAttributes += ACSF_ATTRIBUTES;
            if (ACTotalSF)
                allAttributes += ACTotalSF_ATTRIBUTES;

            return allAttributes;
        }




        //public static string GetArffHeader(int inputRowSize, int fftMaximumFrequencies)
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
                    attributeLocation["Dist_Mean" + (i - 2) + "_Mean" + (i - 1)] = null;
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 2) + "_Mean" + (i) + " NUMERIC\n";
                    arffAttriburesLabels[distanceIndex++] = "Dist_Mean" + (i - 2) + "_Mean" + (i);
                    attributeLocation["Dist_Mean" + (i - 2) + "_Mean" + (i)] = null;
                    DISTANCE_ATTRIBUTES += "@ATTRIBUTE Dist_Mean" + (i - 1) + "_Mean" + (i) + " NUMERIC\n";
                    arffAttriburesLabels[distanceIndex++] = "Dist_Mean" + (i - 1) + "_Mean" + (i);
                    attributeLocation["Dist_Mean" + (i - 1) + "_Mean" + (i)] = null;
                }


                VARIANCE_ATTRIBUTES += "@ATTRIBUTE Variance_" + i + " NUMERIC\n";
                arffAttriburesLabels[varianceIndex++] = "Variance_" + i;
                attributeLocation["Variance_" + i] = i / 3;

                RANGE_ATTRIBUTES += "@ATTRIBUTE RANGE_" + i + " NUMERIC\n";
                arffAttriburesLabels[rangeIndex++] = "RANGE_" + i;
                attributeLocation["RANGE_" + i] = i / 3;
                for (int k = 0; (k < (fftMaximumFrequencies * 2)); k++)
                {
                    k++;
                    FFT_ATTRIBUTES += "@ATTRIBUTE FFT_MAX_FREQ" + i + "_" + k + " NUMERIC\n";
                    arffAttriburesLabels[fftIndex++] = "FFT_MAX_FREQ" + i + "_" + k;
                    attributeLocation["FFT_MAX_FREQ" + i + "_" + k] = i / 3;
                    FFT_ATTRIBUTES += "@ATTRIBUTE FFT_MAX_MAG" + i + "_" + k + " NUMERIC\n";
                    arffAttriburesLabels[fftIndex++] = "FFT_MAX_MAG" + i + "_" + k;
                    attributeLocation["FFT_MAX_MAG" + i + "_" + k] = i / 3;
                }

                ENERGY_ATTRIBUTES += "@ATTRIBUTE ENERGY_" + i + " NUMERIC\n";
                arffAttriburesLabels[energyIndex++] = "ENERGY_" + i;
                attributeLocation["ENERGY_" + i] = i / 3;

                //***correlation coefficients
                for (int k = i - 1; k >= 0; k--)
                {
                    CORRELATION_ATTRIBUTES += "@ATTRIBUTE CORRELATION_" + k + "_" + i + " NUMERIC\n";
                    arffAttriburesLabels[correlationIndex++] = "CORRELATION_" + k + "_" + i;
                    attributeLocation["CORRELATION_" + k + "_" + i] = null;
                }
            }

            TOTAL_ATTRIBUTE += "@ATTRIBUTE TotalMean NUMERIC\n";
            arffAttriburesLabels[distanceIndex] = "TotalMean";
            attributeLocation["TotalMean"] = null;

            return DISTANCE_ATTRIBUTES + TOTAL_ATTRIBUTE + VARIANCE_ATTRIBUTES + RANGE_ATTRIBUTES +
               FFT_ATTRIBUTES + ENERGY_ATTRIBUTES + CORRELATION_ATTRIBUTES;
        }

        /*public static string toString()
        {
            string s = "";
            int i = 0;

            for (i = 0; (i < features.Length - 1); i++)
                s += features[i].ToString("F2") + ",";
            s += features[i].ToString("F2");
            return s;

        }*/

        public static string toString()
        {
            string s = "";
            int i = 0;

            for (i = 0; (i < fv.Length - 1); i++)
                s += fv[i].ToString("F2") + ",";
            s += fv[i].ToString("F2");
            return s;

        }

    }
}


