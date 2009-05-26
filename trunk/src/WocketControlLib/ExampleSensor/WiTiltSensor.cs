using System;
using System.Collections.Generic;
using System.Text;

using System.Threading;
using WocketControlLib;
using BluetoothLayer;

namespace ExampleSensor
{
    public class WiTiltSensor : WocketSensor
    {
        private byte[] buffer;
        private int bufferOffset = 0;
        private BluetoothStream btStream;
        private byte[] addr;
        private string pin;

        private short xMid;
        private short xWidth;
        private short yMid;
        private short yWidth;
        private short zMid;
        private short zWidth;
        private short gyroZero;
        private ushort lastSampleNumber = 0;
        private short[] xBuffer;
        private int sampleCounter = 0;
        private short[] yBuffer;
        //private int yBufferOffset;
        private short[] zBuffer;
        //private int zBufferOffset;
        private short[] gyroBuffer;
        private short[] otherFeaturesBuffer;
        private int[] otherFeaturesBufferInts;
        private ushort[] batteryBuffer;
        public static TimeSpan RAW_SIGNAL_PERIOD = TimeSpan.FromSeconds(0.00285714285714);//350 Hz
        public static TimeSpan BATTERY_LEVEL_PERIOD = TimeSpan.FromMilliseconds(100);//10 Hz
        private const int SAMPLE_BUFFER_SIZE = 1024;

        public WiTiltSensor(byte[] addrParam, string pinParam)
        {
            addr = addrParam;
            pin = pinParam;
            buffer = new byte[5120];
            xBuffer = new short[SAMPLE_BUFFER_SIZE];
            yBuffer = new short[SAMPLE_BUFFER_SIZE];
            zBuffer = new short[SAMPLE_BUFFER_SIZE];
            gyroBuffer = new short[SAMPLE_BUFFER_SIZE];
            batteryBuffer = new ushort[SAMPLE_BUFFER_SIZE];
            otherFeaturesBuffer = new short[128];
            otherFeaturesBufferInts = new int[128];
        }

        protected override int getSleepTimeMillis()
        {
            return 400;
        }

        //this function actually reads/decodes the stream and stores the intermediate values
        private void getSensorValues() 
        {
            int missedSamples = 0;
            int bytesRead = btStream.Read(buffer, bufferOffset, buffer.Length - bufferOffset);
            if (bytesRead == 0)
                return;
            int byteCounter = 0;
            //int state = 0;
            
            while (bytesRead >= 15 && sampleCounter < SAMPLE_BUFFER_SIZE)
            {
                if (buffer[byteCounter] != 0x23 || buffer[byteCounter + 1] != 0x40 || buffer[byteCounter + 14] != 0x24 || buffer[byteCounter + 4] > 3 || buffer[byteCounter + 6] > 3 || buffer[byteCounter + 8] > 3)
                {
                    byteCounter++;
                    bytesRead--;
                    continue;
                }
                ushort newSampleNumber = (ushort)(buffer[byteCounter + 2] << 8);
                newSampleNumber |= buffer[byteCounter + 3];
                if (newSampleNumber != ++lastSampleNumber)
                {
                    missedSamples++;
                    lastSampleNumber = newSampleNumber;
                }
                short x = (short)((buffer[byteCounter + 4] << 8 | buffer[byteCounter + 5]) - xMid);
                short y = (short)((buffer[byteCounter + 6] << 8 | buffer[byteCounter + 7]) - yMid);
                short z = (short)((buffer[byteCounter + 8] << 8 | buffer[byteCounter + 9]) - zMid);
                ushort battery = (ushort)(buffer[byteCounter + 10] << 8 | buffer[byteCounter + 11]);
                short gyro = (short)((buffer[byteCounter + 12] << 8 | buffer[byteCounter + 13]) - gyroZero);
                xBuffer[sampleCounter] = x;
                yBuffer[sampleCounter] = y;
                zBuffer[sampleCounter] = z;
                batteryBuffer[sampleCounter] = battery;
                gyroBuffer[sampleCounter] = gyro;
                sampleCounter++;
                byteCounter += 15;
                bytesRead -= 15;
                
                /*
                switch (state)
                {
                    case 0://state 0 means looking for the start of a packet
                        if (buffer[byteCounter] == 0x23 && buffer[byteCounter + 1] == 0x40)//start of packet marker
                            state = 1;
                        bytesRead--;
                        byteCounter++;
                        break;
                    case 1://state 1 means reading a packet. Counter now points at the second byte in the packet
                        //ushort newSampleNumber = BitConverter.ToUInt16(buffer, byteCounter + 1);
                        ushort newSampleNumber = (ushort)(buffer[byteCounter + 1] << 8) ;
                        newSampleNumber |= buffer[byteCounter + 2];
                        if (newSampleNumber != ++lastSampleNumber)
                        {
                            missedSamples++;
                            lastSampleNumber = newSampleNumber;
                        }
                        
                        //the above doesn't work because BitConverter expects values to be big endian and they're not.
                        //instead, we'll do it manually
                        xBuffer[sampleCounter] = (short)((buffer[byteCounter + 3] << 8 | buffer[byteCounter + 4]) - xMid);
                        yBuffer[sampleCounter] = (short)((buffer[byteCounter + 5] << 8 | buffer[byteCounter + 6]) - yMid);
                        zBuffer[sampleCounter] = (short)((buffer[byteCounter + 7] << 8 | buffer[byteCounter + 8]) - zMid);
                        batteryBuffer[sampleCounter] = (ushort)(buffer[byteCounter + 9] << 8 | buffer[byteCounter + 10]);
                        gyroBuffer[sampleCounter] = (short)((buffer[byteCounter + 11] << 8 | buffer[byteCounter + 12]) - gyroZero);
                        
                        sampleCounter++;
                        byteCounter += 14;
                        bytesRead -= 14;
                        state = 0;
                        break;
                }
                */
            }

            bufferOffset = bytesRead;//if there are 7 bytes still available, the next read will start reading at position 7, etc...
            //bytesRead is down to < 15. Shift bytes down to the front of the buffer
            for (int ii = 0; ii < bytesRead; ii++)
            {
                buffer[ii] = buffer[byteCounter + ii];
            }

            //return sampleCounter;
        }

        protected override void OnStart()
        {
            btStream = BluetoothStream.OpenConnection(addr, pin);
            buffer[0] = 0x41;//A, aborts the binary stream if it's running.
            btStream.Write(buffer, 0, 1);

            //clear out the detritus
            int bytesRead = btStream.Read(buffer, 0, buffer.Length);
            if (bytesRead != 0)
            {
                Thread.Sleep(1000);
                bytesRead = btStream.Read(buffer, 0, buffer.Length);
            }
            
            sendCharacterCommand(0x20);//space
            string s = sendCharacterCommand(0x33);//3, command for calibration menu
            parseCalibrationString(s);
            sendCharacterCommand(0x78);//x, exits the calibration menu
            sendCharacterCommand(0x35);//5, command for output menu
            sendCharacterCommand(0x33);//3, command for binary output
            sendCharacterCommand(0x37);//7, command for frequency menu
            for (int ii = 0; ii < 22; ii++)
            {
                sendCharacterCommandNoPause(0x69);//i, increase frequency command
            }
            sendCharacterCommand(0x78);//x, leave the frequency menu
            sendCharacterCommand(0x31);//1, the start transmitting command
            buffer[0] = 0x53;//S, start command, will immediately start spitting out values after this
            btStream.Write(buffer, 0, 1);
        }

        private void sendCharacterCommandNoPause(byte command)
        {
            buffer[0] = command;
            btStream.Write(buffer, 0, 1);
        }
        protected override void OnStop()
        {
            btStream.Close();
        }
        protected override void CalculateFeatures(List<Feature> features)
        {
            if (features.Count == 0)
                return;

            //there is at least one feature, and they all require reading the 
            getSensorValues();

            features.Sort(FeaturePeriodComparer.instance);
            TimeSpan longestPeriod = features[0].Period;
            int samplesToUse;
            if (features[0].Period == RAW_SIGNAL_PERIOD)
            {
                //if the user only wants raw data, use all the samples.
                samplesToUse = sampleCounter;
            }
            else
            {
                //otherwise, it's the number of samples available divided by the 
                //number of samples needed to calculate one instance of the 
                //feature with the longest period
                samplesToUse = sampleCounter - (sampleCounter % ((int)(longestPeriod.Ticks / RAW_SIGNAL_PERIOD.Ticks)));
            }
            if (samplesToUse == 0)
                return;//FIXME take this out when done testing

            foreach (Feature f in features)
            {
                switch (f.Name)
                {
                    case "rawX":
                        writeFeatureValues(xBuffer, 0, samplesToUse, f);
                        break;
                    case "rawY":
                        writeFeatureValues(yBuffer, 0, samplesToUse, f);
                        break;
                    case "rawZ":
                        writeFeatureValues(zBuffer, 0, samplesToUse, f);
                        break;
                    case "meanX":
                        int samplesPerMean = (int)(f.Period.Ticks / RAW_SIGNAL_PERIOD.Ticks);
                        int numberOfMeans = samplesToUse / samplesPerMean;
                        for (int ii = 0; ii < numberOfMeans; ii++)
                        {
                            int mean = 0;
                            for (int jj = 0; jj < samplesPerMean; jj++)
                            {
                                mean += xBuffer[jj + ii * samplesPerMean];// -yBuffer[jj + ii * samplesPerMean];
                            }
                            otherFeaturesBuffer[ii] = (short)(mean / samplesPerMean);
                        }
                        writeFeatureValues(otherFeaturesBuffer, 0, numberOfMeans, f);
                        break;
                    case "meanY":
                        samplesPerMean = (int)(f.Period.Ticks / RAW_SIGNAL_PERIOD.Ticks);
                        numberOfMeans = samplesToUse / samplesPerMean;
                        for (int ii = 0; ii < numberOfMeans; ii++)
                        {
                            int mean = 0;
                            for (int jj = 0; jj < samplesPerMean; jj++)
                            {
                                mean += yBuffer[jj + ii * samplesPerMean];// -zBuffer[jj + ii * samplesPerMean];
                            }
                            otherFeaturesBuffer[ii] = (short)(mean / samplesPerMean);
                        }
                        writeFeatureValues(otherFeaturesBuffer, 0, numberOfMeans, f);
                        break;
                    case "meanZ":
                        samplesPerMean = (int)(f.Period.Ticks / RAW_SIGNAL_PERIOD.Ticks);
                        numberOfMeans = samplesToUse / samplesPerMean;
                        for (int ii = 0; ii < numberOfMeans; ii++)
                        {
                            int mean = 0;
                            for (int jj = 0; jj < samplesPerMean; jj++)
                            {
                                mean += zBuffer[jj + ii * samplesPerMean];// -xBuffer[jj + ii * samplesPerMean];
                            }
                            otherFeaturesBuffer[ii] = (short)(mean / samplesPerMean);
                        }
                        writeFeatureValues(otherFeaturesBuffer, 0, numberOfMeans, f);
                        break;
                    case "varianceX":
                        int samplesPerVariance = (int)(f.Period.Ticks / RAW_SIGNAL_PERIOD.Ticks);
                        int numberOfVariances = samplesToUse / samplesPerVariance;
                        for (int ii = 0; ii < numberOfVariances; ii++)
                        {
                            int mean = 0;
                            for (int jj = 0; jj < samplesPerVariance; jj++)
                            {
                                mean += xBuffer[jj + ii * samplesPerVariance];
                            }
                            mean /= samplesPerVariance;
                            long variance = 0;
                            for (int jj = 0; jj < samplesPerVariance; jj++)
                            {
                                int temp = (xBuffer[jj + ii * samplesPerVariance] - mean);
                                temp *= temp;
                                variance += temp;
                            }
                            variance /= samplesPerVariance;
                            otherFeaturesBufferInts[ii] = (int)(variance & 0xFFFFFFFF);
                        }
                        writeFeatureValues(otherFeaturesBufferInts, 0, numberOfVariances, f);
                        break;
                    case "varianceY":
                        samplesPerVariance = (int)(f.Period.Ticks / RAW_SIGNAL_PERIOD.Ticks);
                        numberOfVariances = samplesToUse / samplesPerVariance;
                        for (int ii = 0; ii < numberOfVariances; ii++)
                        {
                            int mean = 0;
                            for (int jj = 0; jj < samplesPerVariance; jj++)
                            {
                                mean += yBuffer[jj + ii * samplesPerVariance];
                            }
                            mean /= samplesPerVariance;
                            int variance = 0;
                            for (int jj = 0; jj < samplesPerVariance; jj++)
                            {
                                int temp = (yBuffer[jj + ii * samplesPerVariance] - mean);
                                temp *= temp;
                                variance += temp;
                            }
                            variance /= samplesPerVariance;
                            otherFeaturesBufferInts[ii] = variance;
                        }
                        writeFeatureValues(otherFeaturesBufferInts, 0, numberOfVariances, f);
                        break;
                    case "varianceZ":
                        samplesPerVariance = (int)(f.Period.Ticks / RAW_SIGNAL_PERIOD.Ticks);
                        numberOfVariances = samplesToUse / samplesPerVariance;
                        for (int ii = 0; ii < numberOfVariances; ii++)
                        {
                            int mean = 0;
                            for (int jj = 0; jj < samplesPerVariance; jj++)
                            {
                                mean += zBuffer[jj + ii * samplesPerVariance];
                            }
                            mean /= samplesPerVariance;
                            int variance = 0;
                            for (int jj = 0; jj < samplesPerVariance; jj++)
                            {
                                int temp = (zBuffer[jj + ii * samplesPerVariance] - mean);
                                temp *= temp;
                                variance += temp;
                            }
                            variance /= samplesPerVariance;
                            otherFeaturesBufferInts[ii] = variance;
                        }
                        writeFeatureValues(otherFeaturesBufferInts, 0, numberOfVariances, f);
                        break;
                    default:
                        throw new Exception("Unknown feature: " + f);
                }
            }
            //move the samples down in the array
            int tempCounter = 0;
            for (int ii = samplesToUse; ii < sampleCounter; ii++)
            {
                xBuffer[tempCounter] = xBuffer[ii];
                yBuffer[tempCounter] = yBuffer[ii];
                zBuffer[tempCounter] = zBuffer[ii];
                gyroBuffer[tempCounter] = gyroBuffer[ii];
                batteryBuffer[tempCounter] = batteryBuffer[ii];
                tempCounter++;
            }
            sampleCounter -= samplesToUse;

        }
        /*
        protected override bool featureNameSupported(string name)
        {
            return name == "rawX" || name == "rawY" || name == "rawZ" ||
                name == "meanX" || name == "meanY" || name == "meanZ" ||
                name == "varianceX" || name == "varianceY" || name == "varianceZ" ||
                name == "batteryLevel" || name == "gyro";
        }*/
        protected override bool FeatureSupported(string name, TimeSpan period)
        {
            switch (name)
            {
                case "rawX":
                case "rawY":
                case "rawZ":
                    return period == RAW_SIGNAL_PERIOD;
                case "meanX":
                case "meanY":
                case "meanZ":
                case "varianceX":
                case "varianceY":
                case "varianceZ":
                    return period >= TimeSpan.FromMilliseconds(10) && period <= TimeSpan.FromMilliseconds(1000);
                case "batteryLevel":
                    return period == BATTERY_LEVEL_PERIOD;
                default:
                    return false;
            }
        }
        
        private void parseCalibrationString(string s)
        {
            string xMidString = s.Substring(s.IndexOf("X Midpoint: ") + 12, 3);
            string xWidthString = s.Substring(s.IndexOf("X G-Width: ") + 11, 3);
            string yMidString = s.Substring(s.IndexOf("Y Midpoint: ") + 12, 3);
            string yWidthString = s.Substring(s.IndexOf("Y G-Width: ") + 11, 3);
            string zMidString = s.Substring(s.IndexOf("Z Midpoint: ") + 12, 3);
            string zWidthString = s.Substring(s.IndexOf("Z G-Width: ") + 11, 3);
            string gyroZeroString = s.Substring(s.IndexOf("Gyro Zero Value: ") + 17, 3);

            xMid = Int16.Parse(xMidString);
            xWidth = Int16.Parse(xWidthString);
            yMid = Int16.Parse(yMidString);
            yWidth = Int16.Parse(yWidthString);
            zMid = Int16.Parse(zMidString);
            zWidth = Int16.Parse(zWidthString);
            gyroZero = Int16.Parse(gyroZeroString);
        }

        private string sendCharacterCommand(byte command)
        {
            
            buffer[0] = command;
            btStream.Write(buffer, 0, 1);
            Thread.Sleep(1000);
            int bytesRead = btStream.Read(buffer, 0, buffer.Length);
            return ASCIIEncoding.ASCII.GetString(buffer, 0, bytesRead);
        }
    }
}
