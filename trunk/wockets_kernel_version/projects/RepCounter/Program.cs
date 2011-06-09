using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Collections;
using WocketsWeka.Utils;
using WocketsWeka.Utils.Filters;


namespace RepCounter
{
    class Program
    {
        static string sessionDirectory = "Session5-9-17-37-18";
        static BPButterworth butter;
        
        static void Main(string[] args)
        {
            butter = new BPButterworth(Frequency._0_2Hz, Frequency._5_0Hz, Order.Second, SamplingRates._90Hz,a,b);
            ComputeMagnitude();
            //ComputeNewData();
            
            //bbutter = new ButterWorthDF();
            //int[] vals = bbutter.ccof_bwbp(10);
        }

        static double[] b = new double[5] {0.0051,0.0,-0.0103,0.0,0.0051};
        static double[] a = new double[5] { 1.00, -3.7856, 5.3793, -3.4016, 0.8079 };

        static int NZEROS = 4;
        static int NPOLES = 4;
        static int ORDER = 4;
        static double[] xv = new double[NZEROS + 1];
        static double[] yv = new double[NPOLES + 1];
        static double[] ButterWorth(double[] data)
        {

            double[] filtered = new double[data.Length];

            for (int i = 0; (i < data.Length); i++)
            {

                xv[0] = xv[1]; xv[1] = xv[2]; xv[2] = xv[3]; xv[3] = xv[4];
                xv[4] = data[i];
                yv[0] = yv[1]; yv[1] = yv[2]; yv[2] = yv[3]; yv[3] = yv[4];
                yv[4] = (xv[0] + xv[4]) - 2 * xv[2] -
                    a[1] * yv[3] - a[2] * yv[2] - a[3] * yv[1] - a[4] * yv[0];

                filtered[i] = yv[4];
                if ((filtered[i] < -957) && (filtered[i] > -958))
                    Console.Write("");
            }
            

            return filtered;
        }

        static void ComputeNewData()
        {

            string directory = @"C:\Users\albinali\Desktop\FitFriends\Test2\Sombit\" + sessionDirectory + "\\";

            string[] files = Directory.GetFiles(directory, "*newdata*");

            double[] window = new double[1024];
            double[] xvals = new double[1024];
            for (int i = 0; (i < xvals.Length); i++)
                xvals[i] = i;

            int index = 0;
            for (int i = 0; (i < files.Length); i++)
            {


                TextWriter twf = new StreamWriter(directory + "Sensor" + i + "-Filtered.csv");                
                TextReader tr = new StreamReader(files[i]);
                tr.ReadLine();
                string line = "";

                while ((line = tr.ReadLine()) != null)
                {
                    string[] tokens = line.Split(new char[] { ',' });

                    double magnitude = Convert.ToDouble(tokens[0]);                    
                    window[index++] = magnitude;
                    if (index > window.Length - 1)
                    {
                        double[] filtered = ButterWorth(window);
 




                        //compute the first and second derivatives
                        // check zero crossings for peaks
                        // check zero crossings for troughs
                        // check for inflection points

                        //chain peaks or troughs for counting


                        for (int k = 0; (k < filtered.Length); k++)
                        {
                            twf.WriteLine(filtered[k]);
                        }
                        index = 0;
                    }
                    //                  data.Add(magnitude);            
                  
                }

                twf.Close();

            }
        }

        static double previous = Double.MinValue;
        static double[] Derivative(double[] data)
        {
            double[] diff = new double[data.Length];

            for (int i = 0; (i < data.Length); i++)
            {
                if (previous == Double.MinValue)
                    diff[i] = 0;
                else
                    diff[i] = data[i] - previous;
                previous = data[i];
            }                
            return diff;
        }

        
        static ArrayList PeakCrossings(double[] data)
        {

            ArrayList locations = new ArrayList();       
            for (int i = 1; (i < data.Length); i++)
            {
                if ((data[i - 1] > 0) && (data[i] < 0))
                    locations.Add(i-1);
            }

            return locations;
        }

        static ArrayList TroughCrossings(double[] data)
        {
            ArrayList locations = new ArrayList();  

            for (int i = 1; (i < data.Length); i++)
            {
                if ((data[i - 1]< 0) && (data[i] > 0))
                    locations.Add(i);
            }

            return locations;
        }

        static void ComputeMagnitude()
        {

            string directory = @"C:\Users\albinali\Desktop\FitFriends\Test2\Sombit\" + sessionDirectory + "\\merged";

            string[] files = Directory.GetFiles(directory, "*_RawCorrectedData_*");
        
            double[] xvals = new double[1024];
            for (int i = 0; (i < xvals.Length); i++)
                xvals[i] = i;

            int index = 0;           
           
            for (int i = 0; (i < files.Length); i++)
            {
                TextWriter tw = new StreamWriter(directory + "Sensor" + i + "-Mags.csv");
                TextWriter twf = new StreamWriter(directory + "Sensor" + i + "-Filtered.csv");
                TextWriter twi = new StreamWriter(directory + "Sensor" + i + "-Interpolated.csv");
                TextWriter twp = new StreamWriter(directory + "Sensor" + i + "-Peaks.csv");
                TextWriter twt = new StreamWriter(directory + "Sensor" + i + "-Troughs.csv");
                TextWriter tws = new StreamWriter(directory + "Sensor" + i + "-Suppressed.csv");
                TextWriter twss = new StreamWriter(directory + "Sensor" + i + "-Smoothened.csv");
                TextWriter twc = new StreamWriter(directory + "Sensor" + i + "-Corrected.csv");
                TextWriter twcp = new StreamWriter(directory + "Sensor" + i + "-Counted.csv");
                TextReader tr = new StreamReader(files[i]);
                tr.ReadLine();
                string line = "";
                int totalPeaks = 0;
                int windowStartIndex = 0;
                

                //Store magnitudes in a window
                double[] window = new double[1536];
                for (int k = 0; (k < 512); k++)
                    window[k] = 0;
                index = 512;

                while (true)
                {
                    line = tr.ReadLine();
                    double magnitude = 0.0;
                    long time = 0;
                    if (line != null)
                    {
                        string[] tokens = line.Split(new char[] { ',' });
                        time = (long)Convert.ToDouble(tokens[0]);
                        int x = Convert.ToInt32(tokens[1]);
                        int y = Convert.ToInt32(tokens[2]);
                        int z = Convert.ToInt32(tokens[3]);

                        #region Compute Magnitude
                        //As the data arrives compute the magnitude
                        magnitude = Math.Sqrt(Math.Pow(x, 2.0) + Math.Pow(y, 2.0) + Math.Pow(z, 2.0));
                        #endregion Compute Magnitude

                    }
                    // Test if the window is full
                    if ((line==null)||(index >= window.Length))
                    {

                        ArrayList peaks = new ArrayList();
                        ArrayList peakValues = new ArrayList();
                        ArrayList troughs = new ArrayList();
                        ArrayList inflections = new ArrayList();
                        ArrayList filteredData = new ArrayList();
                        //Reset the index for the next window
                       

                        #region Eliminate peaks from edges
                        //Step 1: Check that no potential peaks lie at the end of the window
                        // scan backwards until you find 3 consecutive decreasing or increasing points
                        // pick the first point as the end of the window and the rest will go in the
                        // next window
                        // BUG: Could fail to find one
                        int end = 0;
                        for (int k = index-1; (k >=2); k--)
                        {
                            if (((window[k] > window[k - 1]) && (window[k - 1] > window[k - 2])) ||
                                ((window[k] < window[k - 1]) && (window[k - 1] < window[k - 2])))
                            {
                                end = k - 2;
                                break;
                            }
                        }
                        index = 512;
                        #endregion Eliminate peaks from edges

                        #region Setup filtered window and apply filter
                        // STEP 2: Once the end of the window is identified
                        // copy the new window and apply to it a filter
                        // then copy the remaining magnitudes into the next window
                        double[] filtered;
                        if (end != 0)
                        {
                            double[] window2 = new double[end + 1];
                            for (int r = 0; (r < window2.Length); r++)
                                window2[r] = window[r];

                            //Filter the window
                            filtered = butter.Apply(window2);

                            //Copy the remaining elements in the next window
                            for (int r = end + 1; (r < window.Length); r++)
                                window[index++] = window[r];
                        }
                        else //BUG: weird data, cannot find a increasing or decreasing 3 pts
                            break;

                        for (int k = 0; (k < filtered.Length); k++)
                        {
                            filteredData.Add(filtered[k]);
                            if (k>=512)
                                twf.WriteLine(filtered[k]);
                        }
                        #endregion Setup filtered window and apply filter

                        #region Compute the zero crossings of the 1st derivative
                        double[] derivative = Derivative(filtered);
                        ArrayList localPeaks = PeakCrossings(derivative);
                        for (int k = 0; (k < localPeaks.Count); k++)
                        {
                            int peakLocation = ((int)localPeaks[k]); //+ windowStartIndex;
                            peaks.Add(peakLocation);
                            peakValues.Add(filtered[((int)localPeaks[k])]);
                        }
                        #endregion Compute the zero crossings of the 1st derivative
                 
                        #region Suppress peaks not within a 0.2-5Hz frequency range 90Hz
                        // Suppress Peaks that are not within acceptable frequencies  5Hz (90/5 = 18),
                        // choose a single peak within 18 samples
                        ArrayList suppressed = new ArrayList();
                        ArrayList unsuppressed = new ArrayList();
                        for (int k = 1; (k < peaks.Count); k++)
                        {

                            if (Math.Abs(((int)peaks[k] - (int)peaks[k - 1])) <= 18)
                            {
                                if (((double)peakValues[k]) >= ((double)peakValues[k - 1]))
                                {
                                    suppressed.Add((int)peaks[k - 1]);
                                    unsuppressed.Add((int)peaks[k]);
                                    peakValues.RemoveAt(k - 1);
                                    peaks.RemoveAt(k - 1);

                                }
                                else
                                {
                                    suppressed.Add((int)peaks[k]);
                                    unsuppressed.Add((int)peaks[k - 1]);
                                    peakValues.RemoveAt(k);
                                    peaks.RemoveAt(k);
                                }
                                k = k - 1;
                            }

                        }
                        #endregion Suppress peaks not within a 0.2-5Hz frequency range 90Hz

                        #region Interpolate Suppressed Peaks            
                        // Interpolate between points for suppressed peaks
                        for (int k = 0; (k < suppressed.Count); k++)
                        {
                            int suppressedPeak = (int)suppressed[k];
                            int unsuppressedPeak = (int)unsuppressed[k];

                            if (suppressedPeak > unsuppressedPeak)
                            {
                                double slope = (double)filteredData[suppressedPeak] - (double)filteredData[unsuppressedPeak];
                                slope = slope / (suppressedPeak - unsuppressedPeak);

                                for (int r = unsuppressedPeak; (r < suppressedPeak); r++)
                                    filteredData[r] = (double)filteredData[unsuppressedPeak] + (r - unsuppressedPeak) * slope;

                            }
                            else
                            {
                                double slope = (double)filteredData[unsuppressedPeak] - (double)filteredData[suppressedPeak];
                                slope = slope / (unsuppressedPeak - suppressedPeak);

                                for (int r = suppressedPeak; (r < unsuppressedPeak); r++)
                                    filteredData[r] = (double)filteredData[suppressedPeak] + (r - suppressedPeak) * slope;
                            }
                        }
                        #endregion Interpolate Suppressed Peaks

                        #region Smoothen Signal using RM
                       ArrayList smoothened = new ArrayList();
                        for (int k = 7; (k < (filteredData.Count - 7)); k++)
                        {
                            double val = 0;
                            for (int r = 1; (r <= 7); r++)
                                val += (1 / 12.0) * ((double)filteredData[k - r] + (double)filteredData[k + r]);
                            smoothened.Add(val);
                        }
                        double[] smoothenedArray = new double[smoothened.Count];
                        for (int r = 0; (r < smoothened.Count); r++)
                            smoothenedArray[r] = (double)smoothened[r];
                    
                        #endregion Smoothen Signal using RM
                       
                        //After smoothening smoothenedArray has 7 pts removed from the beginning i.e. 
                        //start counting from 512-7 = 505
                        #region Compute peaks and troughs for 1st and 2nd derivatives
                        double[] dd = Derivative(smoothenedArray);
                        ArrayList ddPeaks = PeakCrossings(dd);
                        ArrayList ddTroughs = TroughCrossings(dd);
                        double[] dd2 = Derivative(dd);
                        ArrayList dd2Peaks = PeakCrossings(dd2);
                        ArrayList dd2Troughs = TroughCrossings(dd2);
                        #endregion Compute peaks and troughs for 1st and 2nd derivatives

                        #region Integrate and compute CV between consecutive peaks
                        // Compute also dist between a peak and its previous trough
                        // Correct the signal using running mean
                        ArrayList correctedArray = new ArrayList();
                        ArrayList integratedArray = new ArrayList();
                        ArrayList cvArray = new ArrayList();
                        ArrayList distpeaktrough = new ArrayList();
                        for (int k = 1; (k < ddPeaks.Count); k++)
                        {
                            int startPeak = (int)ddPeaks[k - 1];
                            int endPeak = (int)ddPeaks[k];
                            double rmean = 0.0;

                            //Compute vertical distance between a peak and a trough
                            if (((int)ddTroughs[k - 1]) < ((int)ddPeaks[k - 1]))
                            {
                                double diff = (double)smoothenedArray[startPeak] - (double)smoothenedArray[(int)ddTroughs[k - 1]];
                                distpeaktrough.Add(diff);
                            }
                            else if ((k != 1) && (((int)ddTroughs[k - 2]) < ((int)ddPeaks[k - 1])))
                            {
                                double diff = (double)smoothenedArray[startPeak] - (double)smoothenedArray[(int)ddTroughs[k - 2]];
                                distpeaktrough.Add(diff);
                            }
                            else
                                distpeaktrough.Add(0.0);


                            // Compute running mean between consecutive peaks
                            for (int r = startPeak; (r < endPeak); r++)
                                rmean += (double)smoothenedArray[r];
                            rmean = rmean / (endPeak - startPeak);

                            //integrate between consecutive peaks and compute CV
                            double integration = 0.0;
                            double sd = 0.0;
                            for (int r = startPeak; (r < endPeak); r++)
                            {
                                correctedArray.Add((double)smoothenedArray[r] - rmean);
                                integration += Math.Abs((double)smoothenedArray[r] - rmean);
                                sd += Math.Pow((double)smoothenedArray[r] - rmean, 2.0);
                            }
                            sd = Math.Sqrt(sd / (endPeak - startPeak));
                            cvArray.Add(sd / rmean);
                            integratedArray.Add(integration);
                        }

                        #endregion Integrate and compute CV between consecutive peaks

                        #region Count Peaks
                        ArrayList pairwisePeaks = new ArrayList();
                        ArrayList countedPeaks = new ArrayList();
                        double prevDPeakTrough = 0.0;
                        for (int k = 1; (k < ddPeaks.Count); k++)
                        {
                            //Count peaks with AUC above 500
                            // Count peaks with CV higher than 0.02
                            if (((double)integratedArray[k - 1] > 500) &&
                                (Math.Abs((double)cvArray[k - 1]) > 0.02))
                            {
                                //Peaks need to be within reasonable distnace 
                                if (((int)ddPeaks[k] - (int)ddPeaks[k - 1]) < (90 * 3))
                                {
                                    int startPeak = k - 3;
                                    if (startPeak < 0)
                                        startPeak = 0;
                                    int endPeak = k + 3;
                                    if (endPeak > (ddPeaks.Count - 1))
                                        endPeak = ddPeaks.Count - 1;

                                    //Check the 3 previous and 3 following peaks
                                    for (int r = startPeak; (r <= endPeak); r++)
                                    {
                                        if (r != k)
                                        {
                                            int peak1 = (int)ddPeaks[r];
                                            int peak2 = (int)ddPeaks[k];
                                            double percent = Math.Abs(smoothenedArray[peak1]) - Math.Abs(smoothenedArray[peak2]);
                                            percent = percent / Math.Max(Math.Abs(smoothenedArray[peak1]), Math.Abs(smoothenedArray[peak2]));

                                            //if any of the 3 previous and next 3 peaks are within 10% difference
                                            //then potentially count this peak
                                            if (percent < 0.1)
                                            {
                                                int peak = (int)ddPeaks[k];
                                                if (k < ddTroughs.Count)
                                                {
                                                    //Compute distance with previous trough
                                                    int trough = (int)ddTroughs[k];
                                                    double curDPeakTrough = 0.0;
                                                    if ((int)ddTroughs[k] < peak)
                                                        curDPeakTrough = Math.Abs(smoothenedArray[peak] - smoothenedArray[trough]);
                                                    else if (k > 0)
                                                    {
                                                        trough = (int)ddTroughs[k - 1];
                                                        curDPeakTrough = Math.Abs(smoothenedArray[peak] - smoothenedArray[trough]);
                                                    }
                                                    
                                                    //if the cur trough vs prev trough is within 30% then count it, else elimiate it
                                                    if (peak2 >= 505)
                                                    {
                                                        if ((prevDPeakTrough > 0) && (curDPeakTrough > 10) && ((curDPeakTrough / prevDPeakTrough) > 0.30))
                                                            countedPeaks.Add((int)peak2);
                                                        else
                                                            pairwisePeaks.Add((int)peak2);
                                                    }
                                                    prevDPeakTrough = curDPeakTrough;
                                                }

                                                break;
                                            }
                                        }

                                    }

                                }
                            }
                        }
                        totalPeaks += countedPeaks.Count;
                        #endregion Count Peaks

                        #region Output CSV Files
                        twcp.WriteLine(totalPeaks);
                        int peakIndex = 0;
                        int troughIndex = 0;
                        int integrationIndex = 0;
                        int pairwiseIndex = 0;
                        int countedIndex = 0;
                        if (ddPeaks != null)
                        {
                            for (int k = 0; (k < ddPeaks.Count); k++)
                            {
                                if (((int)ddPeaks[k]) > 505)
                                    break;
                                else
                                    peakIndex++;
                            }
                        }
                        if (ddTroughs != null)
                        {
                            for (int k = 0; (k < ddTroughs.Count); k++)
                            {
                                if (((int)ddTroughs[k]) > 505)
                                    break;
                                else
                                    troughIndex++;
                            }
                        }

                        if (countedPeaks != null)
                        {
                            for (int k = 0; (k < countedPeaks.Count); k++)
                            {
                                if (((int)countedPeaks[k]) > 505)
                                    break;
                                else
                                    countedIndex++;
                            }
                        }
                        integrationIndex = peakIndex;
                        
                           
                        for (int k = 505; (k < smoothened.Count); k++)
                        {
                            string peakString = "";
                            if ((peakIndex < ddPeaks.Count) && (k == (int)ddPeaks[peakIndex]))
                            {
                                peakString = ",1000";
                                if ((integrationIndex < ddPeaks.Count - 1))
                                {
                                    peakString += "," + (double)integratedArray[integrationIndex];
                                    peakString += "," + (double)cvArray[integrationIndex];
                                    peakString += "," + ((int)ddPeaks[peakIndex + 1] - (int)ddPeaks[peakIndex]);
                                    peakString += "," + (double)distpeaktrough[integrationIndex];
                                    integrationIndex++;
                                }
                                else
                                    peakString += ",0,0,0,0";

                                peakIndex++;
                            }
                            else
                                peakString = ",-1000,0,0,0,0";

                            if ((troughIndex < ddTroughs.Count) && (k == (int)ddTroughs[troughIndex]))
                            {
                                peakString += ",1000";
                                troughIndex++;
                            }
                            else
                                peakString += ",-1000";

                            if ((pairwiseIndex < pairwisePeaks.Count) && (k == (int)pairwisePeaks[pairwiseIndex]))
                            {
                                peakString += ",1000";
                                pairwiseIndex++;
                            }
                            else
                                peakString += ",-1000";

                            if ((countedIndex < countedPeaks.Count) && (k == (int)countedPeaks[countedIndex]))
                            {
                                peakString += ",1000";
                                countedIndex++;
                            }
                            else
                                peakString += ",-1000";


                            twss.WriteLine((double)smoothened[k] + peakString);

                        }

                        for (int k = 0; (k < filteredData.Count); k++)
                        {
                            tws.WriteLine((double)filteredData[k]);
                        }
                        for (int k = 0; (k < peaks.Count); k++)
                        {
                            twp.WriteLine((int)peaks[k] + "," + (double)peakValues[k]);
                        }

                        for (int k = 0; (k < correctedArray.Count); k++)
                            twc.WriteLine(correctedArray[k]);
                        #endregion Output CSV Files

                        #region Iteration Updates
                        windowStartIndex += end + 1;               
                        peaks = new ArrayList();
                        peakValues = new ArrayList();

                        //Copy the last 512 elements into the begining of the array
                        for (int k = 0; (k < 512); k++)
                            window[k] = window[1024+k];             

                        if (line == null)
                            break;

                        #endregion Iteration Updates

                    }
                    else
                        window[index++] = magnitude;
                    
                    tw.WriteLine(time + "," + magnitude);
                }


                previous = Double.MinValue;
              
                twc.Close();
                twss.Close();
                tws.Close();
                twp.Close();
                twt.Close();
                tw.Close();
                twf.Close();
                twi.Close();
                twcp.Close();
            }
        }
    }
}
