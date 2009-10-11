using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.IO;
using Wockets;
using WocketsWeka;
using Wockets.Utils;
using Wockets.Data.Classifiers;
using Wockets.Data.Classifiers.Utils;
using Wockets.Data.Classifiers.Trees;
using Wockets.Data.Annotation;

using weka.core;
using weka.classifiers;
using weka.classifiers.trees;
using WocketsWeka.Utils;

namespace PCTestApplication
{
    class Program
    {
        static void Main(string[] args)
        {

            string storage = @"C:\Users\albinali\Desktop\Session10-11-1-12-7\wockets\";
            WocketsController wc = new WocketsController("", "", "");
            wc.FromXML(storage+"SensorData.xml");
            int[] lostSeconds = new int[wc._Sensors.Count];
            double[] prevUnix = new double[wc._Sensors.Count];
            int i=0;
            int prev_seq=-1;
            for ( i= 0; (i < wc._Sensors.Count); i++)
            {
                double firstT = 0, lastT = 0;
                int count = 0;
                wc._Sensors[i]._RootStorageDirectory = storage + "data\\raw\\PLFormat\\";
                TextWriter tw = new StreamWriter(storage + "sensor" + wc._Sensors[i]._ID + ".csv");
                TextWriter twp = new StreamWriter(storage + "sensorloss" + wc._Sensors[i]._ID + ".csv");
                double totalLoss = 0;
                try
                {
                    int lastDecodedIndex = 0;
                    while (wc._Sensors[i].Load())
                    {
                        if (wc._Sensors[i]._Decoder._Head == 0)
                            lastDecodedIndex = wc._Sensors[i]._Decoder._Data.Length - 1;
                        else
                            lastDecodedIndex = wc._Sensors[i]._Decoder._Head - 1;
                        count++;


                        Wockets.Data.Accelerometers.AccelerationData data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[lastDecodedIndex];
                        if (firstT == 0)
                            firstT = data.UnixTimeStamp;

                        if ((lastT>1000) && ((data.UnixTimeStamp- lastT) > 1000))
                            totalLoss += (data.UnixTimeStamp-lastT);

                        lastT = data.UnixTimeStamp;
                        /*int seq= ((data.X&0xff) | ((data.Y<<8)));
                        if (prev_seq >= 0)
                        {
                            if ((prev_seq + 1) != seq)
                                twp.WriteLine(data.UnixTimeStamp + "," + seq);
                        }*/

                       

                        //tw.WriteLine(data.UnixTimeStamp + "," + data.X + "," + data.Y + "," + data.Z+","+seq);
                        tw.WriteLine(data.UnixTimeStamp + "," + data.X + "," + data.Y + "," + data.Z);
                        //prev_seq=seq;
                        if ((prevUnix[i] > 1000) && ((data.UnixTimeStamp - prevUnix[i]) > 60000))
                            lostSeconds[i] += (int)((data.UnixTimeStamp - prevUnix[i]) / 1000.0);

                        prevUnix[i] = data.UnixTimeStamp;

                    }
                }
                catch (Exception)
                {
                }
                double sr = count;
                double timer = (lastT - firstT) / 1000.0;
                sr = sr / timer;
                //tw.WriteLine("SR: " + sr);
                //tw.WriteLine("lost " + lostSeconds[i]);
                tw.Flush();
                tw.Close();
                twp.Flush();
                twp.WriteLine("Total Loss in seconds " + totalLoss/1000 + " in mins" + totalLoss / 60000);
                twp.Close();
            }

            Environment.Exit(0);
            TextReader[] trs = new StreamReader[wc._Sensors.Count];
            Hashtable[] sensordata = new Hashtable[wc._Sensors.Count];
            string[] sensorlines = new string[wc._Sensors.Count];
            double[] lastTS=new double[wc._Sensors.Count];
            bool[] processed=new bool[wc._Sensors.Count];
            bool[] done=new bool[wc._Sensors.Count];
            int[] indexes=new int[wc._Sensors.Count];
            CubicSpline[][] csplines = new CubicSpline[wc._Sensors.Count][];

            i=0;
            long currentTS=9999999999999999;
            
            for (i = 0; (i < wc._Sensors.Count); i++)
            {
                trs[i] = new StreamReader(storage + "sensor" + i + ".csv");
                sensordata[i] = new Hashtable();
                processed[i]=true;
                done[i]=false;
                
                sensorlines[i]=trs[i].ReadLine();
                string[] tokens=sensorlines[i].Split(',');                
                lastTS[i]=Convert.ToDouble(tokens[0])/1000.0;  
                indexes[i]=0;
                if (lastTS[i] < currentTS)
                    currentTS= (long)lastTS[i];

            }
            
            bool Alldone=true;
            bool AllProcessed = false;
            TextWriter merged = new StreamWriter(storage + "merged.csv");
            do
            {

                for (i = 0; (i < wc._Sensors.Count); i++)
                {
                    if ((done[i]==false) && (processed[i]))
                    {
                        sensorlines[i] = trs[i].ReadLine();
                        if (sensorlines[i] == null)
                            done[i] = true;
                    }


                    if (done[i] == false)
                    {
                        string[] tokens = sensorlines[i].Split(',');
                        long ts = (long)(Convert.ToDouble(tokens[0]) / 1000.0);
                        if (currentTS != ts)
                        {
                            if (processed[i] == true)
                            {
                                //stop reading
                                processed[i] = false;

                                //correct timestamps                             
                                int count = sensordata[i].Count;
                                double delta = 1000.0 / count;
                                for (int j=0;(j<indexes[i]);j++)
                                {
                                    string vals = (string)sensordata[i][j];
                                    sensordata[i].Remove(j);
                                    long ctime=(long)((currentTS * 1000.0) + j * delta);
                                    sensordata[i].Add(ctime, vals);
                                }
                            }

                        }
                        else
                        {
                            sensordata[i].Add(indexes[i], tokens[1] + "," + tokens[2] + "," + tokens[3]);
                            indexes[i] = indexes[i] + 1;
                        }
                    }
                }

                AllProcessed = false;
                Alldone = true;
                for (i = 0; (i < wc._Sensors.Count); i++)
                {
                    if (done[i] == false)
                        Alldone = false;
                    if ((done[i]==false) && (processed[i] == true))
                        AllProcessed = true;
                }

                if (AllProcessed==false)
                {
                    //go by milliseconds
                 
                    double start_time = currentTS * 1000.0;

                    double[][] xs = new double[wc._Sensors.Count][];
                    double[][] ys1 = new double[wc._Sensors.Count][];
                    double[][] ys2 = new double[wc._Sensors.Count][];
                    double[][] ys3 = new double[wc._Sensors.Count][];
                    int[] ccounter=new int[wc._Sensors.Count];

                    for (int j=0;(j<wc._Sensors.Count);j++)
                    {
                        xs[j] = new double[sensordata[j].Count];
                        ys1[j] = new double[sensordata[j].Count];
                        ys2[j] = new double[sensordata[j].Count];
                        ys3[j] = new double[sensordata[j].Count];
                        //ccounter[j]=new int[sensordata[j].Count];
                        for (int k = 0; (k < sensordata[j].Count); k++)
                        {
                            xs[j][k] = 0;
                            ys1[j][k] = 0;
                            ys2[j][k] = 0;
                            ys3[j][k] = 0;
                            ccounter[j] = 0;
                        }
                    }
                    for (int t = 0; (t < 1000); t++)                    
                    {                       
                        long currentTT=((long)(start_time+t));
                        string output = currentTT.ToString();
                        bool found = false;                                                
                        for (int j = 0; (j < wc._Sensors.Count); j++)
                        {                            
                            if (sensordata[j].ContainsKey(currentTT))
                            {
                                string[] tokens2=((string)sensordata[j][currentTT]).Split(',');
                                xs[j][ccounter[j]] = currentTT - (long)start_time;
                                ys1[j][ccounter[j]] = (double)Convert.ToInt32(tokens2[0]);
                                ys2[j][ccounter[j]] = (double)Convert.ToInt32(tokens2[1]);
                                ys3[j][ccounter[j]] = (double)Convert.ToInt32(tokens2[2]);
                                ccounter[j] = ccounter[j] + 1;
                            }
                            
                            /*if (sensordata[j].ContainsKey(currentTT))
                            {
                                output += "," + (string)sensordata[j][currentTT];
                               found = true;
                            }
                            else
                                output += ",,,";
                             */
                        }
                        //if (found)
                        //merged.WriteLine(output);
                    }
                    
                    for (int j = 0; (j < wc._Sensors.Count); j++)
                    {
                        csplines[j] = new CubicSpline[3];
                        if (xs[j].Length > 10)
                        {
                            csplines[j][0] = new CubicSpline(xs[j], ys1[j]);
                            csplines[j][1] = new CubicSpline(xs[j], ys2[j]);
                            csplines[j][2] = new CubicSpline(xs[j], ys3[j]);
                        }
                    }

                    for (int t = 0; (t < 1000); )
                    {
                        long currentTT = ((long)(start_time + t));
                        string output = currentTT.ToString();
//                        bool found = false;

                        for (int j = 0; (j < wc._Sensors.Count); j++)
                        {
                            //if (sensordata[j].ContainsKey(currentTT))
                            //{

                            if (csplines[j][0] != null)
                            {
                                double xx = csplines[j][0].interpolate(t);
                                double yy=csplines[j][1].interpolate(t);
                                double zz=csplines[j][2].interpolate(t);
                                output += "," + xx +","+yy+","+zz;
                            }else
                                output += ",,,";

 //                               found = true;
                            //}
     //                       else
   //                             output += ",,,";
                        }

                        merged.WriteLine(output);
                        t += 11;
                    }
                    

                    Console.WriteLine("Processing " + currentTS);
                    currentTS += 1;
                    for (i = 0; (i < wc._Sensors.Count); i++)
                    {
                        if (done[i] == false)
                        {
                            sensordata[i] = new Hashtable();
                            processed[i] = true;
                            indexes[i] = 0;
                            //add last read data point
                            string[] tokens = sensorlines[i].Split(',');
                            long ts = (long)(Convert.ToDouble(tokens[0]) / 1000.0);
                            if (currentTS == ts)
                            {
                                sensordata[i].Add(indexes[i], tokens[1] + "," + tokens[2] + "," + tokens[3]);
                                indexes[i] = indexes[i] + 1;
                            }
                        }

                    }
                    AllProcessed = true;
                   
                }
                
            } while (Alldone == false);

            merged.Close();
                

            

            /*
            Classifier classifier;
            FastVector fvWekaAttributes;
            Instances instances;
            string[] activityLabels;
            Hashtable labelIndex;
            int[] labelCounters;

            string storage = @"C:\Users\albinali\Desktop\data\mites data\wockets\";
            WocketsController wc = new WocketsController("", "", "");
            wc.FromXML(storage + "SensorData.xml");
            int[] lostSeconds = new int[wc._Sensors.Count];
            double[] prevUnix = new double[wc._Sensors.Count];
            bool isAllDone = false;


            Session annotatedSession = new Session(); 
            DTConfiguration classifierConfiguration = new DTConfiguration();

            try
            {
                annotatedSession.FromXML(storage + "\\ActivityLabelsRealtime.xml");
            }
            catch (Exception e)
            {
            }


            try
            {
                classifierConfiguration.FromXML(storage + "\\Configuration.xml");
            }
            catch (Exception e)
            {
            }



            FeatureExtractor.Initialize(wc, classifierConfiguration, annotatedSession.OverlappingActivityLists[0]);

            labelIndex = new Hashtable();


            classifier = new J48();
            if (!File.Exists(storage + "\\model.xml"))
            {
                string[] arffFiles = Directory.GetFileSystemEntries(storage, "output*.arff");
                if (arffFiles.Length != 1)
                    throw new Exception("Multiple Arff Files in Directory");
                instances = new Instances(new StreamReader(arffFiles[0]));
                instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                classifier.buildClassifier(instances);
                TextWriter tc = new StreamWriter(storage + "\\model.xml");
                classifier.toXML(tc);
                tc.Flush();
                tc.Close();
            }
            else
            {
                instances = new Instances(new StreamReader(storage + "\\structure.arff"));
                instances.Class = instances.attribute(FeatureExtractor.ArffAttributeLabels.Length);
                classifier.buildClassifier(storage + "\\model.xml", instances);
            }


            fvWekaAttributes = new FastVector(FeatureExtractor.ArffAttributeLabels.Length + 1);
            for (int i = 0; (i < FeatureExtractor.ArffAttributeLabels.Length); i++)
                fvWekaAttributes.addElement(new weka.core.Attribute(FeatureExtractor.ArffAttributeLabels[i]));

            FastVector fvClassVal = new FastVector();
            labelCounters = new int[annotatedSession.OverlappingActivityLists[0].Count + 1];
            activityLabels = new string[annotatedSession.OverlappingActivityLists[0].Count + 1];
            for (int i = 0; (i < annotatedSession.OverlappingActivityLists[0].Count); i++)
            {
                labelCounters[i] = 0;
                string label = "";
                int j = 0;
                for (j = 0; (j < annotatedSession.OverlappingActivityLists.Count - 1); j++)
                    label += annotatedSession.OverlappingActivityLists[j][i]._Name.Replace(' ', '_') + "_";
                label += annotatedSession.OverlappingActivityLists[j][i]._Name.Replace(' ', '_');
                activityLabels[i] = label;
                labelIndex.Add(label, i);
                fvClassVal.addElement(label);
            }



            weka.core.Attribute ClassAttribute = new weka.core.Attribute("activity", fvClassVal);

            int[] lastDecodedIndex = new int[wc._Sensors.Count];
            double[] lastDecodedTime = new double[wc._Sensors.Count];
            bool[] isDone = new bool[wc._Sensors.Count];
            int nextSensor = 0;
            double smallestTimestamp = 0;
            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                wc._Sensors[i]._RootStorageDirectory = storage + "data\\raw\\PLFormat\\";
                isDone[i] = false;
                lastDecodedTime[i] = 0;
                lastDecodedIndex[i] = 0;
            }
            //double lastTimeStamp=0;
            Wockets.Data.Accelerometers.AccelerationData data = null;
            string previousActivity = "";
            Annotation annotation = null;
            int classificationCounter = 0;
            string mostActivity = "";
            while (isAllDone == false)
            {
                isAllDone = true;
                for (int i = 0; (i < wc._Sensors.Count); i++)
                {

                    if (nextSensor == i)
                    {
                        if (wc._Sensors[i].Load())
                        {
                            if (wc._Sensors[i]._Decoder._Head == 0)
                                lastDecodedIndex[i] = wc._Sensors[i]._Decoder._Data.Length - 1;
                            else
                                lastDecodedIndex[i] = wc._Sensors[i]._Decoder._Head - 1;
                            data = (Wockets.Data.Accelerometers.AccelerationData)wc._Sensors[i]._Decoder._Data[lastDecodedIndex[i]];
                            lastDecodedTime[i] = data.UnixTimeStamp;

                            isAllDone = false;


                            double lastTT = FeatureExtractor.StoreWocketsWindow();

                            if (FeatureExtractor.GenerateFeatureVector(lastTT))
                            {
                                Instance newinstance = new Instance(instances.numAttributes());
                                newinstance.Dataset = instances;
                                for (int k = 0; (k < FeatureExtractor.Features.Length); k++)
                                    newinstance.setValue(instances.attribute(k), FeatureExtractor.Features[k]);
                                double predicted = classifier.classifyInstance(newinstance);
                                string predicted_activity = newinstance.dataset().classAttribute().value_Renamed((int)predicted);
                                int currentIndex = (int)labelIndex[predicted_activity];
                                labelCounters[currentIndex] = (int)labelCounters[currentIndex] + 1;
                                classificationCounter++;

                                if (classificationCounter == classifierConfiguration._SmoothWindows)
                                {
                                    classificationCounter = 0;
                                    int mostCount = 0;
                                    for (int j = 0; (j < labelCounters.Length); j++)
                                    {                     
                                        if (labelCounters[j] > mostCount)
                                        {
                                            mostActivity = activityLabels[j];
                                            mostCount = labelCounters[j];

                                        }
                                        labelCounters[j] = 0;
                                    }


                                    if (mostCount == classifierConfiguration._SmoothWindows)
                                    {
                                        DateTime mydate = new DateTime();
                                        if (previousActivity == "")
                                        {
                                            annotation = new Annotation();
                                            annotation._StartUnix = data.UnixTimeStamp;                                            
                                            WocketsTimer.GetDateTime((long)(data.UnixTimeStamp),out mydate);
                                            annotation._StartDate = mydate.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                                            annotation._StartHour = mydate.Hour;
                                            annotation._StartMinute = mydate.Minute;
                                            annotation._StartSecond = mydate.Second;                                           
                                            annotation.Activities.Add(new Activity(mostActivity, "Physical Activiites"));
                                        }
                                        else if (previousActivity != mostActivity)
                                        {
                                            annotation._EndUnix = data.UnixTimeStamp;
                                            WocketsTimer.GetDateTime((long)(data.UnixTimeStamp), out mydate);
                                            annotation._EndDate = mydate.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                                            annotation._EndHour = mydate.Hour;
                                            annotation._EndMinute = mydate.Minute;
                                            annotation._EndSecond = mydate.Second;
                                           
                                            annotatedSession.Annotations.Add(annotation);

                                            annotation = new Annotation();
                                            annotation._StartUnix = data.UnixTimeStamp;
                                            WocketsTimer.GetDateTime((long)(data.UnixTimeStamp), out mydate);
                                            annotation._StartDate = mydate.ToString("yyyy'-'MM'-'dd' 'HH':'mm':'ssK");
                                            annotation._StartHour = mydate.Hour;
                                            annotation._StartMinute = mydate.Minute;
                                            annotation._StartSecond = mydate.Second;
                                           
                                            annotation.Activities.Add(new Activity(mostActivity, "Physical Activiites"));
                                        }

                                        previousActivity = mostActivity;
                                    }
                                   
                                }
                   

                              
                            }
                        }
                    }

                    nextSensor = 0;
                    smallestTimestamp = lastDecodedTime[0];
                    for (int j = 0; (j < wc._Sensors.Count); j++)
                    {
                        if (smallestTimestamp > lastDecodedTime[j])
                        {
                            smallestTimestamp = lastDecodedTime[j];
                            nextSensor = j;
                        }
                    }

                }
            }




            TextWriter tw = new StreamWriter(storage + "\\AnnotationIntervals.xml");
            tw.WriteLine(annotatedSession.ToXML());
            tw.Close();
            tw = new StreamWriter(storage + "\\AnnotationIntervals.CSV");
            tw.WriteLine(annotatedSession.ToCSV());
            tw.Close();
             * 
             *  * 
             * */
        }

    }
}
