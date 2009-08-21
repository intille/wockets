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

namespace PCTestApplication
{
    class Program
    {
        static void Main(string[] args)
        {

            string storage = @"C:\Users\albinali\Desktop\Session8-20-18-51-12\";
            WocketsController wc = new WocketsController("", "", "");
            wc.FromXML(storage+"SensorData.xml");
            int[] lostSeconds = new int[wc._Sensors.Count];
            double[] prevUnix = new double[wc._Sensors.Count];

            for (int i = 0; (i < wc._Sensors.Count); i++)
            {
                double firstT = 0, lastT = 0;
                int count = 0;
                wc._Sensors[i]._RootStorageDirectory = storage + "data\\raw\\PLFormat\\";
                TextWriter tw = new StreamWriter(storage + "sensor" + wc._Sensors[i]._ID + ".csv");
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
                        lastT = data.UnixTimeStamp;
                        tw.WriteLine(data.UnixTimeStamp + "," + data.X + "," + data.Y + "," + data.Z);

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
                tw.WriteLine("SR: " + sr);
                tw.WriteLine("lost " + lostSeconds[i]);
                tw.Flush();
                tw.Close();
            }

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
