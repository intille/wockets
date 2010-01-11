using System;
using System.Collections.Generic;
using System.Text;
using WocketsWeka;
using System.IO;
using weka.core;
using weka.classifiers;
using weka.classifiers.trees;
using weka.filters;
using weka.filters.unsupervised.instance;
using weka.filters.unsupervised.attribute;
using weka.classifiers.evaluation;
using weka.attributeSelection;
using AXML;
using System.Collections;
using Wockets.Data.Annotation;
using Wockets;
using Wockets.Utils;
using Wockets.Data.Classifiers.Trees;
using Wockets.Data.Classifiers.Utils;
using System.Text.RegularExpressions;

namespace MITesAnalysisApplication
{
    class Program
    {

        static void GenerateTrainingCSVFiles()
        {

            string destination = @"C:\DataAnalysis\Stanford-Analysis\";
            if (Directory.Exists(destination))
            {
                for (int id = 15; (id <= 15); id++)
                {
                    destination = @"C:\DataAnalysis\Stanford-Analysis\";
                    string storage = @"C:\DataAnalysis\Stanford-MITes\Subject" + id;
                    string[] subdirectories = Directory.GetDirectories(storage);


                    if (Directory.Exists(destination + "Subject" + id))
                        Directory.Delete(destination + "Subject" + id, true);


                    for (int i = 0; (i < subdirectories.Length); i++)
                    {
                        destination = @"C:\DataAnalysis\Stanford-Analysis\";
                        destination = destination + "Subject" + id;
                        storage = @"C:\DataAnalysis\Stanford-MITes\Subject" + id;
                        subdirectories[i] = subdirectories[i].Substring(subdirectories[i].LastIndexOf('\\') + 1);
                        destination = destination + "\\" + subdirectories[i];
                        string withunknownDirectory = destination + "\\withunknown";
                        string withoutunknownDirectory = destination + "\\withoutunknown";

                        Directory.CreateDirectory(withunknownDirectory);
                        Directory.CreateDirectory(withoutunknownDirectory);

                        //Generate the CSV and ARFF files
                        storage = storage + "\\" + subdirectories[i] + "\\mites";
                        try
                        {
                            string[] filter = new string[2];
                            filter[0] = "annotation";
                            filter[1] = "setup";
                            //Extractor.toARFFVanderbilt(storage, "..\\NeededFiles\\Master\\", 3, filter); 
                            Extractor.toARFFOxycon(storage, "..\\NeededFiles\\Master\\", 3, filter);
                            File.Move(storage + "\\data.arff", withunknownDirectory + "\\data.arff");





                            for (int dataoutputs = 0; (dataoutputs < 2); dataoutputs++)
                            {
                                Instances data = new Instances(new StreamReader(withunknownDirectory + "\\data.arff"));
                                data.ClassIndex = data.numAttributes() - 1;

                                if (data.numInstances() < 50)
                                {
                                    TextWriter twError = new StreamWriter(destination + "\\warning.txt");
                                    twError.WriteLine("Num instances too small" + data.numInstances());
                                    twError.Close();
                                    continue;
                                }
                                string currentDirectory = withunknownDirectory;


                                //Count the number of instances per class
                                int[] classCounter = new int[data.numClasses()];
                                for (int j = 0; (j < data.numClasses()); j++)
                                    classCounter[j] = 0;
                                for (int j = 0; (j < data.numInstances()); j++)
                                {
                                    int classValue = (int)data.instance(j).classValue();
                                    classCounter[classValue] = classCounter[classValue] + 1;
                                }

                                Instances filteredData = new Instances(new StreamReader(currentDirectory + "\\data.arff"));
                                filteredData.ClassIndex = filteredData.numAttributes() - 1;
                                for (int j = 0; (j < classCounter.Length); j++)
                                {
                                    //if we collected less than 60 instances per class filter it out
                                    if (classCounter[j] < 60)
                                    {

                                        RemoveWithValues removeValueFilter = new RemoveWithValues();
                                        removeValueFilter.set_AttributeIndex("last");
                                        removeValueFilter.set_InvertSelection(false);
                                        removeValueFilter.set_NominalIndices((j + 1).ToString());
                                        removeValueFilter.setInputFormat(filteredData);
                                        filteredData = Filter.useFilter(filteredData, removeValueFilter);
                                    }
                                }


                                //check if we are now generating arffs without unknown
                                if (dataoutputs == 1)
                                {
                                    currentDirectory = withoutunknownDirectory;
                                    RemoveWithValues removeUnknownFilter = new RemoveWithValues();
                                    removeUnknownFilter.set_AttributeIndex("last");
                                    removeUnknownFilter.set_InvertSelection(false);
                                    removeUnknownFilter.set_NominalIndices("1");
                                    removeUnknownFilter.setInputFormat(filteredData);
                                    filteredData = Filter.useFilter(filteredData, removeUnknownFilter);
                                }


                                //Balance Samples
                                weka.filters.supervised.instance.Resample resampler = new weka.filters.supervised.instance.Resample();
                                resampler.set_BiasToUniformClass(1.0);
                                resampler.set_RandomSeed(1);
                                resampler.set_SampleSizePercent(100.0);
                                resampler.setInputFormat(filteredData);
                                Instances balancedData = Filter.useFilter(filteredData, resampler);



                                //With Unknowns
                                //Write Filtered data with 60 or more instances

                                //unbalanced

                                filteredData.ToArff(currentDirectory + "\\FilteredUnbalancedData.arff");
                                filteredData.ToCSV(currentDirectory + "\\FilteredUnbalancedData.csv");



                                //balanced

                                balancedData.ToArff(currentDirectory + "\\FilteredBalancedData.arff");
                                balancedData.ToCSV(currentDirectory + "\\FilteredBalancedData.csv");


                                /*
                                //Randomize Filtered Unbalanced Data
                                Randomize randomizeFilter = new Randomize();
                                randomizeFilter.setInputFormat(filteredData);
                                Instances randomData = Filter.useFilter(filteredData, randomizeFilter);

                                //Generate 10 folds
                                
                                int numFolds = 10;
                                for (int k = 1; (k <= numFolds); k++)
                                {

                                    //extract training folds
                                    RemoveFolds trainingFoldsFilter = new RemoveFolds();
                                    trainingFoldsFilter.set_NumFolds(numFolds);
                                    trainingFoldsFilter.set_InvertSelection(true);
                                    trainingFoldsFilter.set_Fold(k);
                                    trainingFoldsFilter.inputFormat(randomData);
                                    Instances training = Filter.useFilter(randomData, trainingFoldsFilter);


                                    //balance training folds
                                    resampler = new weka.filters.supervised.instance.Resample();
                                    resampler.set_BiasToUniformClass(1.0); //balance the samples
                                    resampler.set_RandomSeed(1);
                                    resampler.set_SampleSizePercent(100.0);
                                    resampler.setInputFormat(training);
                                    training = Filter.useFilter(training, resampler);

                                    training.ToArff(currentDirectory + "\\Training" + k + ".arff");
                                    training.ToCSV(currentDirectory + "\\Training" + k + ".csv");


                                    //Output training and testing CSVs for each class independetly
                                    if (dataoutputs == 0)
                                    {

                                        //Generate a training file for each activity
                                        for (int p = 0; (p < training.classAttribute().numValues()); p++)
                                        {
                                            RemoveWithValues removeClassFilter = new RemoveWithValues();
                                            removeClassFilter.set_AttributeIndex("last");
                                            removeClassFilter.set_InvertSelection(true);
                                            //string sss = (p).ToString();
                                            //string act=training.classAttribute().value_Renamed(p + 1);
                                            int removeIndex = p + 1;
                                            string sss = removeIndex.ToString();                      
                                            removeClassFilter.set_NominalIndices(sss);
                                            removeClassFilter.setInputFormat(training);
                                            Instances classData = Filter.useFilter(training, removeClassFilter);

                                            classData.ToCSV(currentDirectory + "\\Training-"+k+"-" + training.attribute(training.classIndex()).value_Renamed(p).Replace(' ', '_').Replace('-', '_') + ".csv");
                                        }
                                    }
                                    

                                    //extract testing fold
                                    RemoveFolds testFoldsFilter = new RemoveFolds();
                                    testFoldsFilter.set_NumFolds(numFolds);
                                    testFoldsFilter.set_InvertSelection(false);
                                    testFoldsFilter.set_Fold(k);
                                    testFoldsFilter.inputFormat(randomData);
                                    Instances test = Filter.useFilter(randomData, testFoldsFilter);

                                    test.ToArff(currentDirectory + "\\Test" + k + ".arff");
                                    test.ToCSV(currentDirectory + "\\Test" + k + ".csv");

                                    if (dataoutputs == 0)
                                    {

                                        //Generate a training file for each activity
                                        for (int p = 0; (p < training.classAttribute().numValues()); p++)
                                        {
                                            RemoveWithValues removeClassFilter = new RemoveWithValues();
                                            removeClassFilter.set_AttributeIndex("last");
                                            removeClassFilter.set_InvertSelection(true);
                                            removeClassFilter.set_NominalIndices((p+1).ToString());
                                            removeClassFilter.setInputFormat(test);
                                            Instances classData = Filter.useFilter(test, removeClassFilter);

                                            classData.ToCSV(currentDirectory + "\\Test-" + k + "-" + test.attribute(test.classIndex()).value_Renamed(p).Replace(' ', '_').Replace('-', '_') + ".csv");
                                        }
                                    }
                                    

                            

                                }
                                 */


                            }

                            // File.Delete(withunknownDirectory + "\\data.arff");

                        }
                        catch (Exception e)
                        {
                            TextWriter twError = new StreamWriter(destination + "\\error.txt");
                            twError.WriteLine(e.Message);
                            twError.WriteLine(e.StackTrace);
                            twError.Close();
                        }
                    }

                }

            }
        }


        static void GenerateCrossValidationDecisionTrees()
        {
            string destination = @"C:\DataAnalysis\Stanford-Analysis\";
            string[] subdirectories = null;
            if (Directory.Exists(destination))
            {
                for (int id = 7; (id <= 7); id++)
                {
                    string storage = @"C:\DataAnalysis\Stanford-Analysis\Subject" + id;

                    if (!Directory.Exists(storage))
                        continue;
       
                    Instances training = null;
                    Instances structure = null;
                    int structureCount = 0;
                    Hashtable classes = new Hashtable();
                    
                    for (int id2 = 3; (id2 <= 25); id2++)
                    {
                        if (id != id2)
                        {
                            destination = @"C:\DataAnalysis\Stanford-Analysis\";
                            destination = destination + "Subject" + id2;
                            if (!Directory.Exists(destination))
                                continue;
                            subdirectories = Directory.GetDirectories(destination);
                            Console.WriteLine("Merging subject " + id + " and subject " + id2);
                            for (int i = 0; (i < subdirectories.Length); i++)
                            {

                                destination = @"C:\DataAnalysis\Stanford-Analysis\";
                                destination = destination + "Subject" + id2;
                                subdirectories[i] = subdirectories[i].Substring(subdirectories[i].LastIndexOf('\\') + 1);
                                destination = destination + "\\" + subdirectories[i];
                                string withunknownDirectory = destination + "\\withunknown";
                                string withoutunknownDirectory = destination + "\\withoutunknown";

                                if (training == null)
                                {
                                    training = new Instances(new StreamReader(withoutunknownDirectory + "\\FilteredBalancedData.arff"));
                                    structure = new Instances(new StreamReader(withoutunknownDirectory + "\\FilteredBalancedData.arff"));                                   
                                    training.Class = training.attribute(training.numAttributes() - 1);
                                    structure.Class = structure.attribute(structure.numAttributes() - 1);
                                    weka.core.Attribute classAttribute = training.attribute(training.numAttributes() - 1);
                                    int attributesLength = classAttribute.numValues();
                                    for (int j = 0; (j < attributesLength); j++)                                    
                                        classes.Add(classAttribute.value_Renamed(j), classAttribute.value_Renamed(j));                                    
                                }
                                else
                                {
                                    Instances addedSet = new Instances(new StreamReader(withoutunknownDirectory + "\\FilteredBalancedData.arff"));
                                    weka.core.Attribute classAttribute = addedSet.attribute(addedSet.numAttributes() - 1);
                                    int attributesLength = classAttribute.numValues();
                                    weka.core.Attribute trainingclassAttribute = training.attribute(training.numAttributes() - 1);
                                    for (int k = 0; (k < attributesLength); k++)
                                    {
                                        string classvalue=classAttribute.value_Renamed(k);
                                        if (!classes.ContainsKey(classvalue))
                                        {
                                            classes.Add(classvalue, classvalue);
                                            training.classAttribute().addStringValue(classvalue);
                                            structure.classAttribute().addStringValue(classvalue);
                                        }                                        
                                    }
                                    int numInstances = addedSet.numInstances();
                                    for (int j = 0; (j < numInstances); j++)
                                    {
                                        Instance currentInstance=addedSet.instance(j);
                                        if (training.checkInstance(currentInstance) == false)
                                            throw new Exception("Instance Problem");
                                        else
                                        {
                                            training.add(currentInstance);
                                            if (structureCount < 10)
                                            {
                                                structure.add(currentInstance);
                                                structureCount++;
                                            }
                                        }
                                    }
                                }
                                //data.classAttribute().numValues()
                            }
                        }
                    }

                    structure.ToArff(storage + "\\structure.arff");
                    training.ToCSV(storage + "\\training.csv");
                    
                    J48 classifier = new J48();
                    classifier.set_MinNumObj(30);
                    classifier.set_ConfidenceFactor((float)0.25);

                    TextWriter tw = new StreamWriter(storage + "\\tree-summary.csv");
                    if (File.Exists(storage + "\\subjectindependent-tree.xml"))                    
                        classifier.buildClassifier(storage + "\\subjectindependent-tree.xml", new Instances(new StreamReader(storage + "\\structure.arff")));                                                                  
                    else
                        classifier.buildClassifier(training);

                    tw.WriteLine("Tree Size," + classifier.measureTreeSize());
                    tw.WriteLine("Num Leaves," + classifier.measureNumLeaves());
                    tw.WriteLine("Num Rules," + classifier.measureNumRules()); 

                   
                    TextWriter dtw = new StreamWriter(storage+"\\subjectindependent-tree.xml");
                    classifier.toXML(dtw);
                    dtw.Close();

                   
                    
                    Instances test = null;//Set = new Instances(new StreamReader(storageWithoutunknownDirectory + "\\FilteredUnbalancedData.arff"));
                    subdirectories = Directory.GetDirectories(storage);
                    //classes = new Hashtable();
                    Hashtable testclassses=new Hashtable();
                    for (int i = 0; (i < subdirectories.Length); i++)
                    {
                        storage = @"C:\DataAnalysis\Stanford-Analysis\";
                        subdirectories[i] = subdirectories[i].Substring(subdirectories[i].LastIndexOf('\\') + 1);
                        storage = storage + "Subject" + id + "\\" + subdirectories[i];
                        
                        string storageWithunknownDirectory = storage + "\\withunknown";
                        string storageWithoutunknownDirectory = storage + "\\withoutunknown";

                        if (test == null)
                        {
                            test = new Instances(new StreamReader(storageWithoutunknownDirectory + "\\FilteredUnbalancedData.arff"));
                            test.Class = test.attribute(test.numAttributes() - 1);
                            weka.core.Attribute classAttribute = test.attribute(test.numAttributes() - 1);
                            //test.classAttribute().
                            int attributesLength = classAttribute.numValues();
                            for (int j = 0; (j < attributesLength); j++)
                                if (!testclassses.ContainsKey(classAttribute.value_Renamed(j)))
                                    testclassses.Add(classAttribute.value_Renamed(j), classAttribute.value_Renamed(j));
                        }
                        else
                        {
                            Instances addedSet = new Instances(new StreamReader(storageWithoutunknownDirectory + "\\FilteredUnbalancedData.arff"));
                            weka.core.Attribute classAttribute = addedSet.attribute(addedSet.numAttributes() - 1);
                            int attributesLength = classAttribute.numValues();

                            for (int k = 0; (k < attributesLength); k++)
                            {
                                string classvalue = classAttribute.value_Renamed(k);
                                if (!testclassses.ContainsKey(classvalue))
                                {
                                    testclassses.Add(classvalue, classvalue);
                                    test.classAttribute().addStringValue(classvalue);
                                }
                            }
                            int numInstances = addedSet.numInstances();
                            for (int j = 0; (j < numInstances); j++)
                            {
                                Instance currentInstance = addedSet.instance(j);
                                if (test.checkInstance(currentInstance) == false)
                                    throw new Exception("Instance Problem");
                                else
                                    test.add(currentInstance);
                            }
                        }
                        //data.classAttribute().numValues()
                    }


                    test.ToCSV(storage + "\\test.csv");


                    //test.Class = training.classAttribute();

                    //Evaluation e = new Evaluation(training);
                   // e.evaluateModel(classifier, test);
                    TextWriter outputFile = new StreamWriter(storage + "\\classification-subjectindependent.csv");
                    //int correct = 0;
                    int[][] confusion = new int[training.classAttribute().numValues()][];
                    Hashtable activityIndex=new Hashtable();
                    for (int z = 0; (z < training.classAttribute().numValues()); z++)
                    {
                        activityIndex.Add(training.attribute(training.numAttributes() - 1).value_Renamed(z),z);
                        confusion[z] = new int[training.classAttribute().numValues()];
                        for (int w = 0; (w < training.classAttribute().numValues()); w++)
                            confusion[z][w] = 0;
                    }
                    for (int z = 0; (z<test.numInstances()); z++)
                    {
                        Instance i = test.instance(z);
                        string ss = i.stringValue(test.numAttributes() - 1);

                        if (classes.ContainsKey(ss))
                        {
                            int result = (int)classifier.classifyInstance(i);
                            string outresult = training.classAttribute().value_Renamed(result) + "," + test.instance(z).stringValue(test.numAttributes() - 1);
                            int predictedIndex = (int)activityIndex[training.classAttribute().value_Renamed(result)];

                            int actualIndex = (int)activityIndex[ss];
                            confusion[actualIndex][predictedIndex] = confusion[actualIndex][predictedIndex] + 1;
                            outputFile.WriteLine(outresult);
                        }
                    }
              
                    //outputFile.WriteLine(e.toSummaryString());
                    outputFile.Close();
                    tw.Close();

                    tw = new StreamWriter(storage + "\\confusion.csv");
                    for (int w = 0; (w < training.classAttribute().numValues()); w++)
                    {
                        tw.Write(training.classAttribute().value_Renamed(w));
                        if (w < (training.classAttribute().numValues() - 1))
                            tw.Write(",");
                    }
                    tw.WriteLine();
                    for (int z = 0; (z < confusion.Length); z++)
                    {
                        for (int w = 0; (w < confusion[z].Length); w++)
                        {
                            tw.Write(confusion[z][w]);
                            if (w < confusion[z].Length - 1)
                                tw.Write(",");
                        }
                        tw.WriteLine();
                    }
                    tw.Close();
                    //double precetnage = (correct * 100.0) / test.numInstances();

                    Console.WriteLine("Training instacnces for subject " + id + " is " + training.numInstances());
                }
            }
        }


        static void GenerateArff()
        {
            Classifier classifier;
            FastVector fvWekaAttributes;
            Instances instances;
            string[] activityLabels;
            Hashtable labelIndex;
            int[] labelCounters;

            string storage = @"C:\Users\albinali\Desktop\wockets-Groden-12-11\InClassAfternoon130-220\naive\Session12-11-13-42-51\wockets\";
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

            TextWriter tw = new StreamWriter(storage + "\\output.arff");
            tw.WriteLine("@RELATION wockets");
            tw.WriteLine(FeatureExtractor.GetArffHeader());
            tw.Write("@ATTRIBUTE activity {unknown");
            for (int i = 0; (i < annotatedSession.OverlappingActivityLists[0].Count); i++)
                tw.Write("," + Regex.Replace(annotatedSession.OverlappingActivityLists[0][i]._Name, "[-]+", "_"));
            tw.WriteLine("}");
            tw.WriteLine("@DATA");
            //"flapping,rocking,flaprock}\n");

            labelIndex = new Hashtable();
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
            Wockets.Data.Annotation.Annotation annotation = null;
            int classificationCounter = 0;
            string realtime_activity = "unknown";
            int realtimeIndex = 0;
            
            Session session=new Session();
            session.FromXML(storage+"AnnotationIntervals.xml");
            Wockets.Data.Annotation.Annotation realtimeRecord = session.Annotations[0];
            realtimeRecord._StartUnix += 5000;
            realtimeRecord._EndUnix -= 5000;
            //AXML.AnnotatedRecord realtimeRecord = ((AXML.AnnotatedRecord)realtimeAnnotation.Data[realtimeIndex]);

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


                            double lastTimeStamp = FeatureExtractor.StoreWocketsWindow();

                            if (smallestTimestamp > realtimeRecord._EndUnix)
                            {
                                realtime_activity = "unknown";
                                realtimeIndex++;
                                if (realtimeIndex < session.Annotations.Count)
                                {
                                    realtimeRecord = session.Annotations[realtimeIndex];
                                    realtimeRecord._StartUnix += 5000;
                                    realtimeRecord._EndUnix -= 5000;
                                }
                            }

                            if ((lastTimeStamp >= realtimeRecord._StartUnix) &&
                                (lastTimeStamp <= realtimeRecord._EndUnix) && realtime_activity.Equals("unknown"))
                            {
                                realtime_activity = realtimeRecord.Activities._CurrentActivity;
                                realtime_activity = realtime_activity.Replace("none", "").Replace('-', '_').Replace(':', '_').Replace('%', '_').Replace('/', '_');
                                realtime_activity = Regex.Replace(realtime_activity, "[_]+", "_");
                                realtime_activity = Regex.Replace(realtime_activity, "^[_]+", "");
                                realtime_activity = Regex.Replace(realtime_activity, "[_]+$", "");
                            }
                            else if (lastTimeStamp > realtimeRecord._EndUnix)
                                realtime_activity = "unknown";

                            if (FeatureExtractor.GenerateFeatureVector(lastTimeStamp))
                            {
                                string arffSample = FeatureExtractor.toString() ;
                                tw.WriteLine(arffSample + "," + realtime_activity);
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



            tw.Close();

        }
        static void GenerateInterRateReliability()
        {
            string root = @"C:\Users\albinali\Desktop\wockets-Groden-12-11\InLabMorning1100-1132\";
            string file1 = root + @"expert\Session12-11-10-37-13";
            string file2 = root + @"naive\Session12-11-10-57-59\wockets";
            file1 += "\\AnnotationIntervals.xml";
            file2 += "\\AnnotationIntervals.xml";
            int totalCount = 0;
            int boundaryCount = 0;
            int delayedCount = 0;
            double delayedAverage = 0;
            bool agreeing = false;
            int missedCount = 0;
            bool a1Changed=false;
            double offsetDelay=0;
            int offsetCount=0;

            Session session1 = new Session();
            Session session2 = new Session();
            session1.FromXML(file1);
            session2.FromXML(file2);
            Hashtable categories = new Hashtable();
            string categorynames="";
            for (int i = 0; (i<session1.OverlappingActivityLists[0].Count); i++)
            {
                categories.Add(session1.OverlappingActivityLists[0][i]._Name, i);
                categorynames+=session1.OverlappingActivityLists[0][i]._Name+",";
            }
            
            int dims=session1.OverlappingActivityLists[0].Count + 1;
            categories.Add("unknown",dims-1);
            categorynames+="unknown";
            int[][] reliability = new int[dims][];
            for (int i = 0; (i < reliability.Length); i++)
            {
                reliability[i] = new int[dims];
                for (int j = 0; (j < dims); j++)
                    reliability[i][j] = 0;
            }

            double startTime = session1.Annotations[0]._StartUnix;
            if (session2.Annotations[0]._StartUnix < startTime)
                startTime = session2.Annotations[0]._StartUnix;
            double endTime = session1.Annotations[session1.Annotations.Count - 1]._EndUnix;
            if (session2.Annotations[session2.Annotations.Count - 1]._EndUnix > endTime)
                endTime = session2.Annotations[session2.Annotations.Count - 1]._EndUnix;

            double currentTime=startTime;
            int currentAnnotation1 = 0;
            int currentAnnotation2 = 0;

            while (currentTime <= endTime)
            {
                double a1end=session1.Annotations[currentAnnotation1]._EndUnix;
                double a1start=session1.Annotations[currentAnnotation1]._StartUnix;

                double a2end=session2.Annotations[currentAnnotation2]._EndUnix;
                double a2start=session2.Annotations[currentAnnotation2]._StartUnix;

                if ((currentTime > a1end) && (currentAnnotation1 < session1.Annotations.Count - 1))
                {
                    a1Changed = true;
                    currentAnnotation1++;
                }
                else
                    a1Changed = false;
                if ((currentTime > a2end) && (currentAnnotation2 < session2.Annotations.Count - 1))
                    currentAnnotation2++;

                string a1label="unknown";
                string a2label="unknown";
                if ((currentTime<=a1end) && (currentTime>=a1start))
                    a1label=session1.Annotations[currentAnnotation1].Activities._CurrentActivity;

                if ((currentTime<=a2end) && (currentTime>=a2start))
                    a2label=session2.Annotations[currentAnnotation2].Activities._CurrentActivity;

                int a1Index = (int)categories[a1label];
                int a2Index = (int)categories[a2label];
                
                reliability[a1Index][a2Index] = reliability[a1Index][a2Index] + 1;
                totalCount++;

                if (a1Index == a2Index)
                    agreeing = true;                
                else
                {
                    
                    if (agreeing)
                    {
                        if ((a1Changed) && (a1label=="unknown"))
                        {
                            double diff = a2end - currentTime;
                            if (diff < 10000)
                            {
                                offsetDelay += diff;
                                offsetCount++;
                            }
                        }
                    }
                    agreeing = false;
                    if (currentAnnotation2<session2.Annotations.Count - 1)
                    {
                        if (session2.Annotations[currentAnnotation2 + 1].Activities._CurrentActivity == a1label)
                        {
                            if (session2.Annotations[currentAnnotation2 + 1]._StartUnix < a1end)
                            {
                                double diff = session2.Annotations[currentAnnotation2 + 1]._StartUnix - a1start;
                                if (diff < 10000)
                                {
                                    delayedAverage += diff;
                                    delayedCount++;
                                }
                            }

                        }
                    }
                }
                currentTime += 1000;
            }

            TextWriter tw = new StreamWriter(root + "results.csv");
            tw.WriteLine("Onset Error," + delayedAverage / delayedCount);
            tw.WriteLine("Delayed Instances," + delayedCount);
            tw.WriteLine("Offset Error," + offsetDelay/offsetCount);
            tw.WriteLine("Offset Instances," + offsetCount);
            tw.Close();
            tw = new StreamWriter(root + "reliability.csv");
            //tw.WriteLine(categorynames);
            for (int i = 0; (i < dims); i++)
                for (int j = 0; (j < dims); j++)
                {
                    tw.Write(reliability[i][j]);
                    if (j == dims - 1)
                        tw.WriteLine();
                    else
                        tw.Write(",");
                }
            tw.Close();


     

        }

        static void Main(string[] args)
        {
            GenerateArff();
           // GenerateInterRateReliability();

            //GenerateCrossValidationDecisionTrees();
            //GenerateTrainingCSVFiles();
            //STANFORD DATA
            /*  string storage = @"C:\DataAnalysis\Stanford-MITes\Subject3\0003v2-sept2408\mites";
              string[] arffList = Directory.GetFiles(storage, "*.arff");
              foreach (string f in arffList)
                  File.Delete(f);


              string[] filter = new string[2];
              filter[0] = "annotation";
              filter[1] = "setup";
            
              Extractor.toARFF(storage, "..\\NeededFiles\\Master\\", 3, filter); 
             */

            //Vanderbilt Data








        }
    }
}
