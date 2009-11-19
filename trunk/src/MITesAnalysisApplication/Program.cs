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

namespace MITesAnalysisApplication
{
    class Program
    {
        static void Main(string[] args)
        {
            string storage = @"C:\DataAnalysis\Stanford-MITes\Subject3\0003v2-sept2408\mites";
            string[] arffList = Directory.GetFiles(storage, "*.arff");
            foreach (string f in arffList)
                File.Delete(f);


            string[] filter = new string[2];
            filter[0] = "annotation";
            filter[1] = "setup";
            
            Extractor.toARFF(storage, "..\\NeededFiles\\Master\\", 3, filter); 
            string[] originalFile = Directory.GetFileSystemEntries(storage, "*output*.arff");                
            if (originalFile.Length != 1)
              throw new Exception("Multiple Arff Files in Directory");

          
            TextReader tr = new StreamReader(originalFile[0]);
            string activities = "";
            while (((activities = tr.ReadLine()) != null) && (!activities.Contains("@ATTRIBUTE activity {"))) ;

            activities = activities.Substring(activities.IndexOf("activity {") + 10);
            activities= activities.Substring(0,activities.IndexOf("}"));
            string[] lactivities=activities.Trim().Split(new char[1]{','});
            TextWriter etw = new StreamWriter(storage + "\\Examples.csv");
            etw.WriteLine("Activity,Number of Examples");

            //Generate new activity files
            foreach (string activity in lactivities)
            {
                if (activity != "unknown")
                {
                    TextReader atr = new StreamReader(originalFile[0]);
                    TextWriter atw = new StreamWriter(storage+"\\Activity_"+activity + ".arff");
                    string line = "";
                    int num_examples = 0;
                    while ((line = atr.ReadLine()) != null)
                    {                                           
                        if (line.Contains("@ATTRIBUTE activity {"))
                            atw.WriteLine("@ATTRIBUTE activity {unknown," + activity + "}");
                        else if (line.Contains("@DATA") || line.Contains("@RELATION") || line.Contains("@ATTRIBUTE"))
                            atw.WriteLine(line);
                        else if (line.Contains(","))
                        {
                            if (line.Contains(activity))
                                num_examples++;
                            int lastComma = line.LastIndexOf(',');
                            string currentActivity = line.Substring(lastComma + 1, line.Length - lastComma-1 );
                            if ((currentActivity != activity) && (currentActivity != "unknown"))
                                line = line.Substring(0, lastComma) + ",unknown";
                            atw.WriteLine(line);
                        }
                    }
                    atw.Close();
                    atr.Close();
                    if (num_examples <= 50)
                        File.Delete(storage + "\\Activity_" + activity + ".arff");
                    etw.WriteLine(activity + "," + num_examples);
                }
            }

            etw.Close();
            arffList = Directory.GetFiles(storage, "Activity_*.arff");
            foreach (string f in arffList)
            {
                int aStart=f.IndexOf("Activity_")+9;
                int aEnd= f.IndexOf(".arff");
                string currentActivity = f.Substring(aStart, aEnd - aStart);

                Instances instances = new Instances(new StreamReader(f));
                instances.Class = instances.attribute(instances.numAttributes() - 1);

                weka.filters.supervised.instance.Resample resampler = new weka.filters.supervised.instance.Resample();
                resampler.set_BiasToUniformClass(1.0); //balance the samples
                resampler.set_RandomSeed(1);
                resampler.set_SampleSizePercent(100.0);
                Instances balancedInstances = null;
                resampler.setInputFormat(instances);
                balancedInstances = Filter.useFilter(instances, resampler);


                InfoGainAttributeEval ig = new InfoGainAttributeEval();
                ig.BinarizeNumericAttributes = false;
                ig.MissingMerge = true;

                Ranker ranker = new Ranker();
                ranker.GenerateRanking = true;
                ranker.NumToSelect = -1;
                ranker.Threshold = -1.7976931348623157E308;

                AttributeSelection selector = new AttributeSelection();
                selector.Evaluator = ig;
                selector.Xval = true;
                selector.Folds = 10;
                selector.Seed = 1;
                selector.Ranking = true;
                selector.Search = ranker;
                selector.SelectAttributes(balancedInstances);

                TextWriter tw = new StreamWriter(storage + "\\"+currentActivity+"_IGRanking.csv");

                tw.WriteLine("Feature, Index, Location, Average IG, Average Std IG, Average Rank, Average Std Rank");
                for (int i = 0; (i < selector.CVRanks.Length); i++)
                {
                    if (selector.m_rankResults[1][selector.CVRanks[i]] > 0)
                    {
                        string featureName = instances.attribute(selector.CVRanks[i]).name();
                        string featureLocation = featureName.Substring(featureName.IndexOf("Location") + 8);
                        if (featureLocation.IndexOf("_")>0)
                            featureLocation = featureLocation.Substring(0, featureLocation.IndexOf("_"));
                        tw.Write(featureName + ",");
                        tw.Write(selector.CVRanks[i]+",");
                        tw.Write(featureLocation + ",");   
                        tw.Write((selector.m_rankResults[0][selector.CVRanks[i]]).ToString("0.00") + ",");
                        tw.Write((selector.m_rankResults[2][selector.CVRanks[i]]).ToString("0.00") + ",");
                        tw.Write((selector.m_rankResults[1][selector.CVRanks[i]]).ToString("0.00") + ",");
                        tw.WriteLine((selector.m_rankResults[3][selector.CVRanks[i]]).ToString("0.00"));
                    }
                }
                tw.Close();

            }

          



        }
    }
}
