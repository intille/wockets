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
using AXML;
using System.Collections;

namespace MITesAnalysisApplication
{
    class Program
    {
        static void Main(string[] args)
        {

            string[] filter = new string[2];
            filter[0] = "annotation";
            filter[1] = "setup";

            Extractor.toARFF(@"C:\DataAnalysis\Stanford-MITes\Subject3\0003v2-sept2408\mites", "..\\NeededFiles\\Master\\", 3, filter);

        }
    }
}
