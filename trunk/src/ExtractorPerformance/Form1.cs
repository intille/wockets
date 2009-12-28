using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace ExtractorPerformance
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
            Wockets.WocketsController wc = new Wockets.WocketsController("", "", "");
            wc.FromXML("\\Program Files\\extractorperformance\\SensorData.xml");
            Wockets.Data.Classifiers.ClassifierConfiguration conf = new Wockets.Data.Classifiers.Trees.DTConfiguration();
            conf.FromXML("\\Program Files\\extractorperformance\\Configuration.xml");
            FeatureExtractor.InitializeOptional(wc,conf,null);
            double[][] input = new double[18][];
            Random r=new Random();
            for (int i = 0; (i < 18); i++)
            {
                input[i] = new double[128];
                for (int j = 0; (j < 128); j++)
                {
                    input[i][j] = (double)(r.Next(10000) % 1024);
                }
            }
            FeatureExtractor.ExtractOverhead(input);
        }
    }
}