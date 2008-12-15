using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using WocketControlLib;
using ExampleSensor;
using System.Threading;
using System.IO;

namespace WocketTestProducer
{
    public partial class ProducerForm : Form
    {
        private Thread readingThread;
        private bool killThread = false;
        private int[] buffer = new int[128];
        private FeatureStream xyMeanStream;
        private FeatureStream yzMeanStream;
        private FeatureStream zxMeanStream;
        private FeatureStream xVarianceStream;
        private FeatureStream yVarianceStream;
        private FeatureStream zVarianceStream;
        private short[] xyMeans = new short[128];
        private short[] yzMeans = new short[128];
        private short[] zxMeans = new short[128];
        private int[] xVariances = new int[128];
        private int[] yVariances = new int[128];
        private int[] zVariances = new int[128];
        private TextWriter writer;

        private WiTiltSensor tiltSensor;

        public ProducerForm()
        {
            InitializeComponent();
            FileInfo info = new FileInfo("testOutput.txt");
            writer = info.CreateText();
        }

        protected override void OnLoad(EventArgs e)
        {
            base.OnLoad(e);
            tiltSensor = new WiTiltSensor(new byte[] { 0x00, 0x06, 0x66, 0x01, 0x57, 0xcc }, "1234");

            tiltSensor.Start();
            xyMeanStream = tiltSensor.OpenFeature("meanX", TimeSpan.FromMilliseconds(400), TimeSpan.FromMilliseconds(600), TimeSpan.FromSeconds(2));//, TimeSpan.Zero, null);//tiltSensor.OpenFeature("rawX", WiTiltSensor.RAW_SIGNAL_PERIOD, WiTiltSensor.RAW_SIGNAL_PERIOD, TimeSpan.Zero, null);//
            yzMeanStream = tiltSensor.OpenFeature("meanY", TimeSpan.FromMilliseconds(400), TimeSpan.FromMilliseconds(600), TimeSpan.FromSeconds(2));//, TimeSpan.Zero, null);
            zxMeanStream = tiltSensor.OpenFeature("meanZ", TimeSpan.FromMilliseconds(400), TimeSpan.FromMilliseconds(600), TimeSpan.FromSeconds(2));//, TimeSpan.Zero, null);
            xVarianceStream = tiltSensor.OpenFeature("varianceX", TimeSpan.FromMilliseconds(400), TimeSpan.FromMilliseconds(600), TimeSpan.FromSeconds(2));
            yVarianceStream = tiltSensor.OpenFeature("varianceY", TimeSpan.FromMilliseconds(400), TimeSpan.FromMilliseconds(600), TimeSpan.FromSeconds(2));
            zVarianceStream = tiltSensor.OpenFeature("varianceZ", TimeSpan.FromMilliseconds(400), TimeSpan.FromMilliseconds(600), TimeSpan.FromSeconds(2));
            readingThread = new Thread(new ThreadStart(readingFunction2));
            readingThread.Start();
        }
        private void readingFunction2()
        {
            StringBuilder sb = new StringBuilder();

            while (!killThread)
            {
                Thread.Sleep(500);
                int xyMeansRead = xyMeanStream.readShorts(xyMeans, 0, xyMeans.Length);
                int yzMeansRead = yzMeanStream.readShorts(yzMeans, 0, yzMeans.Length);
                int zxMeansRead = zxMeanStream.readShorts(zxMeans, 0, zxMeans.Length);
                int xVariancesRead = xVarianceStream.readInts(xVariances, 0, xVariances.Length);
                int yVariancesRead = yVarianceStream.readInts(yVariances, 0, yVariances.Length);
                int zVariancesRead = zVarianceStream.readInts(zVariances, 0, zVariances.Length);

                if (xyMeansRead != 0)
                {
                    writer.Write("xyMeans (" + xyMeansRead + "): ");
                    sb.Append("XY: ");
                    for (int ii = 0; ii < xyMeansRead; ii++)
                    {
                        writer.Write((int)xyMeans[ii]);
                        sb.Append((int)xyMeans[ii]);
                        sb.Append(" ");
                    }
                    writer.Write("\r\n");
                    sb.Append("\r\n");
                }
                if (yzMeansRead != 0)
                {
                    writer.Write("yzMeans (" + yzMeansRead + "): ");
                    sb.Append("YZ: ");
                    for (int ii = 0; ii < yzMeansRead; ii++)
                    {
                        writer.Write((int)yzMeans[ii]);
                        sb.Append((int)yzMeans[ii]);
                        sb.Append(" ");
                    }
                    sb.Append("\r\n");
                    writer.Write("\r\n");
                }
                if (zxMeansRead != 0)
                {
                    writer.Write("zxMeans (" + zxMeansRead + "): ");
                    sb.Append("ZX: ");
                    for (int ii = 0; ii < zxMeansRead; ii++)
                    {
                        writer.Write((int)zxMeans[ii]);
                        sb.Append((int)zxMeans[ii]);
                        sb.Append(" ");
                    }
                    writer.Write("\r\n");
                    sb.Append("\r\n");
                }
                if (xVariancesRead != 0)
                {
                    sb.Append("X Var: ");
                    for (int ii = 0; ii < xVariancesRead; ii++)
                        sb.Append((int)xVariances[ii]).Append(" ");
                    sb.Append("\r\n");
                }
                if (yVariancesRead != 0)
                {
                    sb.Append("Y Var: ");
                    for (int ii = 0; ii < yVariancesRead; ii++)
                        sb.Append((int)yVariances[ii]).Append(" ");
                    sb.Append("\r\n");
                }
                if (zVariancesRead != 0) 
                {
                    sb.Append("Z Var: ");
                    for (int ii = 0; ii < zVariancesRead; ii++)
                        sb.Append((int)zVariances[ii]).Append(" ");
                    sb.Append("\r\n");
                }
                writeOutput(sb.ToString());
                sb.Length = 0;
                writer.Flush();
            }
            
        }
        private delegate void writeOutputDelegate(string output);

        private void writeOutput(string output)
        {
            if (output == "")
                return;
            if (InvokeRequired)
            {
                BeginInvoke(new writeOutputDelegate(writeOutput), new object[] { output });
                return;
            }

            outputLabel.Text = output;
        }



        private void menuItem1_Click(object sender, EventArgs e)
        {
            killThread = true;
            readingThread.Join();
            tiltSensor.Stop();
            this.Close();
        }
        
    }
}