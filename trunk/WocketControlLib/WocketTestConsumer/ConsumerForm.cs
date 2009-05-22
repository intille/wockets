using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using WocketControlLib;
using System.Runtime.InteropServices;
using System.IO;
using ExampleSensor;
using System.Threading;

namespace WocketTestConsumer
{
    public partial class ConsumerForm : Form
    {
        private ExampleSensorB sensor;
        private Thread readingThread;
        private int[] buffer;
        private FeatureStream stream;
        //private FeatureStream stream2;
        private bool killThread = false;

        public ConsumerForm()
        {
            InitializeComponent();
        }

        protected override void OnLoad(EventArgs e)
        {
            base.OnLoad(e);
            buffer = new int[100];
            //sensor = new ExampleSensorA();
            sensor = new ExampleSensorB();
            sensor.Start();
            stream = sensor.OpenFeature("foo", TimeSpan.FromMilliseconds(1), TimeSpan.FromMilliseconds(1), TimeSpan.FromMilliseconds(1000)); //TimeSpan.FromMilliseconds(1), null);
            
            readingThread = new Thread(new ThreadStart(readingFunction));
            readingThread.Start();
        }

        private void readingFunction()
        {
            while (!killThread)
            {
                int intsRead = stream.readInts(buffer, 0, buffer.Length);
                if (intsRead == 0)
                {
                    Thread.Sleep(50);
                    continue;
                }

                for (int ii = 0; ii < intsRead - 1; ii++)
                {
                    if (buffer[ii] != buffer[ii + 1] - 1)
                        throw new Exception("not sequential");
                }
                /*
                intsRead = stream2.readInts(buffer, 0, buffer.Length);
                for (int ii = 0; ii < intsRead - 1; ii++)
                {
                    if (buffer[ii] != buffer[ii + 1] - 1)
                        throw new Exception("Not sequential");
                }*/
            }
        }

        private void menuItem1_Click(object sender, EventArgs e)
        {
            killThread = true;
            readingThread.Join();
            sensor.Stop();
            //mmfstream.Close();
            //filemap.Close();
            this.Close();
            //Application.Exit();
        }





        [DllImport("coredll", SetLastError = true, EntryPoint = "CreateMutex", CharSet = CharSet.Auto)]
        private static extern IntPtr CreateMutex(IntPtr attrs, bool initialOwner, string mutexName);

        [DllImport("coredll", SetLastError = true, EntryPoint = "ReleaseMutex", CharSet = CharSet.Auto)]
        private static extern bool ReleaseMutex(IntPtr handle);

        [DllImport("coredll", SetLastError = true, EntryPoint = "OpenMutex", CharSet = CharSet.Auto)]
        private static extern IntPtr OpenMutex(uint desiredAccess, bool inheritAccess, string mutexName);

        [DllImport("coredll", SetLastError = true, EntryPoint = "WaitForSingleObject", CharSet = CharSet.Auto)]
        private static extern uint WaitForSingleObject(IntPtr handle, uint millis);

        [DllImport("coredll", SetLastError = true, EntryPoint = "CloseHandle", CharSet = CharSet.Auto)]
        private static extern bool CloseHandle(IntPtr handle);
    }
}