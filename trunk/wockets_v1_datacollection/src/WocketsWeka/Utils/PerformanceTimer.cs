using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;
using System.ComponentModel;
using System.Threading;

namespace WocketsWeka.Utils
{
    public class PerformanceTimer
    {
        [DllImport("coredll.dll")]
        private static extern bool QueryPerformanceCounter(
            out long lpPerformanceCount);

        [DllImport("coredll.dll")]
        private static extern bool QueryPerformanceFrequency(
            out long lpFrequency);

        private long startTime, stopTime;
        private long freq;

        // Constructor

        public PerformanceTimer()
        {
            startTime = 0;
            stopTime = 0;

            if (QueryPerformanceFrequency(out freq) == false)
            {
                // high-performance counter not supported

                throw new Win32Exception();
            }
        }

        public void Reset()
        {
            startTime = 0;
            stopTime = 0;
        }
        // Start the timer

        public void Start()
        {
            // lets do the waiting threads there work

            Thread.Sleep(0);

            QueryPerformanceCounter(out startTime);
        }

        // Stop the timer

        public void Stop()
        {
            QueryPerformanceCounter(out stopTime);
        }

        // Returns the duration of the timer (in seconds)

        public double Duration
        {
            get
            {
                return (double)(stopTime - startTime) / (double)freq;
            }
        }
    }
}
