using System;
using System.Threading;


namespace Wockets.Utils
{
    public class Barrier
    {

        private int count;
        private int numSynchronizedThreads;
        private MonitorEx monitor;

        public Barrier(int n)
        {
            //if (n <= 0)
            //    throw new ArgumentException("Barrier initialization specified non-positive value " + n);
            numSynchronizedThreads = count = n;
            monitor = new MonitorEx();
            
        }

        public int NumSynchronizedThreads
        {
            get
            {
                return this.numSynchronizedThreads;
            }

            set
            {
                monitor.Enter();
                this.numSynchronizedThreads = count = value;
                monitor.PulseAll();
                monitor.Exit();            }
        }


        public void Gather()
        {
            monitor.Enter();
            if (--count > 0)
                monitor.Wait();
            else
            {
                count = numSynchronizedThreads;
                monitor.PulseAll();
            }
            monitor.Exit();
        }

    }
}
