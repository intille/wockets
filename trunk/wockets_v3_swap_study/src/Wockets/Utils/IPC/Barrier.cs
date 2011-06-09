using System;
using System.Threading;


namespace Wockets.Utils.IPC
{
    /// <summary>
    /// A synchronization barrier to force threads to gather before proceeding
    /// </summary>
    public class Barrier
    {

        private int count;
        private int numSynchronizedThreads;
        private MonitorEx monitor;

        /// <summary>
        /// Initializes the barrier
        /// </summary>
        /// <param name="n">Number of threads to gather at the barrier</param>
        public Barrier(int n)
        {
            numSynchronizedThreads = count = n;
            monitor = new MonitorEx();            
        }

        /// <summary>
        /// Number of synchronized threads
        /// </summary>
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
                monitor.Exit();            
            }
        }


        /// <summary>
        /// Blocking call for threads to gather
        /// </summary>
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
