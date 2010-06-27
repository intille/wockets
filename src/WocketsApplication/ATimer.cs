using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;
namespace WocketsApplication
{

    public class ATimer
    {
        
        private int DEFAULT_TIMER_CALLBACK = 1000;
        private int interval;
        private int ticks;
        private bool running;
        private Thread timer;

        public ATimer()
        {
            this.timer = new Thread(new ThreadStart(OnTimedEvent));
            this.interval = DEFAULT_TIMER_CALLBACK;
            this.running = false;
            this.timer.Start();
        }

        public ATimer(int interval)
        {
            this.timer = new Thread(new ThreadStart(OnTimedEvent));
            this.interval = interval;
            this.running = false;

            this.running = false;
        }

        public bool isRunning()
        {
            return this.running;
        }

        public int Ticks
        {
            get
            {
                return this.ticks;
            }
        }

        public void start()
        {
            this.running = true;            
        }

        public void stop()
        {
            this.running = false;

        }

        public void reset()
        {
            this.running = false;
            this.ticks = 0;
            TimeSpan ts = TimeSpan.FromSeconds(this.ticks);
            string label = ts.Hours.ToString()
           + ":" + ts.Minutes.ToString("00")
           + ":" + ts.Seconds.ToString("00");
        }


        private void OnTimedEvent()
        {
            while (true)
            {
                if (this.running)
                {
                    this.ticks++;
                    TimeSpan ts = TimeSpan.FromSeconds(this.ticks);
                    string label = ts.Hours.ToString()
                   + ":" + ts.Minutes.ToString("00")
                   + ":" + ts.Seconds.ToString("00");
                }
                Thread.Sleep(interval);
            }
        }
    }
}

