using System;
using System.Collections.Generic;
using System.Text;
using System.Windows.Forms;

namespace WocketsApplication.Utils
{

    public class ATimer
    {
        private Timer timer;
        private int DEFAULT_TIMER_CALLBACK = 1000;
        private SetTextControlCallback c;
        private int control_id;
        private int ticks;
        private bool running;

        public ATimer(SetTextControlCallback c, int control_id)
        {
            this.timer = new Timer();
            this.timer.Tick += new EventHandler(OnTimedEvent);
            // Set the Interval to 1 seconds.
            this.timer.Interval = DEFAULT_TIMER_CALLBACK;
            this.timer.Enabled = false;
            this.c = c;
            this.control_id = control_id;
            this.running = false;
        }

        public ATimer(int interval, SetTextControlCallback c, int control_id)
        {
            this.timer = new Timer();
            this.timer.Tick += new EventHandler(OnTimedEvent);
            // Set the Interval to 1 seconds.
            this.timer.Interval = interval;
            this.timer.Enabled = false;
            this.c = c;
            this.control_id = control_id;
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
            this.timer.Enabled = true;
        }

        public void stop()
        {
            this.running = false;
            this.timer.Enabled = false;
        }

        public void reset()
        {
            this.running = false;
            this.timer.Enabled = false;
            this.ticks = 0;
            TimeSpan ts = TimeSpan.FromSeconds(this.ticks);
            string label = ts.Hours.ToString()
           + ":" + ts.Minutes.ToString("00")
           + ":" + ts.Seconds.ToString("00");
            this.c.SetText(label, this.control_id);
        }


        private void OnTimedEvent(object source, EventArgs e)
        {
            this.ticks++;
            TimeSpan ts = TimeSpan.FromSeconds(this.ticks);
            string label = ts.Hours.ToString()
           + ":" + ts.Minutes.ToString("00")
           + ":" + ts.Seconds.ToString("00");
            this.c.SetText(label, this.control_id);


        }
    }
}

