using System;
using System.Collections.Generic;
using System.Text;
using OpenNETCF.WindowsCE;

namespace WocketsApplication.Feedback
{
    public class Vibrator
    {
        //Vibration :: LED object #1

        private OpenNETCF.WindowsCE.Notification.Led Led;

        public  bool isVibrateON = false;

        private bool vibrate = true;

        private int secs = 0;


        public Vibrator()
        {
            if (vibrate)
            {

                //create a vibrate object if it is requested

                Led = new OpenNETCF.WindowsCE.Notification.Led();

                vibrate = true;

            }

        }




        public void StartVibrate()
        {
            if (vibrate)
            {
                if (isVibrateON == false)
                {   //turn on vibration
                    isVibrateON = true;
                    Led.SetLedStatus(1, OpenNETCF.WindowsCE.Notification.Led.LedState.On);

                }
            }
        }




        public void StopVibrate()
        {
            if (vibrate)
            {
                if (isVibrateON == true)
                {
                    //turn off vibration
                    isVibrateON = false;
                    Led.SetLedStatus(1, OpenNETCF.WindowsCE.Notification.Led.LedState.Off);

                }

            }
        }




        public void StartVibrateInterval(int tsec)
        {
            if (vibrate && (tsec != 0))
            {

                StartVibrate();
                System.Threading.Thread.Sleep(tsec * 1000);
                StopVibrate();

            }

        }
    }
}
    