using System;
using System.Collections.Generic;
using System.Text;
using WocketControlLib;

namespace ExampleSensor
{
    public class ExampleSensorA : WocketSensor
    {

        private int[] buffer = new int[128];
        int lastNumber = 0;
        int lastNumber2 = 117;
        Random rand = new Random((int)DateTime.Now.Ticks);
        public ExampleSensorA() : base()
        {
        }

        protected override void OnStop()
        {
            //nothing
            closeBluetooth();
        }

        private void closeBluetooth()
        {
            //some stuff...
        }
        

        protected override bool FeatureSupported(string name, TimeSpan period)
        {
            if (name.Equals("feature1"))
            {
                return (period <= TimeSpan.FromMilliseconds(4));
            }
            else if (name.Equals("feature2"))
            {
                return period <= TimeSpan.FromMilliseconds(16);
            }
            else
                return false;
        }

        protected override void OnStart()
        {
            openBluetooth();
            //allocate some space
        }

        private void openBluetooth()
        {
            //... do some stuff
        }

        //This is the function that gets called periodically from the WocketSensor code.
        protected override void CalculateFeatures(List<Feature> features)
        {
            if (features.Count == 0)
                return;

            foreach (Feature f in features)
            {
                if (f.Name == "feature1")
                {
                    //fill a random number of slots, between 100 and 128
                    int numberOfSlots = 100;// rand.Next(27) + 100;
                    for (int ii = 0; ii < numberOfSlots; ii++)
                    {
                        buffer[ii] = lastNumber++;
                    }
                    writeFeatureValues(buffer, 0, numberOfSlots, f);
                }
                else if (f.Name == "feature2")
                {
                    int numberOfSlots = 100;
                    for (int ii = 0; ii < numberOfSlots; ii++)
                    {
                        buffer[ii] = lastNumber2++;
                    }
                    writeFeatureValues(buffer, 0, numberOfSlots, f);
                }
            }

        }


        private byte[] readBluetooth()
        {
            return null;
        }
    }
}
