using System;
using System.Collections.Generic;
using System.Text;
using WocketControlLib;

namespace ExampleSensor
{
    public class ExampleSensorB : WocketSensor
    {

        private ExampleSensorA sensorA;
        private FeatureStream inputStream1;
        private FeatureStream inputStream2;


        private byte[] localCopy;

        public ExampleSensorB() : base()
        {
            sensorA = new ExampleSensorA();
            inputStream1 = sensorA.OpenFeature("feature1", TimeSpan.FromMilliseconds(2), TimeSpan.FromMilliseconds(4), TimeSpan.FromSeconds(2));
            inputStream2 = sensorA.OpenFeature("feature2", TimeSpan.FromMilliseconds(5), TimeSpan.FromMilliseconds(10), TimeSpan.FromSeconds(2));
        }

        protected override void OnStart()
        {
            localCopy = new byte[1000];
            sensorA.Start();
        }

        protected override void OnStop()
        {
            sensorA.Stop();
        }

        protected override bool FeatureSupported(string name, TimeSpan period)
        {
            return name.Equals("foo");//frequency doesn't matter?
        }


        protected override void CalculateFeatures(List<Feature> features)
        {
            
        }

        protected override int getSleepTimeMillis()
        {
            return 1000;//This sensor has a guarantee that data from sensorA will be around for 2 seconds, so it decides to be called every 1 second.
        }

    }
}
