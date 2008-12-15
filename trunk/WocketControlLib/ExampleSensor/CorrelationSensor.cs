using System;
using System.Collections.Generic;
using System.Text;
using WocketControlLib;

namespace ExampleSensor
{
    public class CorrelationSensor : WocketSensor 
    {
        protected override bool FeatureSupported(string name, TimeSpan period)
        {
            throw new Exception("The method or operation is not implemented.");
        }

        protected override void OnStart()
        {
            throw new Exception("The method or operation is not implemented.");
        }

        protected override void OnStop()
        {
            throw new Exception("The method or operation is not implemented.");
        }
        
        protected override void CalculateFeatures(List<Feature> features)
        {
            throw new Exception("The method or operation is not implemented.");
        }
    }
}
