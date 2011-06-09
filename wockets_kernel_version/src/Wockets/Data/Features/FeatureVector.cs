using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Data.Features
{
    public abstract class FeatureVector
    {
        public double[] _Values;
        
        public FeatureVector()
        {            
        }

        public abstract bool Extract();
    }
}
