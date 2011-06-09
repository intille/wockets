using System;

using System.Collections.Generic;
using System.Text;

namespace Wockets.Utils
{
    public class Math
    {
        public static int NextPower2(int n)
        {
            int power = 1;
            int count = 0;
            while (power <= n)
            {
                power <<= 1;
                count++;
            }
            return count;
        }
    }
}
