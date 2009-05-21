using System;
using System.Collections.Generic;
using System.Text;
using System.Drawing;

namespace Charts
{
    public class RectangleFUtils
    {
        public static RectangleF FromLTRB(float left, float top,
                           float right, float bottom)
        {
            return new RectangleF(left, top, right - left, bottom - top);
        }


        public static RectangleF Union(RectangleF r1, RectangleF r2)
        {
            return FromLTRB(Math.Min(r1.Left, r2.Left),
                     Math.Min(r1.Top, r2.Top),
                     Math.Max(r1.Right, r2.Right),
                     Math.Max(r1.Bottom, r2.Bottom));
        }

    }
}
