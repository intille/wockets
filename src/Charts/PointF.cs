using System;
using System.Globalization;
using System.Runtime.InteropServices;
using System.ComponentModel;

namespace System.Drawing
{
    public struct PointF
    {
        // Private x and y coordinate fields.
        private float x, y;

        // -----------------------
        // Public Shared Members
        // -----------------------

        /// <summary>
        ///	Empty Shared Field
        /// </summary>
        ///
        /// <remarks>
        ///	An uninitialized PointF Structure.
        /// </remarks>

        public static readonly PointF Empty;

        /// <summary>
        ///	Addition Operator
        /// </summary>
        ///
        /// <remarks>
        ///	Translates a PointF using the Width and Height
        ///	properties of the given Size.
        /// </remarks>

        public static PointF operator +(PointF pt, Size sz)
        {
            return new PointF(pt.X + sz.Width, pt.Y + sz.Height);
        }
#if NET_2_0
		public static PointF operator + (PointF pt, SizeF sz)
		{
			return new PointF (pt.X + sz.Width, pt.Y + sz.Height);
		}
#endif

        /// <summary>
        ///	Equality Operator
        /// </summary>
        ///
        /// <remarks>
        ///	Compares two PointF objects. The return value is
        ///	based on the equivalence of the X and Y properties 
        ///	of the two points.
        /// </remarks>

        public static bool operator ==(PointF pt_a, PointF pt_b)
        {
            return ((pt_a.X == pt_b.X) && (pt_a.Y == pt_b.Y));
        }

        /// <summary>
        ///	Inequality Operator
        /// </summary>
        ///
        /// <remarks>
        ///	Compares two PointF objects. The return value is
        ///	based on the equivalence of the X and Y properties 
        ///	of the two points.
        /// </remarks>

        public static bool operator !=(PointF pt_a, PointF pt_b)
        {
            return ((pt_a.X != pt_b.X) || (pt_a.Y != pt_b.Y));
        }

        /// <summary>
        ///	Subtraction Operator
        /// </summary>
        ///
        /// <remarks>
        ///	Translates a PointF using the negation of the Width 
        ///	and Height properties of the given Size.
        /// </remarks>

        public static PointF operator -(PointF pt, Size sz)
        {
            return new PointF(pt.X - sz.Width, pt.Y - sz.Height);
        }
#if NET_2_0
		public static PointF operator - (PointF pt, SizeF sz)
		{
			return new PointF (pt.X - sz.Width, pt.Y - sz.Height);
		}
#endif

        // -----------------------
        // Public Constructor
        // -----------------------

        /// <summary>
        ///	PointF Constructor
        /// </summary>
        ///
        /// <remarks>
        ///	Creates a PointF from a specified x,y coordinate pair.
        /// </remarks>

        public PointF(float x, float y)
        {
            this.x = x;
            this.y = y;
        }

        // -----------------------
        // Public Instance Members
        // -----------------------

        /// <summary>
        ///	IsEmpty Property
        /// </summary>
        ///
        /// <remarks>
        ///	Indicates if both X and Y are zero.
        /// </remarks>

  
        public bool IsEmpty
        {
            get
            {
                return ((x == 0.0) && (y == 0.0));
            }
        }

        /// <summary>
        ///	X Property
        /// </summary>
        ///
        /// <remarks>
        ///	The X coordinate of the PointF.
        /// </remarks>

        public float X
        {
            get
            {
                return x;
            }
            set
            {
                x = value;
            }
        }

        /// <summary>
        ///	Y Property
        /// </summary>
        ///
        /// <remarks>
        ///	The Y coordinate of the PointF.
        /// </remarks>

        public float Y
        {
            get
            {
                return y;
            }
            set
            {
                y = value;
            }
        }

        /// <summary>
        ///	Equals Method
        /// </summary>
        ///
        /// <remarks>
        ///	Checks equivalence of this PointF and another object.
        /// </remarks>

        public override bool Equals(object o)
        {
            if (!(o is PointF))
                return false;

            return (this == (PointF)o);
        }

        /// <summary>
        ///	GetHashCode Method
        /// </summary>
        ///
        /// <remarks>
        ///	Calculates a hashing value.
        /// </remarks>

        public override int GetHashCode()
        {
            return (int)x ^ (int)y;
        }

        /// <summary>
        ///	ToString Method
        /// </summary>
        ///
        /// <remarks>
        ///	Formats the PointF as a string in coordinate notation.
        /// </remarks>

        public override string ToString()
        {
            return String.Format("{{X={0}, Y={1}}}", x.ToString(CultureInfo.CurrentCulture),
                y.ToString(CultureInfo.CurrentCulture));
        }

#if NET_2_0
		public static PointF Add (PointF pt, Size sz)
		{
			return new PointF (pt.X + sz.Width, pt.Y + sz.Height);
		}
		
		public static PointF Add (PointF pt, SizeF sz)
		{
			return new PointF (pt.X + sz.Width, pt.Y + sz.Height);
		}

		public static PointF Subtract (PointF pt, Size sz)
		{
			return new PointF (pt.X - sz.Width, pt.Y - sz.Height);
		}

		public static PointF Subtract (PointF pt, SizeF sz)
		{
			return new PointF (pt.X - sz.Width, pt.Y - sz.Height);
		}
#endif

    }
}
