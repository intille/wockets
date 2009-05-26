/*
* Maths.java
* Copyright (C) 1999 The Mathworks and NIST
*
*/
using System;
namespace weka.core.matrix
{
	
	/// <summary> Utility class.
	/// <p/>
	/// Adapted from the <a href="http://math.nist.gov/javanumerics/jama/" target="_blank">JAMA</a> package.
	/// 
	/// </summary>
	/// <author>  The Mathworks and NIST 
	/// </author>
	/// <author>  Fracpete (fracpete at waikato dot ac dot nz)
	/// </author>
	/// <version>  $Revision: 1.1.2.2 $
	/// </version>
	
	public class Maths
	{
		
		/// <summary> sqrt(a^2 + b^2) without under/overflow. </summary>
		public static double hypot(double a, double b)
		{
			double r;
			if (System.Math.Abs(a) > System.Math.Abs(b))
			{
				r = b / a;
				r = System.Math.Abs(a) * System.Math.Sqrt(1 + r * r);
			}
			else if (b != 0)
			{
				r = a / b;
				r = System.Math.Abs(b) * System.Math.Sqrt(1 + r * r);
			}
			else
			{
				r = 0.0;
			}
			return r;
		}
	}
}