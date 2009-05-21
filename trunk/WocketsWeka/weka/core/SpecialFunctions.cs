/*
*    SpecialFunctions.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class implementing some mathematical functions.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
	public sealed class SpecialFunctions
	{
		
		/// <summary>Some constants </summary>
		private static double log2 = System.Math.Log(2);
		
		/// <summary> Returns natural logarithm of factorial using gamma function.
		/// 
		/// </summary>
		/// <param name="x">the value
		/// </param>
		/// <returns> natural logarithm of factorial
		/// </returns>
		public static double lnFactorial(double x)
		{
			
			return Statistics.lnGamma(x + 1);
		}
		
		/// <summary> Returns base 2 logarithm of binomial coefficient using gamma function.
		/// 
		/// </summary>
		/// <param name="a">upper part of binomial coefficient
		/// </param>
		/// <param name="b">lower part
		/// </param>
		/// <returns> the base 2 logarithm of the binominal coefficient a over b
		/// </returns>
		public static double log2Binomial(double a, double b)
		{
			
			if (Utils.gr(b, a))
			{
				throw new System.ArithmeticException("Can't compute binomial coefficient.");
			}
			return (lnFactorial(a) - lnFactorial(b) - lnFactorial(a - b)) / log2;
		}
		
		/// <summary> Returns base 2 logarithm of multinomial using gamma function.
		/// 
		/// </summary>
		/// <param name="a">upper part of multinomial coefficient
		/// </param>
		/// <param name="bs">lower part
		/// </param>
		/// <returns> multinomial coefficient of a over the bs
		/// </returns>
		public static double log2Multinomial(double a, double[] bs)
		{
			
			double sum = 0;
			int i;
			
			for (i = 0; i < bs.Length; i++)
			{
				if (Utils.gr(bs[i], a))
				{
					throw new System.ArithmeticException("Can't compute multinomial coefficient.");
				}
				else
				{
					sum = sum + lnFactorial(bs[i]);
				}
			}
			return (lnFactorial(a) - sum) / log2;
		}
		
		/// <summary> Main method for testing this class.</summary>
		//	public static void main(String[] ops) 
		//	{
		//
		//		double[] doubles = {1, 2, 3};
		//
		//		System.out.println("6!: " + Math.exp(SpecialFunctions.lnFactorial(6)));
		//		System.out.println("Binomial 6 over 2: " +
		//			Math.pow(2, SpecialFunctions.log2Binomial(6, 2)));
		//		System.out.println("Multinomial 6 over 1, 2, 3: " +
		//			Math.pow(2, SpecialFunctions.log2Multinomial(6, doubles)));
		//	}    
	}
}