/*
*    GainRatioSplitCrit.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class for computing the gain ratio for a given distribution.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>

	public sealed class GainRatioSplitCrit:EntropyBasedSplitCrit
	{
		
		/// <summary> This method is a straightforward implementation of the gain
		/// ratio criterion for the given distribution.
		/// </summary>
		public override double splitCritValue(Distribution bags)
		{
			
			double numerator;
			double denumerator;
			
			numerator = oldEnt(bags) - newEnt(bags);
			
			// Splits with no gain are useless.
			if (Utils.eq(numerator, 0))
			{
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				return System.Double.MaxValue;
			}
			denumerator = splitEnt(bags);
			
			// Test if split is trivial.
			if (Utils.eq(denumerator, 0))
			{
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				return System.Double.MaxValue;
			}
			
			//  We take the reciprocal value because we want to minimize the
			// splitting criterion's value.
			return denumerator / numerator;
		}
		
		/// <summary> This method computes the gain ratio in the same way C4.5 does.
		/// 
		/// </summary>
		/// <param name="bags">the distribution
		/// </param>
		/// <param name="totalnoInst">the weight of ALL instances
		/// </param>
		/// <param name="numerator">the info gain
		/// </param>
		public double splitCritValue(Distribution bags, double totalnoInst, double numerator)
		{
			
			double denumerator;
			
			
			
			// Compute split info.
			denumerator = splitEnt(bags, totalnoInst);
			
			// Test if split is trivial.
			if (Utils.eq(denumerator, 0))
				return 0;
			denumerator = denumerator / totalnoInst;
			
			return numerator / denumerator;
		}
		
		/// <summary> Help method for computing the split entropy.</summary>
		private double splitEnt(Distribution bags, double totalnoInst)
		{
			
			double returnValue = 0;
			double noUnknown;
			int i;
			
			noUnknown = totalnoInst - bags.total();
			if (Utils.gr(bags.total(), 0))
			{
				for (i = 0; i < bags.numBags(); i++)
					returnValue = returnValue - logFunc(bags.perBag(i));
				returnValue = returnValue - logFunc(noUnknown);
				returnValue = returnValue + logFunc(totalnoInst);
			}
			return returnValue;
		}
	}
}