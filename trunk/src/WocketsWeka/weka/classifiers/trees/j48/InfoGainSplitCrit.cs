/*
*    InfoGainSplitCrit.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class for computing the information gain for a given distribution.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
	public sealed class InfoGainSplitCrit:EntropyBasedSplitCrit
	{
		
		/// <summary> This method is a straightforward implementation of the information
		/// gain criterion for the given distribution.
		/// </summary>
		public override double splitCritValue(Distribution bags)
		{
			
			double numerator;
			
			numerator = oldEnt(bags) - newEnt(bags);
			
			// Splits with no gain are useless.
			if (Utils.eq(numerator, 0))
			{
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				return System.Double.MaxValue;
			}
			
			// We take the reciprocal value because we want to minimize the
			// splitting criterion's value.
			return bags.total() / numerator;
		}
		
		/// <summary> This method computes the information gain in the same way 
		/// C4.5 does.
		/// 
		/// </summary>
		/// <param name="distribution">the distribution
		/// </param>
		/// <param name="totalNoInst">weight of ALL instances (including the
		/// ones with missing values).
		/// </param>
		public double splitCritValue(Distribution bags, double totalNoInst)
		{
			
			double numerator;
			double noUnknown;
			double unknownRate;
		
			
			noUnknown = totalNoInst - bags.total();
			unknownRate = noUnknown / totalNoInst;
			numerator = (oldEnt(bags) - newEnt(bags));
			numerator = (1 - unknownRate) * numerator;
			
			// Splits with no gain are useless.
			if (Utils.eq(numerator, 0))
				return 0;
			
			return numerator / bags.total();
		}
		
		/// <summary> This method computes the information gain in the same way 
		/// C4.5 does.
		/// 
		/// </summary>
		/// <param name="distribution">the distribution
		/// </param>
		/// <param name="totalNoInst">weight of ALL instances 
		/// </param>
		/// <param name="oldEnt">entropy with respect to "no-split"-model.
		/// </param>
		public double splitCritValue(Distribution bags, double totalNoInst, double oldEnt)
		{
			
			double numerator;
			double noUnknown;
			double unknownRate;
		
			
			noUnknown = totalNoInst - bags.total();
			unknownRate = noUnknown / totalNoInst;
			numerator = (oldEnt - newEnt(bags));
			numerator = (1 - unknownRate) * numerator;
			
			// Splits with no gain are useless.
			if (Utils.eq(numerator, 0))
				return 0;
			
			return numerator / bags.total();
		}
	}
}