/*
*    EntropyBasedSplitCrit.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> "Abstract" class for computing splitting criteria
	/// based on the entropy of a class distribution.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>

	public abstract class EntropyBasedSplitCrit:SplitCriterion
	{
		
		/// <summary>The log of 2. </summary>
		protected internal static double log2 = System.Math.Log(2);
		
		/// <summary> Help method for computing entropy.</summary>
		public double logFunc(double num)
		{
			
			// Constant hard coded for efficiency reasons
			if (num < 1e-6)
				return 0;
			else
				return num * System.Math.Log(num) / log2;
		}
		
		/// <summary> Computes entropy of distribution before splitting.</summary>
		public double oldEnt(Distribution bags)
		{
			
			double returnValue = 0;
			int j;
			
			for (j = 0; j < bags.numClasses(); j++)
				returnValue = returnValue + logFunc(bags.perClass(j));
			return logFunc(bags.total()) - returnValue;
		}
		
		/// <summary> Computes entropy of distribution after splitting.</summary>
		public double newEnt(Distribution bags)
		{
			
			double returnValue = 0;
			int i, j;
			
			for (i = 0; i < bags.numBags(); i++)
			{
				for (j = 0; j < bags.numClasses(); j++)
					returnValue = returnValue + logFunc(bags.perClassPerBag(i, j));
				returnValue = returnValue - logFunc(bags.perBag(i));
			}
			return - returnValue;
		}
		
		/// <summary> Computes entropy after splitting without considering the
		/// class values.
		/// </summary>
		public double splitEnt(Distribution bags)
		{
			
			double returnValue = 0;
			int i;
			
			for (i = 0; i < bags.numBags(); i++)
				returnValue = returnValue + logFunc(bags.perBag(i));
			return logFunc(bags.total()) - returnValue;
		}
	}
}