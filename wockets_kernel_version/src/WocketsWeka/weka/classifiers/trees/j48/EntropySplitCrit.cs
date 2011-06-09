/*
*    EntropySplitCrit.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class for computing the entropy for a given distribution.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>

	public sealed class EntropySplitCrit:EntropyBasedSplitCrit
	{
		
		/// <summary> Computes entropy for given distribution.</summary>
		public override double splitCritValue(Distribution bags)
		{
			
			return newEnt(bags);
		}
		
		/// <summary> Computes entropy of test distribution with respect to training distribution.</summary>
		public override double splitCritValue(Distribution train, Distribution test)
		{
			
			double result = 0;
			int numClasses = 0;
			int i, j;
			
			// Find out relevant number of classes
			for (j = 0; j < test.numClasses(); j++)
				if (Utils.gr(train.perClass(j), 0) || Utils.gr(test.perClass(j), 0))
					numClasses++;
			
			// Compute entropy of test data with respect to training data
			for (i = 0; i < test.numBags(); i++)
				if (Utils.gr(test.perBag(i), 0))
				{
					for (j = 0; j < test.numClasses(); j++)
						if (Utils.gr(test.perClassPerBag(i, j), 0))
							result -= test.perClassPerBag(i, j) * System.Math.Log(train.perClassPerBag(i, j) + 1);
					result += test.perBag(i) * System.Math.Log(train.perBag(i) + numClasses);
				}
			
			return result / log2;
		}
	}
}