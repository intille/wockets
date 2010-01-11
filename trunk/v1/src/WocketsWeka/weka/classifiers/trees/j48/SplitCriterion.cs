/*
*    SplitCriterion.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Abstract class for computing splitting criteria
	/// with respect to distributions of class values.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>

	public abstract class SplitCriterion
	{
		
		/// <summary> Computes result of splitting criterion for given distribution.
		/// 
		/// </summary>
		/// <returns> value of splitting criterion. 0 by default
		/// </returns>
		public virtual double splitCritValue(Distribution bags)
		{
			
			return 0;
		}
		
		/// <summary> Computes result of splitting criterion for given training and
		/// test distributions.
		/// 
		/// </summary>
		/// <returns> value of splitting criterion. 0 by default
		/// </returns>
		public virtual double splitCritValue(Distribution train, Distribution test)
		{
			
			return 0;
		}
		
		/// <summary> Computes result of splitting criterion for given training and
		/// test distributions and given number of classes.
		/// 
		/// </summary>
		/// <returns> value of splitting criterion. 0 by default
		/// </returns>
		public virtual double splitCritValue(Distribution train, Distribution test, int noClassesDefault)
		{
			
			return 0;
		}
		
		/// <summary> Computes result of splitting criterion for given training and
		/// test distributions and given default distribution.
		/// 
		/// </summary>
		/// <returns> value of splitting criterion. 0 by default
		/// </returns>
		public virtual double splitCritValue(Distribution train, Distribution test, Distribution defC)
		{
			
			return 0;
		}
	}
}