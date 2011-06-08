/*
*    RandomizableIteratedSingleClassifierEnhancer.java
*    Copyright (C) 2004 Eibe Frank
*
*/
using System;
using Utils = weka.core.Utils;
using Option = weka.core.Option;
using Instances = weka.core.Instances;
//UPGRADE_TODO: The type 'weka.core.Randomizable' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Randomizable = weka.core.Randomizable;
namespace weka.classifiers
{
	
	/// <summary> Abstract utility class for handling settings common to randomizable
	/// meta classifiers that build an ensemble from a single base learner.  
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2 $
	/// </version>
	public abstract class RandomizableIteratedSingleClassifierEnhancer:IteratedSingleClassifierEnhancer, Randomizable
	{
		/// <summary>The random number seed. </summary>
		protected internal int m_Seed = 1;
		
		/// <summary> Set the seed for random number generation.
		/// 
		/// </summary>
		/// <param name="seed">the seed 
		/// </param>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The random number seed to be used.")  </attribute>
		/// <property>   </property>
		public virtual void  set_Seed(int seed)
		{
			
			m_Seed = seed;
		}
		
		/// <summary> Gets the seed for the random number generations
		/// 
		/// </summary>
		/// <returns> the seed for the random number generation
		/// </returns>
		/// <property>   </property>
		public virtual int get_Seed()
		{
			
			return m_Seed;
		}
	}
}