/*
*    Randomizable.java
*    Copyright (C) 2003 Richard Kirkby
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface to something that has random behaviour that is able to be
	/// seeded with an integer.
	/// 
	/// </summary>
	/// <author>  Richard Kirkby (rkirkby@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2 $
	/// </version>
	public interface Randomizable
	{
		/// <summary> Set the seed for random number generation.
		/// 
		/// </summary>
		/// <param name="seed">the seed 
		/// </param>
		/// <property>   </property>
		void  set_Seed(int seed);
		
		/// <summary> Gets the seed for the random number generations
		/// 
		/// </summary>
		/// <returns> the seed for the random number generation
		/// </returns>
		/// <property>   </property>
		int get_Seed();
	}
}