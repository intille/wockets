/*
*    Matchable.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface to something that can be matched with tree matching
	/// algorithms.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	public interface Matchable
	{
		/// <summary> Returns a string that describes a tree representing
		/// the object in prefix order.
		/// 
		/// </summary>
		/// <returns> the tree described as a string
		/// </returns>
		/// <exception cref="Exception">if the tree can't be computed
		/// </exception>
		System.String prefix();
	}
}