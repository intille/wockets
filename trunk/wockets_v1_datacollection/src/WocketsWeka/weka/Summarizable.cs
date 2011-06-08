/*
*    Summarizable.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface to something that provides a short textual summary (as opposed
	/// to toString() which is usually a fairly complete description) of itself.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	public interface Summarizable
	{
		/// <summary> Returns a string that summarizes the object.
		/// 
		/// </summary>
		/// <returns> the object summarized as a string
		/// </returns>
		System.String toSummaryString();
	}
}