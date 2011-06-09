/*
*    AdditionalMeasureProducer.java
*    Copyright (C) 2000 Mark Hall
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface to something that can produce measures other than those
	/// calculated by evaluation modules. 
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.7 $
	/// </version>
	public interface AdditionalMeasureProducer
	{
		/// <summary> Returns an enumeration of the measure names. Additional measures
		/// must follow the naming convention of starting with "measure", eg.
		/// double measureBlah()
		/// </summary>
		/// <returns> an enumeration of the measure names
		/// </returns>
		System.Collections.IEnumerator enumerateMeasures();
		
		/// <summary> Returns the value of the named measure</summary>
		/// <param name="measureName">the name of the measure to query for its value
		/// </param>
		/// <returns> the value of the named measure
		/// </returns>
		/// <exception cref="IllegalArgumentException">if the named measure is not supported
		/// </exception>
		double getMeasure(System.String measureName);
	}
}