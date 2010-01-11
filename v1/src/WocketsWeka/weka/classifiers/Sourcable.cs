/*
*    Sourcable.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.classifiers
{
	
	/// <summary> Interface for classifiers that can be converted to Java source.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	public interface Sourcable
	{
		
		/// <summary> Returns a string that describes the classifier as source. The
		/// classifier will be contained in a class with the given name (there may
		/// be auxiliary classes),
		/// and will contain a method with the signature:
		/// <pre><code>
		/// public static double classify(Object [] i);
		/// </code></pre>
		/// where the array <code>i</code> contains elements that are either
		/// Double, String, with missing values represented as null. The generated
		/// code is public domain and comes with no warranty.
		/// 
		/// </summary>
		/// <param name="className">the name that should be given to the source class.
		/// </param>
		/// <returns> the object source described by a string
		/// </returns>
		/// <exception cref="Exception">if the souce can't be computed
		/// </exception>
		System.String toSource(System.String className);
	}
}