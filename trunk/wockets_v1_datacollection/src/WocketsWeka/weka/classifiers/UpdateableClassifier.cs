/*
*    UpdateableClassifier.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
namespace weka.classifiers
{
	
	/// <summary> Interface to incremental classification models that can learn using
	/// one instance at a time.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	public interface UpdateableClassifier
	{
		/// <summary> Updates a classifier using the given instance.
		/// 
		/// </summary>
		/// <param name="instance">the instance to included
		/// </param>
		/// <exception cref="Exception">if instance could not be incorporated
		/// successfully
		/// </exception>
		void  updateClassifier(Instance instance);
	}
}