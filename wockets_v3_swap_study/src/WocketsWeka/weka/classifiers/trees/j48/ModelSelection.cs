/*
*    ModelSelection.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
using System.IO;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Abstract class for model selection criteria.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
#if !PocketPC
    [Serializable()]  
#endif
	public abstract class ModelSelection
	{
		
		/// <summary> Selects a model for the given dataset.
		/// 
		/// </summary>
		/// <exception cref="Exception">if model can't be selected
		/// </exception>
		public abstract ClassifierSplitModel selectModel(Instances data);


        public abstract void toXML(TextWriter tw);
		
		/// <summary> Selects a model for the given train data using the given test data
		/// 
		/// </summary>
		/// <exception cref="Exception">if model can't be selected
		/// </exception>
		public virtual ClassifierSplitModel selectModel(Instances train, Instances test)
		{
			
			throw new System.Exception("Model selection method not implemented");
		}
	}
}