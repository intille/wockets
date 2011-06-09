/*
*    IteratedSingleClassifierEnhancer.java
*    Copyright (C) 2004 Eibe Frank
*
*/
using System;
using Utils = weka.core.Utils;
using Option = weka.core.Option;
using Instances = weka.core.Instances;
namespace weka.classifiers
{
	
	/// <summary> Abstract utility class for handling settings common to
	/// meta classifiers that build an ensemble from a single base learner.  
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2 $
	/// </version>
#if !PocketPC
    [Serializable()]  
#endif
	public abstract class IteratedSingleClassifierEnhancer:SingleClassifierEnhancer
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the number of bagging iterations
		/// 
		/// </summary>
		/// <returns> the maximum number of bagging iterations
		/// </returns>
		/// <summary> Sets the number of bagging iterations</summary>
		virtual public int NumIterations
		{
			get
			{
				
				return m_NumIterations;
			}
			
			set
			{
				
				m_NumIterations = value;
			}
			
		}
		/// <summary>Array for storing the generated base classifiers. </summary>
		protected internal Classifier[] m_Classifiers;
		
		/// <summary>The number of iterations. </summary>
		protected internal int m_NumIterations = 10;
		
		/// <summary> Stump method for building the classifiers.
		/// 
		/// </summary>
		/// <param name="data">the training data to be used for generating the
		/// bagged classifier.
		/// </param>
		/// <exception cref="Exception">if the classifier could not be built successfully
		/// </exception>
		public override void  buildClassifier(Instances data)
		{
			
			if (m_Classifier == null)
			{
				throw new System.Exception("A base classifier has not been specified!");
			}
			m_Classifiers = Classifier.makeCopies(m_Classifier, m_NumIterations);
		}
		
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String numIterationsTipText()
		{
			return "The number of iterations to be performed.";
		}
	}
}