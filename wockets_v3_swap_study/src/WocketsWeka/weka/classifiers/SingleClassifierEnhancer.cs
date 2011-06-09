/*
*    SingleClassifierEnhancer.java
*    Copyright (C) 2004 Eibe Frank
*
*/
using System;
//UPGRADE_TODO: The type 'weka.classifiers.rules.ZeroR' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using ZeroR = weka.classifiers.rules.ZeroR;
using Utils = weka.core.Utils;
using Option = weka.core.Option;
namespace weka.classifiers
{
	
	/// <summary> Abstract utility class for handling settings common to meta
	/// classifiers that use a single base learner.  
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2.2.1 $
	/// </version>
#if !PocketPC
    [Serializable()]  
#endif
	public abstract class SingleClassifierEnhancer:Classifier
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the classifier used as the base learner.
		/// 
		/// </summary>
		/// <returns> the classifier used as the classifier
		/// </returns>
		/// <summary> Set the base learner.
		/// 
		/// </summary>
		/// <param name="newClassifier">the classifier to use.
		/// </param>
		virtual public Classifier Classifier
		{
			get
			{
				
				return m_Classifier;
			}
			
			set
			{
				
				m_Classifier = value;
			}
			
		}
		/// <summary> Gets the classifier specification string, which contains the class name of
		/// the classifier and any options to the classifier
		/// 
		/// </summary>
		/// <returns> the classifier string
		/// </returns>
		virtual protected internal System.String ClassifierSpec
		{
			get
			{
				
				Classifier c = Classifier;
				return c.GetType().FullName;
			}
			
		}
		/// <summary>The base classifier to use </summary>
		protected internal Classifier m_Classifier = new ZeroR();
		
		/// <summary> String describing default classifier.</summary>
		protected internal virtual System.String defaultClassifierString()
		{
			
			return "weka.classifiers.rules.ZeroR";
		}
		
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String classifierTipText()
		{
			return "The base classifier to be used.";
		}
	}
}