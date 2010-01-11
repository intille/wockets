/*
*    PotentialClassIgnorer.java
*    Copyright (C) 2003 University of Waikato
*
*/
using System;
using Filter = weka.filters.Filter;
using Instances = weka.core.Instances;
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> This filter should be extended by other unsupervised attribute
	/// filters to allow processing of the class attribute if that's
	/// required. It the class is to be ignored it is essential that the
	/// extending filter does not change the position (i.e. index) of the
	/// attribute that is originally the class attribute !
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz), Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2 $ 
	/// </version>
    /// 
#if !PocketPC
	[Serializable]
#endif
	public abstract class PotentialClassIgnorer:Filter
	{
		/// <summary> Set the IgnoreClass value. Set this to true if the
		/// class index is to be unset before the filter is applied.
		/// </summary>
		/// <param name="newIgnoreClass">The new IgnoreClass value.
		/// </param>
		virtual public bool IgnoreClass
		{
			set
			{
				
				m_IgnoreClass = value;
			}
			
		}
		/// <summary>True if the class is to be unset </summary>
		protected internal bool m_IgnoreClass = false;
		/// <summary>Storing the class index </summary>
		protected internal int m_ClassIndex = - 1;
		
		/// <summary> Sets the format of the input instances. If the filter is able to
		/// determine the output format before seeing any input instances, it
		/// does so here. This default implementation clears the output format
		/// and output queue, and the new batch flag is set. Overriders should
		/// call <code>super.setInputFormat(Instances)</code>
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input instance
		/// structure (any instances contained in the object are ignored - only the
		/// structure is required).
		/// </param>
		/// <returns> true if the outputFormat may be collected immediately
		/// </returns>
		/// <exception cref="Exception">if the inputFormat can't be set successfully 
		/// </exception>
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			bool result = base.setInputFormat(instanceInfo);
			if (m_IgnoreClass)
			{
				m_ClassIndex = inputFormatPeek().classIndex();
				inputFormatPeek().ClassIndex = - 1;
			}
			return result;
		}
		
		/// <summary> Gets the format of the output instances. This should only be called
		/// after input() or batchFinished() has returned true. The relation
		/// name of the output instances should be changed to reflect the
		/// action of the filter (eg: add the filter name and options).
		/// 
		/// </summary>
		/// <returns> an Instances object containing the output instance
		/// structure only.
		/// </returns>
		/// <exception cref="NullPointerException">if no input structure has been
		/// defined (or the output format hasn't been determined yet) 
		/// </exception>
		public override Instances getOutputFormat()
		{
			
			if (m_IgnoreClass)
			{
				outputFormatPeek().ClassIndex = m_ClassIndex;
			}
			return base.getOutputFormat();
		}
	}
}