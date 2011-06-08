/*
*    AllFilter.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.filters
{
	
	/// <summary> A simple instance filter that passes all instances directly
	/// through. Basically just for testing purposes.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("A simple instance filter that passes all instances directly through.")  </attribute>
	/// <attribute>  System.ComponentModel.BrowsableAttribute(false)  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class AllFilter:Filter
	{
		/// <summary> Returns a string describing this filter
		/// 
		/// </summary>
		/// <returns> a description of the filter suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "An instance filter that passes all instances through unmodified." + " Primarily for testing purposes.";
		}
		
		/// <summary> Sets the format of the input instances.
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input instance
		/// structure (any instances contained in the object are ignored - only the
		/// structure is required).
		/// </param>
		/// <returns> true if the outputFormat may be collected immediately
		/// </returns>
		public override bool setInputFormat(Instances instanceInfo)
		{
			base.setInputFormat(instanceInfo);
			setOutputFormat(instanceInfo);
			return true;
		}
		
		
		/// <summary> Input an instance for filtering. Ordinarily the instance is processed
		/// and made available for output immediately. Some filters require all
		/// instances be read before producing output.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
		/// <exception cref="IllegalStateException">if no input format has been defined.
		/// </exception>
		public override bool input(Instance instance)
		{
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			if (m_NewBatch)
			{
				resetQueue();
				m_NewBatch = false;
			}
			push((Instance) instance.copy());
			return true;
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain arguments to the filter: use -h for help
		/// </param>
		//	public static void main(String [] argv) 
		//	{
		//		try 
		//		{
		//			if (Utils.getFlag('b', argv)) 
		//			{
		//				Filter.batchFilterFile(new AllFilter(), argv);
		//			} 
		//			else 
		//			{
		//				Filter.filterFile(new AllFilter(), argv);
		//			}
		//		} 
		//		catch (Exception ex) 
		//		{
		//			System.out.println(ex.getMessage());
		//		}
		//	}
	}
}