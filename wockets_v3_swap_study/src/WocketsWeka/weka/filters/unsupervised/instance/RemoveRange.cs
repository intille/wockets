/*
*    RemoveRange.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
//UPGRADE_TODO: The type 'weka.core.Range' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Range = weka.core.Range;
using Utils = weka.core.Utils;
using Filter = weka.filters.Filter;
using UnsupervisedFilter = weka.filters.UnsupervisedFilter;
namespace weka.filters.unsupervised.instance
{
	
	/// <summary> This filter takes a dataset and removes a subset of it.
	/// 
	/// Valid options are: <p>
	/// 
	/// -R inst1,inst2-inst4,... <br>
	/// Specifies list of instances to select. First
	/// and last are valid indexes. (required)<p>
	/// 
	/// -V <br>
	/// Specifies if inverse of selection is to be output.<p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.3.2.1 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("This filter takes a dataset and removes a subset of it.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class RemoveRange:Filter, UnsupervisedFilter
	{
		/// <summary>Range of instances requested by the user. </summary>
		private Range m_Range = new Range("first-last");
		
		/// <summary> Gets ranges of instances selected.
		/// 
		/// </summary>
		/// <returns> a string containing a comma-separated list of ranges
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The range of instances to select. First and last are valid indexes.")  </attribute>
		/// <property>   </property>
		public virtual System.String get_InstancesIndices()
		{
			
			return m_Range.Ranges;
		}
		
		/// <summary> Sets the ranges of instances to be selected. If provided string
		/// is null, ranges won't be used for selecting instances.
		/// 
		/// </summary>
		/// <param name="rangeList">a string representing the list of instances. 
		/// eg: first-3,5,6-last
		/// </param>
		/// <exception cref="IllegalArgumentException">if an invalid range list is supplied 
		/// </exception>
		/// <property>   </property>
		public virtual void  set_InstancesIndices(System.String rangeList)
		{
			
			m_Range.Ranges=rangeList;
		}
		
		
		/// <summary> Gets if selection is to be inverted.
		/// 
		/// </summary>
		/// <returns> true if the selection is to be inverted
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Whether to invert the selection.")  </attribute>
		/// <property>   </property>
		public virtual bool get_InvertSelection()
		{
			
			return m_Range.Invert;
		}
		
		/// <summary> Sets if selection is to be inverted.
		/// 
		/// </summary>
		/// <param name="inverse">true if inversion is to be performed
		/// </param>
		/// <property>   </property>
		public virtual void  set_InvertSelection(bool inverse)
		{
			
			m_Range.Invert=inverse;
		}
		
		/// <summary> Sets the format of the input instances.
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input instance
		/// structure (any instances contained in the object are ignored - only the
		/// structure is required).
		/// </param>
		/// <returns> true because outputFormat can be collected immediately
		/// </returns>
		/// <exception cref="Exception">if the input format can't be set successfully
		/// </exception>
		public override bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(instanceInfo);
			setOutputFormat(instanceInfo);
			return true;
		}
		
		/// <summary> Input an instance for filtering. Filter requires all
		/// training instances be read before producing output.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
		/// <throws>  IllegalStateException if no input structure has been defined </throws>
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
			if (m_FirstBatchDone)
			{
				push(instance);
				return true;
			}
			else
			{
				bufferInput(instance);
				return false;
			}
		}
		
		/// <summary> Signify that this batch of input to the filter is
		/// finished. Output() may now be called to retrieve the filtered
		/// instances.
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		/// <exception cref="IllegalStateException">if no input structure has been defined 
		/// </exception>
		public override bool batchFinished()
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			if (!m_FirstBatchDone)
			{
				// Push instances for output into output queue
				m_Range.Upper=getInputFormat().numInstances() - 1;
				for (int i = 0; i < getInputFormat().numInstances(); i++)
				{
					if (!m_Range.isInRange(i))
					{
						push(getInputFormat().instance(i));
					}
				}
			}
			else
			{
				for (int i = 0; i < getInputFormat().numInstances(); i++)
				{
					push(getInputFormat().instance(i));
				}
			}
			flushInput();
			m_NewBatch = true;
			m_FirstBatchDone = true;
			return (numPendingOutput() != 0);
		}
	}
}