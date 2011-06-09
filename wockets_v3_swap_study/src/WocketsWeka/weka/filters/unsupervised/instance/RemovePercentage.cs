/*
*    RemovePercentage.java
*    Copyright (C) 2002 Richard Kirkby
*/
using System;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
using Utils = weka.core.Utils;
using Filter = weka.filters.Filter;
using UnsupervisedFilter = weka.filters.UnsupervisedFilter;
namespace weka.filters.unsupervised.instance
{
	
	/// <summary> This filter removes a given percentage of a dataset.
	/// 
	/// Valid options are: <p>
	/// 
	/// -V <br>
	/// Specifies if inverse of selection is to be output.<p>
	/// 
	/// -P percentage <br>
	/// The percentage of instances to select. (default 50)<p>
	/// 
	/// </summary>
	/// <author>  Richard Kirkby (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.3.2.1 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("This filter removes a given percentage of a dataset.")  </attribute>
#if !PocketPC	
    [Serializable]
#endif
	public class RemovePercentage:Filter, UnsupervisedFilter
	{
		/// <summary>Percentage of instances to select. </summary>
		private int m_Percentage = 50;
		/// <summary>Indicates if inverse of selection is to be output. </summary>
		private bool m_Inverse = false;
		
		/// <summary> Gets the percentage of instances to select.
		/// 
		/// </summary>
		/// <returns> the percentage.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The percentage of the data to select.")  </attribute>
		/// <property>   </property>
		public virtual int get_Percentage()
		{
			
			return m_Percentage;
		}
		
		/// <summary> Sets the percentage of intances to select.
		/// 
		/// </summary>
		/// <param name="percent">the percentage
		/// </param>
		/// <exception cref="IllegalArgumentException">if percenatge out of range
		/// </exception>
		/// <property>   </property>
		public virtual void  set_Percentage(int percent)
		{
			
			if (percent < 0 || percent > 100)
			{
				throw new System.ArgumentException("Percentage must be between 0 and 100.");
			}
			m_Percentage = percent;
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
			
			return m_Inverse;
		}
		
		/// <summary> Sets if selection is to be inverted.
		/// 
		/// </summary>
		/// <param name="inverse">true if inversion is to be performed
		/// </param>
		/// <property>   </property>
		public virtual void  set_InvertSelection(bool inverse)
		{
			
			m_Inverse = inverse;
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
		/// <throws>  IllegalStateException if no input format has been set. </throws>
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
			
			// Push instances for output into output queue
			Instances toFilter = getInputFormat();
			int cutOff = toFilter.numInstances() * m_Percentage / 100;
			
			if (m_Inverse)
			{
				for (int i = 0; i < cutOff; i++)
				{
					push(toFilter.instance(i));
				}
			}
			else
			{
				for (int i = cutOff; i < toFilter.numInstances(); i++)
				{
					push(toFilter.instance(i));
				}
			}
			flushInput();
			m_NewBatch = true;
			m_FirstBatchDone = true;
			return (numPendingOutput() != 0);
		}
	}
}