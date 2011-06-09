/*
*    RemoveUseless.java
*    Copyright (C) 2002 Richard Kirkby
*/
using System;
using weka.filters;
using weka.core;
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> This filter removes attributes that do not vary at all or that vary too much.
	/// All constant attributes are deleted automatically, along with any that exceed
	/// the maximum percentage of variance parameter. The maximum variance test is
	/// only applied to nominal attributes.<p>
	/// 
	/// Valid filter-specific options are: <p>
	/// 
	/// -M percentage <br>
	/// The maximum variance allowed before an attribute will be deleted (default 99).<p>
	/// 
	/// </summary>
	/// <author>  Richard Kirkby (rkirkby@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("This filter removes attributes that do not vary at all or that vary too much.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class RemoveUseless:Filter, UnsupervisedFilter
	//,OptionHandler 
	{
		/// <summary>The filter used to remove attributes </summary>
		protected internal Remove m_removeFilter = null;
		/// <summary>The type of attribute to delete </summary>
		protected internal double m_maxVariancePercentage = 99.0;
		
		/// <summary> Sets the format of the input instances.
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
			
			base.setInputFormat(instanceInfo);
			m_removeFilter = null;
			return false;
		}
		
		/// <summary> Input an instance for filtering.
		/// 
		/// </summary>
		/// <param name="instance">the input instance
		/// </param>
		/// <returns> true if the filtered instance may now be
		/// collected with output().
		/// </returns>
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
			if (m_removeFilter != null)
			{
				m_removeFilter.input(instance);
				Instance processed = m_removeFilter.output();
				processed.Dataset = getOutputFormat();
				push(processed);
				return true;
			}
			bufferInput(instance);
			return false;
		}
		
		/// <summary> Signify that this batch of input to the filter is finished.
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		public override bool batchFinished()
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			if (m_removeFilter == null)
			{
				
				// establish attributes to remove from first batch
				
				Instances toFilter = getInputFormat();
				int[] attsToDelete = new int[toFilter.numAttributes()];
				int numToDelete = 0;
				for (int i = 0; i < toFilter.numAttributes(); i++)
				{
					if (i == toFilter.classIndex())
						continue; // skip class
					AttributeStats stats = toFilter.attributeStats(i);
					if (stats.distinctCount < 2)
					{
						// remove constant attributes
						attsToDelete[numToDelete++] = i;
					}
					else if (toFilter.attribute(i).Nominal)
					{
						// remove nominal attributes that vary too much
						double variancePercent = (double) stats.distinctCount / (double) stats.totalCount * 100.0;
						if (variancePercent > m_maxVariancePercentage)
						{
							attsToDelete[numToDelete++] = i;
						}
					}
				}
				
				int[] finalAttsToDelete = new int[numToDelete];
				Array.Copy(attsToDelete, 0, finalAttsToDelete, 0, numToDelete);
				
				m_removeFilter = new Remove();
				m_removeFilter.SetAttributeIndicesArray(finalAttsToDelete);
				m_removeFilter.set_InvertSelection(false);
				m_removeFilter.setInputFormat(toFilter);
				
				for (int i = 0; i < toFilter.numInstances(); i++)
				{
					m_removeFilter.input(toFilter.instance(i));
				}
				m_removeFilter.batchFinished();
				
				Instance processed;
				Instances outputDataset = m_removeFilter.getOutputFormat();
				
				// restore old relation name to hide attribute filter stamp
				outputDataset.RelationName = toFilter.relationName();
				
				setOutputFormat(outputDataset);
				while ((processed = m_removeFilter.output()) != null)
				{
					processed.Dataset = outputDataset;
					push(processed);
				}
			}
			flushInput();
			
			m_NewBatch = true;
			return (numPendingOutput() != 0);
		}
		
		
		/// <summary> Sets the maximum variance attributes are allowed to have before they are
		/// deleted by the filter.
		/// 
		/// </summary>
		/// <param name="maxVariance">the maximum variance allowed, specified as a percentage
		/// </param>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Set the threshold for the highest variance allowed before a nominal attribute will be deleted.Specifically, if (number_of_distinct_values / total_number_of_values * 100) is greater than this value then the attribute will be removed.")  </attribute>
		/// <property>   </property>
		public virtual void  set_MaximumVariancePercentageAllowed(double maxVariance)
		{
			
			m_maxVariancePercentage = maxVariance;
		}
		
		/// <summary> Gets the maximum variance attributes are allowed to have before they are
		/// deleted by the filter.
		/// 
		/// </summary>
		/// <returns> the maximum variance allowed, specified as a percentage
		/// </returns>
		/// <property>   </property>
		public virtual double get_MaximumVariancePercentageAllowed()
		{
			
			return m_maxVariancePercentage;
		}
	}
}