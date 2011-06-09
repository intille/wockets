/*
*    ReplaceMissingValues.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using weka.filters;
using weka.core;
namespace weka.filters.unsupervised.attribute
{
	
	/// <summary> Replaces all missing values for nominal and numeric attributes in a 
	/// dataset with the modes and means from the training data.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz) 
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Replaces all missing values for nominal and numeric attributes in a dataset with the modes and means from the training data.")  </attribute>
	public class ReplaceMissingValues:PotentialClassIgnorer, UnsupervisedFilter
	{
		/// <summary>The modes and means </summary>
		private double[] m_ModesAndMeans = null;
		
		/// <summary> Sets the format of the input instances.
		/// 
		/// </summary>
		/// <param name="instanceInfo">an Instances object containing the input 
		/// instance structure (any instances contained in the object are 
		/// ignored - only the structure is required).
		/// </param>
		/// <returns> true if the outputFormat may be collected immediately
		/// </returns>
		/// <exception cref="Exception">if the input format can't be set 
		/// successfully
		/// </exception>
		public virtual bool setInputFormat(Instances instanceInfo)
		{
			
			base.setInputFormat(instanceInfo);
			setOutputFormat(instanceInfo);
			m_ModesAndMeans = null;
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
		/// <exception cref="IllegalStateException">if no input format has been set.
		/// </exception>
		public virtual bool input(Instance instance)
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
			if (m_ModesAndMeans == null)
			{
				bufferInput(instance);
				return false;
			}
			else
			{
				convertInstance(instance);
				return true;
			}
		}
		
		/// <summary> Signify that this batch of input to the filter is finished. 
		/// If the filter requires all instances prior to filtering,
		/// output() may now be called to retrieve the filtered instances.
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		/// <exception cref="IllegalStateException">if no input structure has been defined
		/// </exception>
		public virtual bool batchFinished()
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			
			if (m_ModesAndMeans == null)
			{
				// Compute modes and means
				double sumOfWeights = getInputFormat().sumOfWeights();
				double[][] counts = new double[getInputFormat().numAttributes()][];
				for (int i = 0; i < getInputFormat().numAttributes(); i++)
				{
					if (getInputFormat().attribute(i).Nominal)
					{
						counts[i] = new double[getInputFormat().attribute(i).numValues()];
						counts[i][0] = sumOfWeights;
					}
				}
				double[] sums = new double[getInputFormat().numAttributes()];
				for (int i = 0; i < sums.Length; i++)
				{
					sums[i] = sumOfWeights;
				}
				double[] results = new double[getInputFormat().numAttributes()];
				for (int j = 0; j < getInputFormat().numInstances(); j++)
				{
					Instance inst = getInputFormat().instance(j);
					for (int i = 0; i < inst.numValues(); i++)
					{
						if (!inst.isMissingSparse(i))
						{
							double value_Renamed = inst.valueSparse(i);
							if (inst.attributeSparse(i).Nominal)
							{
								//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
								counts[inst.index(i)][(int) value_Renamed] += inst.weight();
								counts[inst.index(i)][0] -= inst.weight();
							}
							else if (inst.attributeSparse(i).Numeric)
							{
								results[inst.index(i)] += inst.weight() * inst.valueSparse(i);
							}
						}
						else
						{
							if (inst.attributeSparse(i).Nominal)
							{
								counts[inst.index(i)][0] -= inst.weight();
							}
							else if (inst.attributeSparse(i).Numeric)
							{
								sums[inst.index(i)] -= inst.weight();
							}
						}
					}
				}
				m_ModesAndMeans = new double[getInputFormat().numAttributes()];
				for (int i = 0; i < getInputFormat().numAttributes(); i++)
				{
					if (getInputFormat().attribute(i).Nominal)
					{
						m_ModesAndMeans[i] = (double) Utils.maxIndex(counts[i]);
					}
					else if (getInputFormat().attribute(i).Numeric)
					{
						if (Utils.gr(sums[i], 0))
						{
							m_ModesAndMeans[i] = results[i] / sums[i];
						}
					}
				}
				
				// Convert pending input instances
				for (int i = 0; i < getInputFormat().numInstances(); i++)
				{
					convertInstance(getInputFormat().instance(i));
				}
			}
			// Free memory
			flushInput();
			
			m_NewBatch = true;
			return (numPendingOutput() != 0);
		}
		
		/// <summary> Convert a single instance over. The converted instance is 
		/// added to the end of the output queue.
		/// 
		/// </summary>
		/// <param name="instance">the instance to convert
		/// </param>
		private void  convertInstance(Instance instance)
		{
			
			Instance inst = null;
			if (instance is SparseInstance)
			{
				double[] vals = new double[instance.numValues()];
				int[] indices = new int[instance.numValues()];
				int num = 0;
				for (int j = 0; j < instance.numValues(); j++)
				{
					if (instance.isMissingSparse(j) && (getInputFormat().classIndex() != instance.index(j)) && (instance.attributeSparse(j).Nominal || instance.attributeSparse(j).Numeric))
					{
						if (m_ModesAndMeans[instance.index(j)] != 0.0)
						{
							vals[num] = m_ModesAndMeans[instance.index(j)];
							indices[num] = instance.index(j);
							num++;
						}
					}
					else
					{
						vals[num] = instance.valueSparse(j);
						indices[num] = instance.index(j);
						num++;
					}
				}
				if (num == instance.numValues())
				{
					inst = new SparseInstance(instance.weight(), vals, indices, instance.numAttributes());
				}
				else
				{
					double[] tempVals = new double[num];
					int[] tempInd = new int[num];
					Array.Copy(vals, 0, tempVals, 0, num);
					Array.Copy(indices, 0, tempInd, 0, num);
					inst = new SparseInstance(instance.weight(), tempVals, tempInd, instance.numAttributes());
				}
			}
			else
			{
				double[] vals = new double[getInputFormat().numAttributes()];
				for (int j = 0; j < instance.numAttributes(); j++)
				{
					if (instance.isMissing(j) && (getInputFormat().classIndex() != j) && (getInputFormat().attribute(j).Nominal || getInputFormat().attribute(j).Numeric))
					{
						vals[j] = m_ModesAndMeans[j];
					}
					else
					{
						vals[j] = instance.value_Renamed(j);
					}
				}
				inst = new Instance(instance.weight(), vals);
			}
			inst.Dataset = instance.dataset();
			push(inst);
		}
	}
}