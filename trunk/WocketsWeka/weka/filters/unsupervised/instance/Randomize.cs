/*
*    Randomize.java
*    Copyright (C) 1999 Len Trigg
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
	
	/// <summary> This filter randomly shuffles the order of instances passed through it.
	/// The random number generator is reset with the seed value whenever
	/// setInputFormat() is called. <p>
	/// 
	/// Valid filter-specific options are:<p>
	/// 
	/// -S num <br>
	/// Specify the random number seed (default 42).<p>
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2.2.1 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("This filter randomly shuffles the order of instances passed through it.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class Randomize:Filter, UnsupervisedFilter
	{
		/// <summary>The random number seed </summary>
		protected internal int m_Seed = 42;
		/// <summary>The current random number generator </summary>
		protected internal System.Random m_Random;
		
		/// <summary> Get the random number generator seed value.
		/// 
		/// </summary>
		/// <returns> random number generator seed value.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Seed for the random number generator.")  </attribute>
		/// <property>   </property>
		public virtual int get_RandomSeed()
		{
			
			return m_Seed;
		}
		
		/// <summary> Set the random number generator seed value.
		/// 
		/// </summary>
		/// <param name="newRandomSeed">value to use as the random number generator seed.
		/// </param>
		/// <property>   </property>
		public virtual void  set_RandomSeed(int newRandomSeed)
		{
			
			m_Seed = newRandomSeed;
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
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			m_Random = new System.Random((System.Int32) m_Seed);
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
		
		/// <summary> Signify that this batch of input to the filter is finished. If
		/// the filter requires all instances prior to filtering, output()
		/// may now be called to retrieve the filtered instances. Any
		/// subsequent instances filtered should be filtered based on setting
		/// obtained from the first batch (unless the setInputFormat has been
		/// re-assigned or new options have been set). This 
		/// implementation randomizes all the instances received in the batch.
		/// 
		/// </summary>
		/// <returns> true if there are instances pending output
		/// </returns>
		/// <exception cref="IllegalStateException">if no input format has been set. 
		/// </exception>
		public override bool batchFinished()
		{
			
			if (getInputFormat() == null)
			{
				throw new System.SystemException("No input instance format defined");
			}
			
			if (!m_FirstBatchDone)
			{
				getInputFormat().randomize(m_Random);
			}
			for (int i = 0; i < getInputFormat().numInstances(); i++)
			{
				push(getInputFormat().instance(i));
			}
			flushInput();
			
			m_NewBatch = true;
			m_FirstBatchDone = true;
			return (numPendingOutput() != 0);
		}
	}
}