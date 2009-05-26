/*
*    Resample.java
*    Copyright (C) 2002 University of Waikato
*/
using System;
using weka.filters;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
using Utils = weka.core.Utils;
namespace weka.filters.unsupervised.instance
{
	
	/// <summary> Produces a random subsample of a dataset using sampling with
	/// replacement. The original dataset must fit entirely in memory. The
	/// number of instances in the generated dataset may be specified. When
	/// used in batch mode, subsequent batches are <b>not</b> resampled.
	/// 
	/// Valid options are:<p>
	/// 
	/// -S num <br>
	/// Specify the random number seed (default 1).<p>
	/// 
	/// -Z percent <br>
	/// Specify the size of the output dataset, as a percentage of the input
	/// dataset (default 100). <p>
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.4.2.1 $ 
	/// 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Produces a random subsample of a dataset using sampling with replacement.")  </attribute>

#if !PocketPC    
    [Serializable]
#endif
	public class Resample:Filter, UnsupervisedFilter
	{
		/// <summary>The subsample size, percent of original set, default 100% </summary>
		private double m_SampleSizePercent = 100;
		/// <summary>The random number generator seed </summary>
		private int m_RandomSeed = 1;
		
		
		/// <summary> Gets the random number seed.
		/// 
		/// </summary>
		/// <returns> the random number seed.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The seed used for random sampling.")  </attribute>
		/// <property>   </property>
		public virtual int get_RandomSeed()
		{
			
			return m_RandomSeed;
		}
		
		/// <summary> Sets the random number seed.
		/// 
		/// </summary>
		/// <param name="newSeed">the new random number seed.
		/// </param>
		/// <property>   </property>
		public virtual void  set_RandomSeed(int newSeed)
		{
			
			m_RandomSeed = newSeed;
		}
		
		
		
		/// <summary> Gets the subsample size as a percentage of the original set.
		/// 
		/// </summary>
		/// <returns> the subsample size
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("Size of the subsample as a percentage of the original dataset.")  </attribute>
		/// <property>   </property>
		public virtual double get_SampleSizePercent()
		{
			
			return m_SampleSizePercent;
		}
		
		/// <summary> Sets the size of the subsample, as a percentage of the original set.
		/// 
		/// </summary>
		/// <param name="newSampleSizePercent">the subsample set size, between 0 and 100.
		/// </param>
		/// <property>   </property>
		public virtual void  set_SampleSizePercent(double newSampleSizePercent)
		{
			
			m_SampleSizePercent = newSampleSizePercent;
		}
		
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
		/// <exception cref="IllegalStateException">if no input structure has been defined
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
		
		/// <summary> Signify that this batch of input to the filter is finished. 
		/// If the filter requires all instances prior to filtering,
		/// output() may now be called to retrieve the filtered instances.
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
				// Do the subsample, and clear the input instances.
				createSubsample();
			}
			flushInput();
			
			m_NewBatch = true;
			m_FirstBatchDone = true;
			return (numPendingOutput() != 0);
		}
		
		/// <summary> Creates a subsample of the current set of input instances. The output
		/// instances are pushed onto the output queue for collection.
		/// </summary>
		private void  createSubsample()
		{
			
			int origSize = getInputFormat().numInstances();
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			int sampleSize = (int) (origSize * m_SampleSizePercent / 100);
			
			// Simple subsample
			
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random random = new System.Random((System.Int32) m_RandomSeed);
			// Convert pending input instances
			for (int i = 0; i < sampleSize; i++)
			{
				int index = random.Next(origSize);
				push((Instance) getInputFormat().instance(index).copy());
			}
		}
	}
}