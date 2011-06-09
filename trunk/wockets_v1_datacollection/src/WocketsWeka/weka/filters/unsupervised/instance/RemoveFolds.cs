/*
*    RemoveFolds.java
*    Copyright (C) 1999 Eibe Frank
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
	
	/// <summary> This filter takes a dataset and outputs a specified fold for cross validation.
	/// If you want the folds to be stratified use the supervised version.
	/// 
	/// Valid options are: <p>
	/// 
	/// -V <br>
	/// Specifies if inverse of selection is to be output.<p>
	/// 
	/// -N number of folds <br>
	/// Specifies number of folds dataset is split into (default 10). <p>
	/// 
	/// -F fold <br>
	/// Specifies which fold is selected. (default 1)<p>
	/// 
	/// -S seed <br>
	/// Specifies a random number seed for shuffling the dataset.
	/// (default 0, don't randomize)<p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.1.2.1 $ 
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("This filter takes a dataset and outputs a specified fold for cross validation.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class RemoveFolds:Filter, UnsupervisedFilter
	{
		/// <summary>Indicates if inverse of selection is to be output. </summary>
		private bool m_Inverse = false;
		/// <summary>Number of folds to split dataset into </summary>
		private int m_NumFolds = 10;
		/// <summary>Fold to output </summary>
		private int m_Fold = 1;
		/// <summary>Random number seed. </summary>
		private long m_Seed = 0;
		
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
		
		
		/// <summary> Gets the number of folds in which dataset is to be split into.
		/// 
		/// </summary>
		/// <returns> the number of folds the dataset is to be split into.
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The number of folds to split the dataset into.")  </attribute>
		/// <property>   </property>
		public virtual int get_NumFolds()
		{
			
			return m_NumFolds;
		}
		
		/// <summary> Sets the number of folds the dataset is split into. If the number
		/// of folds is zero, it won't split it into folds. 
		/// 
		/// </summary>
		/// <param name="numFolds">number of folds dataset is to be split into
		/// </param>
		/// <exception cref="IllegalArgumentException">if number of folds is negative
		/// </exception>
		/// <property>   </property>
		public virtual void  set_NumFolds(int numFolds)
		{
			
			if (numFolds < 0)
			{
				throw new System.ArgumentException("Number of folds has to be positive or zero.");
			}
			m_NumFolds = numFolds;
		}
		
		
		/// <summary> Gets the fold which is selected.
		/// 
		/// </summary>
		/// <returns> the fold which is selected
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("The fold which is selected.")  </attribute>
		/// <property>   </property>
		public virtual int get_Fold()
		{
			
			return m_Fold;
		}
		
		/// <summary> Selects a fold.
		/// 
		/// </summary>
		/// <param name="fold">the fold to be selected.
		/// </param>
		/// <exception cref="IllegalArgumentException">if fold's index is smaller than 1
		/// </exception>
		/// <property>   </property>
		public virtual void  set_Fold(int fold)
		{
			
			if (fold < 1)
			{
				throw new System.ArgumentException("Fold's index has to be greater than 0.");
			}
			m_Fold = fold;
		}
		
		
		/// <summary> Gets the random number seed used for shuffling the dataset.
		/// 
		/// </summary>
		/// <returns> the random number seed
		/// </returns>
		/// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
		/// <attribute>  System.ComponentModel.DescriptionAttribute("the random number seed for shuffling the dataset. If seed is negative, shuffling will not be performed.")  </attribute>
		/// <property>   </property>
		public virtual long get_Seed()
		{
			
			return m_Seed;
		}
		
		/// <summary> Sets the random number seed for shuffling the dataset. If seed
		/// is negative, shuffling won't be performed.
		/// 
		/// </summary>
		/// <param name="seed">the random number seed
		/// </param>
		/// <property>   </property>
		public virtual void  set_Seed(long seed)
		{
			
			m_Seed = seed;
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
			
			if ((m_NumFolds > 0) && (m_NumFolds < m_Fold))
			{
				throw new System.ArgumentException("Fold has to be smaller or equal to " + "number of folds.");
			}
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
			
			Instances instances;
			
			// Select out a fold
			if (!m_FirstBatchDone)
			{
				if (m_Seed > 0)
				{
					// User has provided a random number seed.
					//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
					getInputFormat().randomize(new System.Random((System.Int32) m_Seed));
				}
				
				if (!m_Inverse)
				{
					instances = getInputFormat().testCV(m_NumFolds, m_Fold - 1);
				}
				else
				{
					instances = getInputFormat().trainCV(m_NumFolds, m_Fold - 1);
				}
			}
			else
			{
				instances = getInputFormat();
			}
			
			flushInput();
			
			for (int i = 0; i < instances.numInstances(); i++)
			{
				push(instances.instance(i));
			}
			
			m_NewBatch = true;
			m_FirstBatchDone = true;
			return (numPendingOutput() != 0);
		}
	}
}