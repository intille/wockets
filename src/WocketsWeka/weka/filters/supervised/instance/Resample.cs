/*
*    Resample.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
using weka.filters;
using Instance = weka.core.Instance;
using Instances = weka.core.Instances;
using Option = weka.core.Option;
using Utils = weka.core.Utils;
namespace weka.filters.supervised.instance
{

    /// <summary> Produces a random subsample of a dataset using sampling with
    /// replacement. The original dataset must fit entirely in memory. The
    /// number of instances in the generated dataset may be specified. The
    /// dataset must have a nominal class attribute. If not, use the
    /// unsupervised version. The filter can be made to maintain the class
    /// distribution in the subsample, or to bias the class distribution
    /// toward a uniform distribution. When used in batch mode, subsequent
    /// batches are <b>not</b> resampled.
    /// 
    /// Valid options are:<p>
    /// 
    /// -S num <br>
    /// Specify the random number seed (default 1).<p>
    /// 
    /// -B num <br>
    /// Specify a bias towards uniform class distribution. 0 = distribution
    /// in input data, 1 = uniform class distribution (default 0). <p>
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
    [Serializable]
    public class Resample : Filter, SupervisedFilter
    {
        /// <summary>The subsample size, percent of original set, default 100% </summary>
        private double m_SampleSizePercent = 100;
        /// <summary>The random number generator seed </summary>
        private int m_RandomSeed = 1;
        /// <summary>The degree of bias towards uniform (nominal) class distribution </summary>
        private double m_BiasToUniformClass = 0;

        /// <summary> Gets the bias towards a uniform class. A value of 0 leaves the class
        /// distribution as-is, a value of 1 ensures the class distributions are
        /// uniform in the output data.
        /// 
        /// </summary>
        /// <returns> the current bias
        /// </returns>
        /// <attribute>  System.ComponentModel.DefaultValueAttribute(0)  </attribute>
        /// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
        /// <attribute>  System.ComponentModel.DescriptionAttribute("Whether to use bias towards a uniform class. A value of 0 leaves the class distribution as-is, a value of 1 ensures the class distribution is uniform in the output data.")  </attribute>
        /// <property>   </property>
        public virtual double get_BiasToUniformClass()
        {

            return m_BiasToUniformClass;
        }

        /// <summary> Sets the bias towards a uniform class. A value of 0 leaves the class
        /// distribution as-is, a value of 1 ensures the class distributions are
        /// uniform in the output data.
        /// 
        /// </summary>
        /// <param name="newBiasToUniformClass">the new bias value, between 0 and 1.
        /// </param>
        /// <property>   </property>
        public virtual void set_BiasToUniformClass(double newBiasToUniformClass)
        {
            m_BiasToUniformClass = newBiasToUniformClass;
        }


        /// <summary> Gets the random number seed.
        /// 
        /// </summary>
        /// <returns> the random number seed.
        /// </returns>
        /// <attribute>  System.ComponentModel.DefaultValueAttribute(1)  </attribute>
        /// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
        /// <attribute>  System.ComponentModel.DescriptionAttribute("Sets the random number seed for subsampling.")  </attribute>
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
        public virtual void set_RandomSeed(int newSeed)
        {

            m_RandomSeed = newSeed;
        }


        /// <summary> Gets the subsample size as a percentage of the original set.
        /// 
        /// </summary>
        /// <returns> the subsample size
        /// </returns>
        /// <attribute>  System.ComponentModel.DefaultValueAttribute(100)  </attribute>
        /// <attribute>  System.ComponentModel.CategoryAttribute("Behavior")  </attribute>
        /// <attribute>  System.ComponentModel.DescriptionAttribute("The subsample size as a percentage of the original set.")  </attribute>
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
        public virtual void set_SampleSizePercent(double newSampleSizePercent)
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

            if (instanceInfo.classIndex() < 0 || !instanceInfo.classAttribute().Nominal)
            {
                throw new System.ArgumentException("Supervised resample requires nominal class");
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
        private void createSubsample()
        {

            int origSize = getInputFormat().numInstances();
            //UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
            int sampleSize = (int)(origSize * m_SampleSizePercent / 100);

            // Subsample that takes class distribution into consideration

            // Sort according to class attribute.
            getInputFormat().sort(getInputFormat().classIndex());

            // Create an index of where each class value starts
            int[] classIndices = new int[getInputFormat().numClasses() + 1];
            int currentClass = 0;
            classIndices[currentClass] = 0;
            for (int i = 0; i < getInputFormat().numInstances(); i++)
            {
                Instance current = getInputFormat().instance(i);
                if (current.classIsMissing())
                {
                    for (int j = currentClass + 1; j < classIndices.Length; j++)
                    {
                        classIndices[j] = i;
                    }
                    break;
                }
                else if (current.classValue() != currentClass)
                {
                    for (int j = currentClass + 1; j <= current.classValue(); j++)
                    {
                        classIndices[j] = i;
                    }
                    //UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
                    currentClass = (int)current.classValue();
                }
            }
            if (currentClass <= getInputFormat().numClasses())
            {
                for (int j = currentClass + 1; j < classIndices.Length; j++)
                {
                    classIndices[j] = getInputFormat().numInstances();
                }
            }

            int actualClasses = 0;
            for (int i = 0; i < classIndices.Length - 1; i++)
            {
                if (classIndices[i] != classIndices[i + 1])
                {
                    actualClasses++;
                }
            }
            // Create the new sample

            //UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
            System.Random random = new System.Random((System.Int32)m_RandomSeed);
            // Convert pending input instances
            for (int i = 0; i < sampleSize; i++)
            {
                int index = 0;
                if (random.NextDouble() < m_BiasToUniformClass)
                {
                    // Pick a random class (of those classes that actually appear)
                    int cIndex = random.Next(actualClasses);
                    for (int j = 0, k = 0; j < classIndices.Length - 1; j++)
                    {
                        if ((classIndices[j] != classIndices[j + 1]) && (k++ >= cIndex))
                        {
                            // Pick a random instance of the designated class
                            index = classIndices[j] + random.Next(classIndices[j + 1] - classIndices[j]);
                            break;
                        }
                    }
                }
                else
                {
                    index = random.Next(origSize);
                }
                push((Instance)getInputFormat().instance(index).copy());
            }
        }


        /// <summary> Main method for testing this class.
        /// 
        /// </summary>
        /// <param name="argv">should contain arguments to the filter: 
        /// use -h for help
        /// </param>
        //	public static void main(String [] argv) 
        //	{
        //		try 
        //		{
        //			if (Utils.getFlag('b', argv)) 
        //			{
        //				Filter.batchFilterFile(new Resample(), argv);
        //			} 
        //			else 
        //			{
        //				Filter.filterFile(new Resample(), argv);
        //			}
        //		} 
        //		catch (Exception ex) 
        //		{
        //			System.out.println(ex.getMessage());
        //		}
        //	}
    }
}