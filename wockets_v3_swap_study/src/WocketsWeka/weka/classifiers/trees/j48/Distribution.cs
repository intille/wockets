/*
*    Distribution.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
using weka.core;
using WocketsWeka;
using System.Xml;
using System.IO;
namespace weka.classifiers.trees.j48
{
	
	/// <summary> Class for handling a distribution of class values.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8 $
	/// </version>
#if !PocketPC
    [Serializable()]  
#endif
	public class Distribution : System.ICloneable
	{


		/// <summary>Weight of instances per class per bag. </summary>
		private double[][] m_perClassPerBag;
		
		/// <summary>Weight of instances per bag. </summary>
		private double[] m_perBag;
		
		/// <summary>Weight of instances per class. </summary>
		private double[] m_perClass;
		
		/// <summary>Total weight of instances. </summary>
		private double totaL;


        public void toXML(TextWriter tw)
        {
            tw.WriteLine("<" + Constants.DISTRIBUTION + " " +
         Constants.TOTAL + "=\"" + totaL + "\"   " +
         " xmlns=\"urn:mites-schema\">\n");

            tw.WriteLine("<" + Constants.PERCLASSPERBAG + " "+Constants.XSIZE+"=\"" + m_perClassPerBag.Length + "\" "+Constants.YSIZE+"=\"" + m_perClassPerBag[0].Length + "\" >\n");
            for (int i = 0; (i < m_perClassPerBag.Length); i++)           
                for (int j = 0; (j < m_perClassPerBag[i].Length); j++)
                    tw.WriteLine("<"+Constants.VALUE+" "+Constants.I+"=\""+i+"\" "+Constants.J+"=\""+j+"\" "+Constants.VAL+"=\"" + m_perClassPerBag[i][j] + "\" />");
            tw.WriteLine("</" + Constants.PERCLASSPERBAG + ">\n");

            tw.WriteLine("<" + Constants.PERBAG + " "+Constants.XSIZE+"=\"" + m_perBag.Length + "\">\n");
            for (int i = 0; (i < m_perBag.Length); i++)
                tw.WriteLine("<"+Constants.VALUE+"  "+Constants.I+"=\"" + i + "\" "+Constants.VAL+"=\"" + m_perBag[i] + "\" />\n");            
            tw.WriteLine("</" + Constants.PERBAG + ">\n");

           tw.WriteLine("<" + Constants.PERCLASS + " " + Constants.XSIZE + "=\"" + m_perClass.Length + "\">\n");
            for (int i = 0; (i < m_perClass.Length); i++)
                tw.WriteLine("<"+Constants.VALUE+"  "+Constants.I+"=\"" + i + "\" "+Constants.VAL+"=\"" + m_perClass[i] + "\" />\n");
            tw.WriteLine("</" + Constants.PERCLASS + ">\n");

            tw.WriteLine("</" + Constants.DISTRIBUTION + ">");
       


        }

        public Distribution(XmlNode distribution)
        {
            foreach (XmlAttribute xAttribute in distribution.Attributes)
            {
                if (xAttribute.Name == Constants.TOTAL)
                    this.totaL= Convert.ToDouble(xAttribute.Value);
            }

              //Going through the subtrees
            foreach (XmlNode iNode in distribution.ChildNodes)
            {
                if (iNode.Name == Constants.PERCLASSPERBAG)
                {
                    int xsize=-1;
                    int ysize=-1;
                    foreach (XmlAttribute xAttribute in iNode.Attributes)
                    {
                        if (xAttribute.Name == Constants.XSIZE)
                            xsize = Convert.ToInt32(xAttribute.Value);
                        else if (xAttribute.Name == Constants.YSIZE)
                            ysize = Convert.ToInt32(xAttribute.Value);
                    }

                    m_perClassPerBag = new double[xsize][];
                    for (int i = 0; (i < xsize); i++)
                        m_perClassPerBag[i] = new double[ysize];

                    foreach (XmlNode jNode in iNode.ChildNodes)
                    {
                        if (jNode.Name == Constants.VALUE)
                        {
                            int i = -1;
                            int j = -1;
                            double val = -1;
                            foreach (XmlAttribute xAttribute in jNode.Attributes)
                            {
                                if (xAttribute.Name == Constants.I)
                                   i = Convert.ToInt32(xAttribute.Value);
                               else if (xAttribute.Name == Constants.J)
                                   j = Convert.ToInt32(xAttribute.Value);
                               else if (xAttribute.Name == Constants.VAL)
                                  val = Convert.ToDouble(xAttribute.Value);
                            }
                            m_perClassPerBag[i][j]=val;
                        }
                    }
                }
                else if (iNode.Name == Constants.PERBAG)
                {

                    int xsize = -1;
                    foreach (XmlAttribute xAttribute in iNode.Attributes)
                    {
                        if (xAttribute.Name == Constants.XSIZE)
                            xsize = Convert.ToInt32(xAttribute.Value);               
                    }
                    m_perBag = new double[xsize];

                    foreach (XmlNode jNode in iNode.ChildNodes)
                    {
                        if (jNode.Name == Constants.VALUE)
                        {
                            int i = -1;        
                            double val = -1;
                            foreach (XmlAttribute xAttribute in jNode.Attributes)
                            {
                                if (xAttribute.Name == Constants.I)
                                    i = Convert.ToInt32(xAttribute.Value);
                                else if (xAttribute.Name == Constants.VAL)
                                    val = Convert.ToDouble(xAttribute.Value);
                            }
                            m_perBag[i] = val;
                        }
                    }

                }
                else if (iNode.Name == Constants.PERCLASS)
                {

                    int xsize = -1;
                    foreach (XmlAttribute xAttribute in iNode.Attributes)
                    {
                        if (xAttribute.Name == Constants.XSIZE)
                            xsize = Convert.ToInt32(xAttribute.Value);
                    }
                    m_perClass = new double[xsize];

                    foreach (XmlNode jNode in iNode.ChildNodes)
                    {
                        if (jNode.Name == Constants.VALUE)
                        {
                            int i = -1;
                            double val = -1;
                            foreach (XmlAttribute xAttribute in jNode.Attributes)
                            {
                                if (xAttribute.Name == Constants.I)
                                    i = Convert.ToInt32(xAttribute.Value);
                                else if (xAttribute.Name == Constants.VAL)
                                    val = Convert.ToDouble(xAttribute.Value);
                            }
                            m_perClass[i] = val;
                        }
                    }

                }
            }
        }
		
		/// <summary> Creates and initializes a new distribution.</summary>
		public Distribution(int numBags, int numClasses)
		{
			
			int i;
			
			m_perClassPerBag = new double[numBags][];
			for (int i2 = 0; i2 < numBags; i2++)
			{
				m_perClassPerBag[i2] = new double[0];
			}
			m_perBag = new double[numBags];
			m_perClass = new double[numClasses];
			for (i = 0; i < numBags; i++)
				m_perClassPerBag[i] = new double[numClasses];
			totaL = 0;
		}
		
		/// <summary> Creates and initializes a new distribution using the given
		/// array. WARNING: it just copies a reference to this array.
		/// </summary>
		public Distribution(double[][] table)
		{
			
			int i, j;
			
			m_perClassPerBag = table;
			m_perBag = new double[table.Length];
			m_perClass = new double[table[0].Length];
			for (i = 0; i < table.Length; i++)
				for (j = 0; j < table[i].Length; j++)
				{
					m_perBag[i] += table[i][j];
					m_perClass[j] += table[i][j];
					totaL += table[i][j];
				}
		}
		
		/// <summary> Creates a distribution with only one bag according
		/// to instances in source.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public Distribution(Instances source)
		{
			
			m_perClassPerBag = new double[1][];
			for (int i = 0; i < 1; i++)
			{
				m_perClassPerBag[i] = new double[0];
			}
			m_perBag = new double[1];
			totaL = 0;
			m_perClass = new double[source.numClasses()];
			m_perClassPerBag[0] = new double[source.numClasses()];
			System.Collections.IEnumerator enu = source.enumerateInstances();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				add(0, (Instance) enu.Current);
			}
		}
		
		/// <summary> Creates a distribution according to given instances and
		/// split model.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		
		public Distribution(Instances source, ClassifierSplitModel modelToUse)
		{
			
			int index;
			Instance instance;
			double[] weights;
			
			m_perClassPerBag = new double[modelToUse.numSubsets()][];
			for (int i = 0; i < modelToUse.numSubsets(); i++)
			{
				m_perClassPerBag[i] = new double[0];
			}
			m_perBag = new double[modelToUse.numSubsets()];
			totaL = 0;
			m_perClass = new double[source.numClasses()];
			for (int i = 0; i < modelToUse.numSubsets(); i++)
				m_perClassPerBag[i] = new double[source.numClasses()];
			System.Collections.IEnumerator enu = source.enumerateInstances();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				instance = (Instance) enu.Current;
				index = modelToUse.whichSubset(instance);
				if (index != - 1)
					add(index, instance);
				else
				{
					weights = modelToUse.GetWeights(instance);
					addWeights(instance, weights);
				}
			}
		}
		
		/// <summary> Creates distribution with only one bag by merging all
		/// bags of given distribution.
		/// </summary>
		public Distribution(Distribution toMerge)
		{
			
			totaL = toMerge.totaL;
			m_perClass = new double[toMerge.numClasses()];
			Array.Copy(toMerge.m_perClass, 0, m_perClass, 0, toMerge.numClasses());
			m_perClassPerBag = new double[1][];
			for (int i = 0; i < 1; i++)
			{
				m_perClassPerBag[i] = new double[0];
			}
			m_perClassPerBag[0] = new double[toMerge.numClasses()];
			Array.Copy(toMerge.m_perClass, 0, m_perClassPerBag[0], 0, toMerge.numClasses());
			m_perBag = new double[1];
			m_perBag[0] = totaL;
		}
		
		/// <summary> Creates distribution with two bags by merging all bags apart of
		/// the indicated one.
		/// </summary>
		public Distribution(Distribution toMerge, int index)
		{
			
			int i;
			
			totaL = toMerge.totaL;
			m_perClass = new double[toMerge.numClasses()];
			Array.Copy(toMerge.m_perClass, 0, m_perClass, 0, toMerge.numClasses());
			m_perClassPerBag = new double[2][];
			for (int i2 = 0; i2 < 2; i2++)
			{
				m_perClassPerBag[i2] = new double[0];
			}
			m_perClassPerBag[0] = new double[toMerge.numClasses()];
			Array.Copy(toMerge.m_perClassPerBag[index], 0, m_perClassPerBag[0], 0, toMerge.numClasses());
			m_perClassPerBag[1] = new double[toMerge.numClasses()];
			for (i = 0; i < toMerge.numClasses(); i++)
				m_perClassPerBag[1][i] = toMerge.m_perClass[i] - m_perClassPerBag[0][i];
			m_perBag = new double[2];
			m_perBag[0] = toMerge.m_perBag[index];
			m_perBag[1] = totaL - m_perBag[0];
		}
		
		/// <summary> Returns number of non-empty bags of distribution.</summary>
		public int actualNumBags()
		{
			
			int returnValue = 0;
			int i;
			
			for (i = 0; i < m_perBag.Length; i++)
				if (Utils.gr(m_perBag[i], 0))
					returnValue++;
			
			return returnValue;
		}
		
		/// <summary> Returns number of classes actually occuring in distribution.</summary>
		public int actualNumClasses()
		{
			
			int returnValue = 0;
			int i;
			
			for (i = 0; i < m_perClass.Length; i++)
				if (Utils.gr(m_perClass[i], 0))
					returnValue++;
			
			return returnValue;
		}
		
		/// <summary> Returns number of classes actually occuring in given bag.</summary>
		public int actualNumClasses(int bagIndex)
		{
			
			int returnValue = 0;
			int i;
			
			for (i = 0; i < m_perClass.Length; i++)
				if (Utils.gr(m_perClassPerBag[bagIndex][i], 0))
					returnValue++;
			
			return returnValue;
		}
		
		/// <summary> Adds given instance to given bag.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  add(int bagIndex, Instance instance)
		{
			
			int classIndex;
			double weight;
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			classIndex = (int) instance.classValue();
			weight = instance.weight();
			m_perClassPerBag[bagIndex][classIndex] = m_perClassPerBag[bagIndex][classIndex] + weight;
			m_perBag[bagIndex] = m_perBag[bagIndex] + weight;
			m_perClass[classIndex] = m_perClass[classIndex] + weight;
			totaL = totaL + weight;
		}
		
		/// <summary> Subtracts given instance from given bag.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  sub(int bagIndex, Instance instance)
		{
			
			int classIndex;
			double weight;
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			classIndex = (int) instance.classValue();
			weight = instance.weight();
			m_perClassPerBag[bagIndex][classIndex] = m_perClassPerBag[bagIndex][classIndex] - weight;
			m_perBag[bagIndex] = m_perBag[bagIndex] - weight;
			m_perClass[classIndex] = m_perClass[classIndex] - weight;
			totaL = totaL - weight;
		}
		
		/// <summary> Adds counts to given bag.</summary>
		public void  add(int bagIndex, double[] counts)
		{
			
			double sum = Utils.sum(counts);
			
			for (int i = 0; i < counts.Length; i++)
				m_perClassPerBag[bagIndex][i] += counts[i];
			m_perBag[bagIndex] = m_perBag[bagIndex] + sum;
			for (int i = 0; i < counts.Length; i++)
				m_perClass[i] = m_perClass[i] + counts[i];
			totaL = totaL + sum;
		}
		
		/// <summary> Adds all instances with unknown values for given attribute, weighted
		/// according to frequency of instances in each bag.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  addInstWithUnknown(Instances source, int attIndex)
		{
			
			double[] probs;
			double weight, newWeight;
			int classIndex;
			Instance instance;
			int j;
			
			probs = new double[m_perBag.Length];
			for (j = 0; j < m_perBag.Length; j++)
			{
				if (Utils.eq(totaL, 0))
				{
					probs[j] = 1.0 / probs.Length;
				}
				else
				{
					probs[j] = m_perBag[j] / totaL;
				}
			}
			System.Collections.IEnumerator enu = source.enumerateInstances();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				instance = (Instance) enu.Current;
				if (instance.isMissing(attIndex))
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					classIndex = (int) instance.classValue();
					weight = instance.weight();
					m_perClass[classIndex] = m_perClass[classIndex] + weight;
					totaL = totaL + weight;
					for (j = 0; j < m_perBag.Length; j++)
					{
						newWeight = probs[j] * weight;
						m_perClassPerBag[j][classIndex] = m_perClassPerBag[j][classIndex] + newWeight;
						m_perBag[j] = m_perBag[j] + newWeight;
					}
				}
			}
		}
		
		/// <summary> Adds all instances in given range to given bag.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  addRange(int bagIndex, Instances source, int startIndex, int lastPlusOne)
		{
			
			double sumOfWeights = 0;
			int classIndex;
			Instance instance;
			int i;
			
			for (i = startIndex; i < lastPlusOne; i++)
			{
				instance = (Instance) source.instance(i);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				classIndex = (int) instance.classValue();
				sumOfWeights = sumOfWeights + instance.weight();
				m_perClassPerBag[bagIndex][classIndex] += instance.weight();
				m_perClass[classIndex] += instance.weight();
			}
			m_perBag[bagIndex] += sumOfWeights;
			totaL += sumOfWeights;
		}
		
		/// <summary> Adds given instance to all bags weighting it according to given weights.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  addWeights(Instance instance, double[] weights)
		{
			
			int classIndex;
			int i;
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			classIndex = (int) instance.classValue();
			for (i = 0; i < m_perBag.Length; i++)
			{
				double weight = instance.weight() * weights[i];
				m_perClassPerBag[i][classIndex] = m_perClassPerBag[i][classIndex] + weight;
				m_perBag[i] = m_perBag[i] + weight;
				m_perClass[classIndex] = m_perClass[classIndex] + weight;
				totaL = totaL + weight;
			}
		}
		
		/// <summary> Checks if at least two bags contain a minimum number of instances.</summary>
		public bool check(double minNoObj)
		{
			
			int counter = 0;
			int i;
			
			for (i = 0; i < m_perBag.Length; i++)
				if (Utils.grOrEq(m_perBag[i], minNoObj))
					counter++;
			if (counter > 1)
				return true;
			else
				return false;
		}
		
		/// <summary> Clones distribution (Deep copy of distribution).</summary>
		public virtual System.Object Clone()
		{
			
			int i, j;
			
			Distribution newDistribution = new Distribution(m_perBag.Length, m_perClass.Length);
			for (i = 0; i < m_perBag.Length; i++)
			{
				newDistribution.m_perBag[i] = m_perBag[i];
				for (j = 0; j < m_perClass.Length; j++)
					newDistribution.m_perClassPerBag[i][j] = m_perClassPerBag[i][j];
			}
			for (j = 0; j < m_perClass.Length; j++)
				newDistribution.m_perClass[j] = m_perClass[j];
			newDistribution.totaL = totaL;
			
			return newDistribution;
		}
		
		/// <summary> Deletes given instance from given bag.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  del(int bagIndex, Instance instance)
		{
			
			int classIndex;
			double weight;
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			classIndex = (int) instance.classValue();
			weight = instance.weight();
			m_perClassPerBag[bagIndex][classIndex] = m_perClassPerBag[bagIndex][classIndex] - weight;
			m_perBag[bagIndex] = m_perBag[bagIndex] - weight;
			m_perClass[classIndex] = m_perClass[classIndex] - weight;
			totaL = totaL - weight;
		}
		
		/// <summary> Deletes all instances in given range from given bag.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  delRange(int bagIndex, Instances source, int startIndex, int lastPlusOne)
		{
			
			double sumOfWeights = 0;
			int classIndex;
			Instance instance;
			int i;
			
			for (i = startIndex; i < lastPlusOne; i++)
			{
				instance = (Instance) source.instance(i);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				classIndex = (int) instance.classValue();
				sumOfWeights = sumOfWeights + instance.weight();
				m_perClassPerBag[bagIndex][classIndex] -= instance.weight();
				m_perClass[classIndex] -= instance.weight();
			}
			m_perBag[bagIndex] -= sumOfWeights;
			totaL -= sumOfWeights;
		}
		
		/// <summary> Prints distribution.</summary>
		
		public System.String dumpDistribution()
		{
			
			System.Text.StringBuilder text;
			int i, j;
			
			text = new System.Text.StringBuilder();
			for (i = 0; i < m_perBag.Length; i++)
			{
				text.Append("Bag num " + i + "\n");
				for (j = 0; j < m_perClass.Length; j++)
					text.Append("Class num " + j + " " + m_perClassPerBag[i][j] + "\n");
			}
			return text.ToString();
		}
		
		/// <summary> Sets all counts to zero.</summary>
		public void  initialize()
		{
			
			for (int i = 0; i < m_perClass.Length; i++)
				m_perClass[i] = 0;
			for (int i = 0; i < m_perBag.Length; i++)
				m_perBag[i] = 0;
			for (int i = 0; i < m_perBag.Length; i++)
				for (int j = 0; j < m_perClass.Length; j++)
					m_perClassPerBag[i][j] = 0;
			totaL = 0;
		}
		
		/// <summary> Returns matrix with distribution of class values.</summary>
		public double[][] matrix()
		{
			
			return m_perClassPerBag;
		}
		
		/// <summary> Returns index of bag containing maximum number of instances.</summary>
		public int maxBag()
		{
			
			double max;
			int maxIndex;
			int i;
			
			max = 0;
			maxIndex = - 1;
			for (i = 0; i < m_perBag.Length; i++)
				if (Utils.grOrEq(m_perBag[i], max))
				{
					max = m_perBag[i];
					maxIndex = i;
				}
			return maxIndex;
		}
		
		/// <summary> Returns class with highest frequency over all bags.</summary>
		public int maxClass()
		{
			
			double maxCount = 0;
			int maxIndex = 0;
			int i;
			
			for (i = 0; i < m_perClass.Length; i++)
				if (Utils.gr(m_perClass[i], maxCount))
				{
					maxCount = m_perClass[i];
					maxIndex = i;
				}
			
			return maxIndex;
		}
		
		/// <summary> Returns class with highest frequency for given bag.</summary>
		public int maxClass(int index)
		{
			
			double maxCount = 0;
			int maxIndex = 0;
			int i;
			
			if (Utils.gr(m_perBag[index], 0))
			{
				for (i = 0; i < m_perClass.Length; i++)
					if (Utils.gr(m_perClassPerBag[index][i], maxCount))
					{
						maxCount = m_perClassPerBag[index][i];
						maxIndex = i;
					}
				return maxIndex;
			}
			else
				return maxClass();
		}
		
		/// <summary> Returns number of bags.</summary>
		public int numBags()
		{
			
			return m_perBag.Length;
		}
		
		/// <summary> Returns number of classes.</summary>
		public int numClasses()
		{
			
			return m_perClass.Length;
		}
		
		/// <summary> Returns perClass(maxClass()).</summary>
		public double numCorrect()
		{
			
			return m_perClass[maxClass()];
		}
		
		/// <summary> Returns perClassPerBag(index,maxClass(index)).</summary>
		public double numCorrect(int index)
		{
			
			return m_perClassPerBag[index][maxClass(index)];
		}
		
		/// <summary> Returns total-numCorrect().</summary>
		public double numIncorrect()
		{
			
			return totaL - numCorrect();
		}
		
		/// <summary> Returns perBag(index)-numCorrect(index).</summary>
		public double numIncorrect(int index)
		{
			
			return m_perBag[index] - numCorrect(index);
		}
		
		/// <summary> Returns number of (possibly fractional) instances of given class in 
		/// given bag.
		/// </summary>
		public double perClassPerBag(int bagIndex, int classIndex)
		{
			
			return m_perClassPerBag[bagIndex][classIndex];
		}
		
		/// <summary> Returns number of (possibly fractional) instances in given bag.</summary>
		public double perBag(int bagIndex)
		{
			
			return m_perBag[bagIndex];
		}
		
		/// <summary> Returns number of (possibly fractional) instances of given class.</summary>
		public double perClass(int classIndex)
		{
			
			return m_perClass[classIndex];
		}
		
		/// <summary> Returns relative frequency of class over all bags with
		/// Laplace correction.
		/// </summary>
		public double laplaceProb(int classIndex)
		{
			
			return (m_perClass[classIndex] + 1) / (totaL + (double) actualNumClasses());
		}
		
		/// <summary> Returns relative frequency of class for given bag.</summary>
		public double laplaceProb(int classIndex, int intIndex)
		{
			
			return (m_perClassPerBag[intIndex][classIndex] + 1.0) / (m_perBag[intIndex] + (double) actualNumClasses());
		}
		
		/// <summary> Returns relative frequency of class over all bags.</summary>
		public double prob(int classIndex)
		{
			
			if (!Utils.eq(totaL, 0))
			{
				return m_perClass[classIndex] / totaL;
			}
			else
			{
				return 0;
			}
		}
		
		/// <summary> Returns relative frequency of class for given bag.</summary>
		public double prob(int classIndex, int intIndex)
		{
			
			if (Utils.gr(m_perBag[intIndex], 0))
				return m_perClassPerBag[intIndex][classIndex] / m_perBag[intIndex];
			else
				return prob(classIndex);
		}
		
		/// <summary> Subtracts the given distribution from this one. The results
		/// has only one bag.
		/// </summary>
		public Distribution subtract(Distribution toSubstract)
		{
			
			Distribution newDist = new Distribution(1, m_perClass.Length);
			
			newDist.m_perBag[0] = totaL - toSubstract.totaL;
			newDist.totaL = newDist.m_perBag[0];
			for (int i = 0; i < m_perClass.Length; i++)
			{
				newDist.m_perClassPerBag[0][i] = m_perClass[i] - toSubstract.m_perClass[i];
				newDist.m_perClass[i] = newDist.m_perClassPerBag[0][i];
			}
			return newDist;
		}
		
		/// <summary> Returns total number of (possibly fractional) instances.</summary>
		public double total()
		{
			
			return totaL;
		}
		
		/// <summary> Shifts given instance from one bag to another one.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  shift(int from, int to, Instance instance)
		{
			
			int classIndex;
			double weight;
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			classIndex = (int) instance.classValue();
			weight = instance.weight();
			m_perClassPerBag[from][classIndex] -= weight;
			m_perClassPerBag[to][classIndex] += weight;
			m_perBag[from] -= weight;
			m_perBag[to] += weight;
		}
		
		/// <summary> Shifts all instances in given range from one bag to another one.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public void  shiftRange(int from, int to, Instances source, int startIndex, int lastPlusOne)
		{
			
			int classIndex;
			double weight;
			Instance instance;
			int i;
			
			for (i = startIndex; i < lastPlusOne; i++)
			{
				instance = (Instance) source.instance(i);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				classIndex = (int) instance.classValue();
				weight = instance.weight();
				m_perClassPerBag[from][classIndex] -= weight;
				m_perClassPerBag[to][classIndex] += weight;
				m_perBag[from] -= weight;
				m_perBag[to] += weight;
			}
		}
	}
}