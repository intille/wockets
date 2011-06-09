/*    DecisionStump.java
*    Copyright (C) 1999 Eibe Frank
*/
using System;
using Classifier = weka.classifiers.Classifier;
using Evaluation = weka.classifiers.Evaluation;
using Sourcable = weka.classifiers.Sourcable;
using weka.core;
using System.IO;
namespace weka.classifiers.trees
{
	
	/// <summary> Class for building and using a decision stump. Usually used in conjunction
	/// with a boosting algorithm.
	/// 
	/// Typical usage: <p>
	/// <code>java weka.classifiers.trees.LogitBoost -I 100 -W weka.classifiers.trees.DecisionStump 
	/// -t training_data </code><p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.18 $
	/// </version>
	/// <attribute>  System.ComponentModel.DescriptionAttribute("Class for building and using a decision stump. Usually used in conjunction with a boosting algorithm.")  </attribute>
#if !PocketPC
    [Serializable]
#endif
	public class DecisionStump:Classifier, WeightedInstancesHandler, Sourcable
	{
		/// <summary>The attribute used for classification. </summary>
		private int m_AttIndex;
		/// <summary>The split point (index respectively). </summary>
		private double m_SplitPoint;
		/// <summary>The distribution of class values or the means in each subset. </summary>
		private double[][] m_Distribution;
		/// <summary>The instances used for training. </summary>
		private Instances m_Instances;

        public override void  toXML(TextWriter tw)
        {
 
        }

        public override void buildClassifier(string fileName, Instances instances)
        {
        }
		/// <summary> Generates the classifier.
		/// 
		/// </summary>
		/// <param name="instances">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the classifier has not been generated successfully
		/// </exception>
		public override void  buildClassifier(Instances instances)
		{
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double bestVal = System.Double.MaxValue, currVal;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double bestPoint = - System.Double.MaxValue, sum;
			int bestAtt = - 1, numClasses;
			
			if (instances.checkForStringAttributes())
			{
				throw new Exception("Can't handle string attributes!");
			}
			
			double[][] bestDist = new double[3][];
			for (int i = 0; i < 3; i++)
			{
				bestDist[i] = new double[instances.numClasses()];
			}
			
			m_Instances = new Instances(instances);
			m_Instances.deleteWithMissingClass();
			
			if (m_Instances.numInstances() == 0)
			{
				throw new System.ArgumentException("No instances without missing " + "class values in training file!");
			}
			
			if (instances.numAttributes() == 1)
			{
				throw new System.ArgumentException("Attribute missing. Need at least one " + "attribute other than class attribute!");
			}
			
			if (m_Instances.classAttribute().Nominal)
			{
				numClasses = m_Instances.numClasses();
			}
			else
			{
				numClasses = 1;
			}
			
			// For each attribute
			bool first = true;
			for (int i = 0; i < m_Instances.numAttributes(); i++)
			{
				if (i != m_Instances.classIndex())
				{
					
					// Reserve space for distribution.
					double[][] tmpArray = new double[3][];
					for (int i2 = 0; i2 < 3; i2++)
					{
						tmpArray[i2] = new double[numClasses];
					}
					m_Distribution = tmpArray;
					
					// Compute value of criterion for best split on attribute
					if (m_Instances.attribute(i).Nominal)
					{
						currVal = findSplitNominal(i);
					}
					else
					{
						currVal = findSplitNumeric(i);
					}
					if ((first) || (currVal < bestVal))
					{
						bestVal = currVal;
						bestAtt = i;
						bestPoint = m_SplitPoint;
						for (int j = 0; j < 3; j++)
						{
							Array.Copy(m_Distribution[j], 0, bestDist[j], 0, numClasses);
						}
					}
					
					// First attribute has been investigated
					first = false;
				}
			}
			
			// Set attribute, split point and distribution.
			m_AttIndex = bestAtt;
			m_SplitPoint = bestPoint;
			m_Distribution = bestDist;
			if (m_Instances.classAttribute().Nominal)
			{
				for (int i = 0; i < m_Distribution.Length; i++)
				{
					double sumCounts = Utils.sum(m_Distribution[i]);
					if (sumCounts == 0)
					{
						// This means there were only missing attribute values
						Array.Copy(m_Distribution[2], 0, m_Distribution[i], 0, m_Distribution[2].Length);
						Utils.normalize(m_Distribution[i]);
					}
					else
					{
						Utils.normalize(m_Distribution[i], sumCounts);
					}
				}
			}
			
			// Save memory
			m_Instances = new Instances(m_Instances, 0);
		}
		
		/// <summary> Calculates the class membership probabilities for the given test instance.
		/// 
		/// </summary>
		/// <param name="instance">the instance to be classified
		/// </param>
		/// <returns> predicted class probability distribution
		/// </returns>
		/// <exception cref="Exception">if distribution can't be computed
		/// </exception>
		public override double[] distributionForInstance(Instance instance)
		{
			
			return m_Distribution[whichSubset(instance)];
		}
		
		/// <summary> Returns the decision tree as Java source code.
		/// 
		/// </summary>
		/// <returns> the tree as Java source code
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public virtual System.String toSource(System.String className)
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder("class ");
			weka.core.Attribute c = m_Instances.classAttribute();
			text.Append(className).Append(" {\n" + "  public static double classify(Object [] i) {\n");
			text.Append("    /* " + m_Instances.attribute(m_AttIndex).name() + " */\n");
			text.Append("    if (i[").Append(m_AttIndex);
			text.Append("] == null) { return ");
			text.Append(sourceClass(c, m_Distribution[2])).Append(";");
			if (m_Instances.attribute(m_AttIndex).Nominal)
			{
				text.Append(" } else if (((String)i[").Append(m_AttIndex);
				text.Append("]).equals(\"");
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				text.Append(m_Instances.attribute(m_AttIndex).value_Renamed((int) m_SplitPoint));
				text.Append("\")");
			}
			else
			{
				text.Append(" } else if (((Double)i[").Append(m_AttIndex);
				text.Append("]).doubleValue() <= ").Append(m_SplitPoint);
			}
			text.Append(") { return ");
			text.Append(sourceClass(c, m_Distribution[0])).Append(";");
			text.Append(" } else { return ");
			text.Append(sourceClass(c, m_Distribution[1])).Append(";");
			text.Append(" }\n  }\n}\n");
			return text.ToString();
		}
		
		private System.String sourceClass(weka.core.Attribute c, double[] dist)
		{
			
			if (c.Nominal)
			{
				return System.Convert.ToString(Utils.maxIndex(dist));
			}
			else
			{
				return dist[0].ToString();
			}
		}
		
		/// <summary> Returns a description of the classifier.
		/// 
		/// </summary>
		/// <returns> a description of the classifier as a string.
		/// </returns>
		public override System.String ToString()
		{
			if (m_Instances == null)
			{
				return "Decision Stump: No model built yet.";
			}
			try
			{
				System.Text.StringBuilder text = new System.Text.StringBuilder();
				
				text.Append("Decision Stump\n\n");
				text.Append("Classifications\n\n");
				weka.core.Attribute att = m_Instances.attribute(m_AttIndex);
				if (att.Nominal)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					text.Append(att.name() + " = " + att.value_Renamed((int) m_SplitPoint) + " : ");
					text.Append(printClass(m_Distribution[0]));
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					text.Append(att.name() + " != " + att.value_Renamed((int) m_SplitPoint) + " : ");
					text.Append(printClass(m_Distribution[1]));
				}
				else
				{
					text.Append(att.name() + " <= " + m_SplitPoint + " : ");
					text.Append(printClass(m_Distribution[0]));
					text.Append(att.name() + " > " + m_SplitPoint + " : ");
					text.Append(printClass(m_Distribution[1]));
				}
				text.Append(att.name() + " is missing : ");
				text.Append(printClass(m_Distribution[2]));
				
				if (m_Instances.classAttribute().Nominal)
				{
					text.Append("\nClass distributions\n\n");
					if (att.Nominal)
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						text.Append(att.name() + " = " + att.value_Renamed((int) m_SplitPoint) + "\n");
						text.Append(printDist(m_Distribution[0]));
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						text.Append(att.name() + " != " + att.value_Renamed((int) m_SplitPoint) + "\n");
						text.Append(printDist(m_Distribution[1]));
					}
					else
					{
						text.Append(att.name() + " <= " + m_SplitPoint + "\n");
						text.Append(printDist(m_Distribution[0]));
						text.Append(att.name() + " > " + m_SplitPoint + "\n");
						text.Append(printDist(m_Distribution[1]));
					}
					text.Append(att.name() + " is missing\n");
					text.Append(printDist(m_Distribution[2]));
				}
				
				return text.ToString();
			}
			catch (System.Exception e)
			{
				return "Can't print decision stump classifier!";
			}
		}
		
		/// <summary> Prints a class distribution.
		/// 
		/// </summary>
		/// <param name="dist">the class distribution to print
		/// </param>
		/// <returns> the distribution as a string
		/// </returns>
		/// <exception cref="Exception">if distribution can't be printed
		/// </exception>
		private System.String printDist(double[] dist)
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_Instances.classAttribute().Nominal)
			{
				for (int i = 0; i < m_Instances.numClasses(); i++)
				{
					text.Append(m_Instances.classAttribute().value_Renamed(i) + "\t");
				}
				text.Append("\n");
				for (int i = 0; i < m_Instances.numClasses(); i++)
				{
					text.Append(dist[i] + "\t");
				}
				text.Append("\n");
			}
			
			return text.ToString();
		}
		
		/// <summary> Prints a classification.
		/// 
		/// </summary>
		/// <param name="dist">the class distribution
		/// </param>
		/// <returns> the classificationn as a string
		/// </returns>
		/// <exception cref="Exception">if the classification can't be printed
		/// </exception>
		private System.String printClass(double[] dist)
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_Instances.classAttribute().Nominal)
			{
				text.Append(m_Instances.classAttribute().value_Renamed(Utils.maxIndex(dist)));
			}
			else
			{
				text.Append(dist[0]);
			}
			
			return text.ToString() + "\n";
		}
		
		/// <summary> Finds best split for nominal attribute and returns value.
		/// 
		/// </summary>
		/// <param name="index">attribute index
		/// </param>
		/// <returns> value of criterion for the best split
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double findSplitNominal(int index)
		{
			
			if (m_Instances.classAttribute().Nominal)
			{
				return findSplitNominalNominal(index);
			}
			else
			{
				return findSplitNominalNumeric(index);
			}
		}
		
		/// <summary> Finds best split for nominal attribute and nominal class
		/// and returns value.
		/// 
		/// </summary>
		/// <param name="index">attribute index
		/// </param>
		/// <returns> value of criterion for the best split
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double findSplitNominalNominal(int index)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double bestVal = System.Double.MaxValue, currVal;
			double[][] counts = new double[m_Instances.attribute(index).numValues() + 1][];
			for (int i = 0; i < m_Instances.attribute(index).numValues() + 1; i++)
			{
				counts[i] = new double[m_Instances.numClasses()];
			}
			double[] sumCounts = new double[m_Instances.numClasses()];
			double[][] bestDist = new double[3][];
			for (int i2 = 0; i2 < 3; i2++)
			{
				bestDist[i2] = new double[m_Instances.numClasses()];
			}
			int numMissing = 0;
			
			// Compute counts for all the values
			for (int i = 0; i < m_Instances.numInstances(); i++)
			{
				Instance inst = m_Instances.instance(i);
				if (inst.isMissing(index))
				{
					numMissing++;
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					counts[m_Instances.attribute(index).numValues()][(int) inst.classValue()] += inst.weight();
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					counts[(int) inst.value_Renamed(index)][(int) inst.classValue()] += inst.weight();
				}
			}
			
			// Compute sum of counts
			for (int i = 0; i < m_Instances.attribute(index).numValues(); i++)
			{
				for (int j = 0; j < m_Instances.numClasses(); j++)
				{
					sumCounts[j] += counts[i][j];
				}
			}
			
			// Make split counts for each possible split and evaluate
			Array.Copy(counts[m_Instances.attribute(index).numValues()], 0, m_Distribution[2], 0, m_Instances.numClasses());
			for (int i = 0; i < m_Instances.attribute(index).numValues(); i++)
			{
				for (int j = 0; j < m_Instances.numClasses(); j++)
				{
					m_Distribution[0][j] = counts[i][j];
					m_Distribution[1][j] = sumCounts[j] - counts[i][j];
				}
				currVal = ContingencyTables.entropyConditionedOnRows(m_Distribution);
				if (currVal < bestVal)
				{
					bestVal = currVal;
					m_SplitPoint = (double) i;
					for (int j = 0; j < 3; j++)
					{
						Array.Copy(m_Distribution[j], 0, bestDist[j], 0, m_Instances.numClasses());
					}
				}
			}
			
			// No missing values in training data.
			if (numMissing == 0)
			{
				Array.Copy(sumCounts, 0, bestDist[2], 0, m_Instances.numClasses());
			}
			
			m_Distribution = bestDist;
			return bestVal;
		}
		
		/// <summary> Finds best split for nominal attribute and numeric class
		/// and returns value.
		/// 
		/// </summary>
		/// <param name="index">attribute index
		/// </param>
		/// <returns> value of criterion for the best split
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double findSplitNominalNumeric(int index)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double bestVal = System.Double.MaxValue, currVal;
			double[] sumsSquaresPerValue = new double[m_Instances.attribute(index).numValues()], sumsPerValue = new double[m_Instances.attribute(index).numValues()], weightsPerValue = new double[m_Instances.attribute(index).numValues()];
			double totalSumSquaresW = 0, totalSumW = 0, totalSumOfWeightsW = 0, totalSumOfWeights = 0, totalSum = 0;
			double[] sumsSquares = new double[3], sumOfWeights = new double[3];
			double[][] bestDist = new double[3][];
			for (int i = 0; i < 3; i++)
			{
				bestDist[i] = new double[1];
			}
			
			// Compute counts for all the values
			for (int i = 0; i < m_Instances.numInstances(); i++)
			{
				Instance inst = m_Instances.instance(i);
				if (inst.isMissing(index))
				{
					m_Distribution[2][0] += inst.classValue() * inst.weight();
					sumsSquares[2] += inst.classValue() * inst.classValue() * inst.weight();
					sumOfWeights[2] += inst.weight();
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					weightsPerValue[(int) inst.value_Renamed(index)] += inst.weight();
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					sumsPerValue[(int) inst.value_Renamed(index)] += inst.classValue() * inst.weight();
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					sumsSquaresPerValue[(int) inst.value_Renamed(index)] += inst.classValue() * inst.classValue() * inst.weight();
				}
				totalSumOfWeights += inst.weight();
				totalSum += inst.classValue() * inst.weight();
			}
			
			// Check if the total weight is zero
			if (totalSumOfWeights <= 0)
			{
				return bestVal;
			}
			
			// Compute sum of counts without missing ones
			for (int i = 0; i < m_Instances.attribute(index).numValues(); i++)
			{
				totalSumOfWeightsW += weightsPerValue[i];
				totalSumSquaresW += sumsSquaresPerValue[i];
				totalSumW += sumsPerValue[i];
			}
			
			// Make split counts for each possible split and evaluate
			for (int i = 0; i < m_Instances.attribute(index).numValues(); i++)
			{
				
				m_Distribution[0][0] = sumsPerValue[i];
				sumsSquares[0] = sumsSquaresPerValue[i];
				sumOfWeights[0] = weightsPerValue[i];
				m_Distribution[1][0] = totalSumW - sumsPerValue[i];
				sumsSquares[1] = totalSumSquaresW - sumsSquaresPerValue[i];
				sumOfWeights[1] = totalSumOfWeightsW - weightsPerValue[i];
				
				currVal = variance(m_Distribution, sumsSquares, sumOfWeights);
				
				if (currVal < bestVal)
				{
					bestVal = currVal;
					m_SplitPoint = (double) i;
					for (int j = 0; j < 3; j++)
					{
						if (sumOfWeights[j] > 0)
						{
							bestDist[j][0] = m_Distribution[j][0] / sumOfWeights[j];
						}
						else
						{
							bestDist[j][0] = totalSum / totalSumOfWeights;
						}
					}
				}
			}
			
			m_Distribution = bestDist;
			return bestVal;
		}
		
		/// <summary> Finds best split for numeric attribute and returns value.
		/// 
		/// </summary>
		/// <param name="index">attribute index
		/// </param>
		/// <returns> value of criterion for the best split
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double findSplitNumeric(int index)
		{
			
			if (m_Instances.classAttribute().Nominal)
			{
				return findSplitNumericNominal(index);
			}
			else
			{
				return findSplitNumericNumeric(index);
			}
		}
		
		/// <summary> Finds best split for numeric attribute and nominal class
		/// and returns value.
		/// 
		/// </summary>
		/// <param name="index">attribute index
		/// </param>
		/// <returns> value of criterion for the best split
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double findSplitNumericNominal(int index)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double bestVal = System.Double.MaxValue, currVal, currCutPoint;
			int numMissing = 0;
			double[] sum = new double[m_Instances.numClasses()];
			double[][] bestDist = new double[3][];
			for (int i = 0; i < 3; i++)
			{
				bestDist[i] = new double[m_Instances.numClasses()];
			}
			
			// Compute counts for all the values
			for (int i = 0; i < m_Instances.numInstances(); i++)
			{
				Instance inst = m_Instances.instance(i);
				if (!inst.isMissing(index))
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_Distribution[1][(int) inst.classValue()] += inst.weight();
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_Distribution[2][(int) inst.classValue()] += inst.weight();
					numMissing++;
				}
			}
			Array.Copy(m_Distribution[1], 0, sum, 0, m_Instances.numClasses());
			
			// Save current distribution as best distribution
			for (int j = 0; j < 3; j++)
			{
				Array.Copy(m_Distribution[j], 0, bestDist[j], 0, m_Instances.numClasses());
			}
			
			// Sort instances
			m_Instances.sort(index);
			
			// Make split counts for each possible split and evaluate
			for (int i = 0; i < m_Instances.numInstances() - (numMissing + 1); i++)
			{
				Instance inst = m_Instances.instance(i);
				Instance instPlusOne = m_Instances.instance(i + 1);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				m_Distribution[0][(int) inst.classValue()] += inst.weight();
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				m_Distribution[1][(int) inst.classValue()] -= inst.weight();
				if (inst.value_Renamed(index) < instPlusOne.value_Renamed(index))
				{
					currCutPoint = (inst.value_Renamed(index) + instPlusOne.value_Renamed(index)) / 2.0;
					currVal = ContingencyTables.entropyConditionedOnRows(m_Distribution);
					if (currVal < bestVal)
					{
						m_SplitPoint = currCutPoint;
						bestVal = currVal;
						for (int j = 0; j < 3; j++)
						{
							Array.Copy(m_Distribution[j], 0, bestDist[j], 0, m_Instances.numClasses());
						}
					}
				}
			}
			
			// No missing values in training data.
			if (numMissing == 0)
			{
				Array.Copy(sum, 0, bestDist[2], 0, m_Instances.numClasses());
			}
			
			m_Distribution = bestDist;
			return bestVal;
		}
		
		/// <summary> Finds best split for numeric attribute and numeric class
		/// and returns value.
		/// 
		/// </summary>
		/// <param name="index">attribute index
		/// </param>
		/// <returns> value of criterion for the best split
		/// </returns>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private double findSplitNumericNumeric(int index)
		{
			
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double bestVal = System.Double.MaxValue, currVal, currCutPoint;
			int numMissing = 0;
			double[] sumsSquares = new double[3], sumOfWeights = new double[3];
			double[][] bestDist = new double[3][];
			for (int i = 0; i < 3; i++)
			{
				bestDist[i] = new double[1];
			}
			double totalSum = 0, totalSumOfWeights = 0;
			
			// Compute counts for all the values
			for (int i = 0; i < m_Instances.numInstances(); i++)
			{
				Instance inst = m_Instances.instance(i);
				if (!inst.isMissing(index))
				{
					m_Distribution[1][0] += inst.classValue() * inst.weight();
					sumsSquares[1] += inst.classValue() * inst.classValue() * inst.weight();
					sumOfWeights[1] += inst.weight();
				}
				else
				{
					m_Distribution[2][0] += inst.classValue() * inst.weight();
					sumsSquares[2] += inst.classValue() * inst.classValue() * inst.weight();
					sumOfWeights[2] += inst.weight();
					numMissing++;
				}
				totalSumOfWeights += inst.weight();
				totalSum += inst.classValue() * inst.weight();
			}
			
			// Check if the total weight is zero
			if (totalSumOfWeights <= 0)
			{
				return bestVal;
			}
			
			// Sort instances
			m_Instances.sort(index);
			
			// Make split counts for each possible split and evaluate
			for (int i = 0; i < m_Instances.numInstances() - (numMissing + 1); i++)
			{
				Instance inst = m_Instances.instance(i);
				Instance instPlusOne = m_Instances.instance(i + 1);
				m_Distribution[0][0] += inst.classValue() * inst.weight();
				sumsSquares[0] += inst.classValue() * inst.classValue() * inst.weight();
				sumOfWeights[0] += inst.weight();
				m_Distribution[1][0] -= inst.classValue() * inst.weight();
				sumsSquares[1] -= inst.classValue() * inst.classValue() * inst.weight();
				sumOfWeights[1] -= inst.weight();
				if (inst.value_Renamed(index) < instPlusOne.value_Renamed(index))
				{
					currCutPoint = (inst.value_Renamed(index) + instPlusOne.value_Renamed(index)) / 2.0;
					currVal = variance(m_Distribution, sumsSquares, sumOfWeights);
					if (currVal < bestVal)
					{
						m_SplitPoint = currCutPoint;
						bestVal = currVal;
						for (int j = 0; j < 3; j++)
						{
							if (sumOfWeights[j] > 0)
							{
								bestDist[j][0] = m_Distribution[j][0] / sumOfWeights[j];
							}
							else
							{
								bestDist[j][0] = totalSum / totalSumOfWeights;
							}
						}
					}
				}
			}
			
			m_Distribution = bestDist;
			return bestVal;
		}
		
		/// <summary> Computes variance for subsets.</summary>
		private double variance(double[][] s, double[] sS, double[] sumOfWeights)
		{
			
			double var = 0;
			
			for (int i = 0; i < s.Length; i++)
			{
				if (sumOfWeights[i] > 0)
				{
					var += sS[i] - ((s[i][0] * s[i][0]) / (double) sumOfWeights[i]);
				}
			}
			
			return var;
		}
		
		/// <summary> Returns the subset an instance falls into.</summary>
		private int whichSubset(Instance instance)
		{
			
			if (instance.isMissing(m_AttIndex))
			{
				return 2;
			}
			else if (instance.attribute(m_AttIndex).Nominal)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if ((int) instance.value_Renamed(m_AttIndex) == m_SplitPoint)
				{
					return 0;
				}
				else
				{
					return 1;
				}
			}
			else
			{
				if (instance.value_Renamed(m_AttIndex) <= m_SplitPoint)
				{
					return 0;
				}
				else
				{
					return 1;
				}
			}
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{
			return null;
		}
	}
}