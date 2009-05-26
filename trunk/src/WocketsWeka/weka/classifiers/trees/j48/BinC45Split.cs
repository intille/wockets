/*
*    BinC45Split.java
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
	
	/// <summary> Class implementing a binary C4.5-like split on an attribute.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.9.2.1 $
	/// </version>
	
	public class BinC45Split:ClassifierSplitModel
	{
		/// <summary> Sets split point to greatest value in given data smaller or equal to
		/// old split point.
		/// (C4.5 does this for some strange reason).
		/// </summary>
		virtual public Instances SplitPoint
		{
			set
			{
				
				//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				double newSplitPoint = - System.Double.MaxValue;
				double tempValue;
				Instance instance;
				
				if ((!value.attribute(m_attIndex).Nominal) && (m_numSubsets > 1))
				{
					System.Collections.IEnumerator enu = value.enumerateInstances();
					//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
					while (enu.MoveNext())
					{
						//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
						instance = (Instance) enu.Current;
						if (!instance.isMissing(m_attIndex))
						{
							tempValue = instance.value_Renamed(m_attIndex);
							if (Utils.gr(tempValue, newSplitPoint) && Utils.smOrEq(tempValue, m_splitPoint))
								newSplitPoint = tempValue;
						}
					}
					m_splitPoint = newSplitPoint;
				}
			}
			
		}
		
		/// <summary>Attribute to split on. </summary>
		private int m_attIndex;
		
		/// <summary>Minimum number of objects in a split.   </summary>
		private int m_minNoObj;
		
		/// <summary>Value of split point. </summary>
		private double m_splitPoint;
		
		/// <summary>InfoGain of split. </summary>
		private double m_infoGain;
		
		/// <summary>GainRatio of split.  </summary>
		private double m_gainRatio;
		
		/// <summary>The sum of the weights of the instances. </summary>
		private double m_sumOfWeights;
		
		/// <summary>Static reference to splitting criterion. </summary>
		private static InfoGainSplitCrit m_infoGainCrit = new InfoGainSplitCrit();
		
		/// <summary>Static reference to splitting criterion. </summary>
		private static GainRatioSplitCrit m_gainRatioCrit = new GainRatioSplitCrit();
        
        //public const string BINC45SPLIT_ELEMENT = "BinC45Split";
        //public const string ATTRIBUTE_SPLITON_ATTRIBUTE = "AttributeIndex";
        //public const string MIN_NO_OBJ_ATTRIBUTE = "MinNoObject";
        //public const string SPLIT_POINT_ATTRIBUTE = "SplitPoint";
        //public const string INFO_GAIN_ATTRIBUTE = "InfoGain";
        //public const string GAIN_RATIO_ATTRIBUTE = "GainRation";
        //public const string SUM_WEIGHTS_ATTRIBUTE = "SumWeights";
        public override void toXML(TextWriter tw)
        {
            tw.WriteLine("<" + Constants.BINC45SPLIT_ELEMENT+ " " +
            Constants.ATTRIBUTE_SPLITON_ATTRIBUTE+ "=\"" + this.m_attIndex+ "\"   " +
            Constants.MIN_NO_OBJ_ATTRIBUTE + "=\"" + this.m_minNoObj+ "\"   " +
            Constants.SPLIT_POINT_ATTRIBUTE + "=\"" + this.m_splitPoint + "\"   " +
            Constants.INFO_GAIN_ATTRIBUTE + "=\"" + this.m_infoGain + "\"   " +
            Constants.GAIN_RATIO_ATTRIBUTE + "=\"" + this.m_gainRatio+ "\"   " +
            Constants.SUM_WEIGHTS_ATTRIBUTE+ "=\"" + this.m_sumOfWeights + "\"   " +
            Constants.NUM_SUBSETS_ATTRIBUTE + "=\"" + this.m_numSubsets + "\"   " +
            " xmlns=\"urn:mites-schema\">\n");
            this.m_distribution.toXML(tw);
            tw.WriteLine("</" + Constants.BINC45SPLIT_ELEMENT+ ">");         

        }

        public BinC45Split(XmlNode split)
        {
            foreach (XmlAttribute xAttribute in split.Attributes)
            {
                if (xAttribute.Name == Constants.NUM_SUBSETS_ATTRIBUTE)
                    this.m_numSubsets = Convert.ToInt32(xAttribute.Value);
                else if (xAttribute.Name == Constants.SUM_WEIGHTS_ATTRIBUTE)
                    this.m_sumOfWeights = Convert.ToDouble(xAttribute.Value);
                else if (xAttribute.Name == Constants.GAIN_RATIO_ATTRIBUTE)
                    this.m_gainRatio = Convert.ToDouble(xAttribute.Value);
                else if (xAttribute.Name == Constants.INFO_GAIN_ATTRIBUTE)
                    this.m_infoGain = Convert.ToDouble(xAttribute.Value);
                else if (xAttribute.Name == Constants.SPLIT_POINT_ATTRIBUTE)
                    this.m_splitPoint = Convert.ToDouble(xAttribute.Value);
                else if (xAttribute.Name == Constants.MIN_NO_OBJ_ATTRIBUTE)
                    this.m_minNoObj = Convert.ToInt32(xAttribute.Value);
                else if (xAttribute.Name == Constants.ATTRIBUTE_SPLITON_ATTRIBUTE)
                    this.m_attIndex = Convert.ToInt32(xAttribute.Value);

            }
            foreach (XmlNode iNode in split.ChildNodes)
            {
                if (iNode.Name == Constants.DISTRIBUTION)
                    this.m_distribution = new Distribution(iNode);
            }
        }

		/// <summary> Initializes the split model.</summary>
		public BinC45Split(int attIndex, int minNoObj, double sumOfWeights)
		{
			
			// Get index of attribute to split on.
			m_attIndex = attIndex;
			
			// Set minimum number of objects.
			m_minNoObj = minNoObj;
			
			// Set sum of weights;
			m_sumOfWeights = sumOfWeights;
		}
		
		/// <summary> Creates a C4.5-type split on the given data.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public override void  buildClassifier(Instances trainInstances)
		{
			
			// Initialize the remaining instance variables.
			m_numSubsets = 0;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			m_splitPoint = System.Double.MaxValue;
			m_infoGain = 0;
			m_gainRatio = 0;
			
			// Different treatment for enumerated and numeric
			// attributes.
			if (trainInstances.attribute(m_attIndex).Nominal)
			{
				handleEnumeratedAttribute(trainInstances);
			}
			else
			{
				trainInstances.sort(trainInstances.attribute(m_attIndex));
				handleNumericAttribute(trainInstances);
			}
		}
		
		/// <summary> Returns index of attribute for which split was generated.</summary>
		public int attIndex()
		{
			
			return m_attIndex;
		}
		
		/// <summary> Returns (C4.5-type) gain ratio for the generated split.</summary>
		public double gainRatio()
		{
			return m_gainRatio;
		}
		
		/// <summary> Gets class probability for instance.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		public override double classProb(int classIndex, Instance instance, int theSubset)
		{
			
			if (theSubset <= - 1)
			{
				double[] weights = GetWeights(instance);
				if (weights == null)
				{
					return m_distribution.prob(classIndex);
				}
				else
				{
					double prob = 0;
					for (int i = 0; i < weights.Length; i++)
					{
						prob += weights[i] * m_distribution.prob(classIndex, i);
					}
					return prob;
				}
			}
			else
			{
				if (Utils.gr(m_distribution.perBag(theSubset), 0))
				{
					return m_distribution.prob(classIndex, theSubset);
				}
				else
				{
					return m_distribution.prob(classIndex);
				}
			}
		}
		
		/// <summary> Creates split on enumerated attribute.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private void  handleEnumeratedAttribute(Instances trainInstances)
		{
			
			Distribution newDistribution, secondDistribution;
			int numAttValues;
			double currIG, currGR;
			Instance instance;
			int i;
			
			numAttValues = trainInstances.attribute(m_attIndex).numValues();
			newDistribution = new Distribution(numAttValues, trainInstances.numClasses());
			
			// Only Instances with known values are relevant.
			System.Collections.IEnumerator enu = trainInstances.enumerateInstances();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				instance = (Instance) enu.Current;
				if (!instance.isMissing(m_attIndex))
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					newDistribution.add((int) instance.value_Renamed(m_attIndex), instance);
				}
			}
			m_distribution = newDistribution;
			
			// For all values
			for (i = 0; i < numAttValues; i++)
			{
				
				if (Utils.grOrEq(newDistribution.perBag(i), m_minNoObj))
				{
					secondDistribution = new Distribution(newDistribution, i);
					
					// Check if minimum number of Instances in the two
					// subsets.
					if (secondDistribution.check(m_minNoObj))
					{
						m_numSubsets = 2;
						currIG = m_infoGainCrit.splitCritValue(secondDistribution, m_sumOfWeights);
						currGR = m_gainRatioCrit.splitCritValue(secondDistribution, m_sumOfWeights, currIG);
						if ((i == 0) || Utils.gr(currGR, m_gainRatio))
						{
							m_gainRatio = currGR;
							m_infoGain = currIG;
							m_splitPoint = (double) i;
							m_distribution = secondDistribution;
						}
					}
				}
			}
		}
		
		/// <summary> Creates split on numeric attribute.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		private void  handleNumericAttribute(Instances trainInstances)
		{
			
			int firstMiss;
			int next = 1;
			int last = 0;
			int index = 0;
			int splitIndex = - 1;
			double currentInfoGain;
			double defaultEnt;
			double minSplit;
			Instance instance;
			int i;
			
			// Current attribute is a numeric attribute.
			m_distribution = new Distribution(2, trainInstances.numClasses());
			
			// Only Instances with known values are relevant.
			System.Collections.IEnumerator enu = trainInstances.enumerateInstances();
			i = 0;
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (enu.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				instance = (Instance) enu.Current;
				if (instance.isMissing(m_attIndex))
					break;
				m_distribution.add(1, instance);
				i++;
			}
			firstMiss = i;
			
			// Compute minimum number of Instances required in each
			// subset.
			minSplit = 0.1 * (m_distribution.total()) / ((double) trainInstances.numClasses());
			if (Utils.smOrEq(minSplit, m_minNoObj))
				minSplit = m_minNoObj;
			else if (Utils.gr(minSplit, 25))
				minSplit = 25;
			
			// Enough Instances with known values?
			if (Utils.sm((double) firstMiss, 2 * minSplit))
				return ;
			
			// Compute values of criteria for all possible split
			// indices.
			defaultEnt = m_infoGainCrit.oldEnt(m_distribution);
			while (next < firstMiss)
			{
				
				if (trainInstances.instance(next - 1).value_Renamed(m_attIndex) + 1e-5 < trainInstances.instance(next).value_Renamed(m_attIndex))
				{
					
					// Move class values for all Instances up to next 
					// possible split point.
					m_distribution.shiftRange(1, 0, trainInstances, last, next);
					
					// Check if enough Instances in each subset and compute
					// values for criteria.
					if (Utils.grOrEq(m_distribution.perBag(0), minSplit) && Utils.grOrEq(m_distribution.perBag(1), minSplit))
					{
						currentInfoGain = m_infoGainCrit.splitCritValue(m_distribution, m_sumOfWeights, defaultEnt);
						if (Utils.gr(currentInfoGain, m_infoGain))
						{
							m_infoGain = currentInfoGain;
							splitIndex = next - 1;
						}
						index++;
					}
					last = next;
				}
				next++;
			}
			
			// Was there any useful split?
			if (index == 0)
				return ;
			
			// Compute modified information gain for best split.
			m_infoGain = m_infoGain - (Utils.log2(index) / m_sumOfWeights);
			if (Utils.smOrEq(m_infoGain, 0))
				return ;
			
			// Set instance variables' values to values for
			// best split.
			m_numSubsets = 2;
			m_splitPoint = (trainInstances.instance(splitIndex + 1).value_Renamed(m_attIndex) + trainInstances.instance(splitIndex).value_Renamed(m_attIndex)) / 2;
			
			// In case we have a numerical precision problem we need to choose the
			// smaller value
			if (m_splitPoint == trainInstances.instance(splitIndex + 1).value_Renamed(m_attIndex))
			{
				m_splitPoint = trainInstances.instance(splitIndex).value_Renamed(m_attIndex);
			}
			
			// Restore distributioN for best split.
			m_distribution = new Distribution(2, trainInstances.numClasses());
			m_distribution.addRange(0, trainInstances, 0, splitIndex + 1);
			m_distribution.addRange(1, trainInstances, splitIndex + 1, firstMiss);
			
			// Compute modified gain ratio for best split.
			m_gainRatio = m_gainRatioCrit.splitCritValue(m_distribution, m_sumOfWeights, m_infoGain);
		}
		
		/// <summary> Returns (C4.5-type) information gain for the generated split.</summary>
		public double infoGain()
		{
			
			return m_infoGain;
		}
		
		/// <summary> Prints left side of condition..</summary>
		/// <param name="index">of subset and training set.
		/// </param>
		public override System.String leftSide(Instances data)
		{
			
			return data.attribute(m_attIndex).name();
		}
		
		/// <summary> Prints the condition satisfied by instances in a subset.
		/// 
		/// </summary>
		/// <param name="index">of subset and training set.
		/// </param>
		public override System.String rightSide(int index, Instances data)
		{
			
			System.Text.StringBuilder text;
			
			text = new System.Text.StringBuilder();
			if (data.attribute(m_attIndex).Nominal)
			{
				if (index == 0)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					text.Append(" = " + data.attribute(m_attIndex).value_Renamed((int) m_splitPoint));
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					text.Append(" != " + data.attribute(m_attIndex).value_Renamed((int) m_splitPoint));
				}
			}
			else if (index == 0)
				text.Append(" <= " + m_splitPoint);
			else
				text.Append(" > " + m_splitPoint);
			
			return text.ToString();
		}
		
		/// <summary> Returns a string containing java source code equivalent to the test
		/// made at this node. The instance being tested is called "i".
		/// 
		/// </summary>
		/// <param name="index">index of the nominal value tested
		/// </param>
		/// <param name="data">the data containing instance structure info
		/// </param>
		/// <returns> a value of type 'String'
		/// </returns>
		public override System.String sourceExpression(int index, Instances data)
		{
			
			System.Text.StringBuilder expr = null;
			if (index < 0)
			{
				return "i[" + m_attIndex + "] == null";
			}
			if (data.attribute(m_attIndex).Nominal)
			{
				if (index == 0)
				{
					expr = new System.Text.StringBuilder("i[");
				}
				else
				{
					expr = new System.Text.StringBuilder("!i[");
				}
				expr.Append(m_attIndex).Append("]");
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				expr.Append(".equals(\"").Append(data.attribute(m_attIndex).value_Renamed((int) m_splitPoint)).Append("\")");
			}
			else
			{
				expr = new System.Text.StringBuilder("((Double) i[");
				expr.Append(m_attIndex).Append("])");
				if (index == 0)
				{
					expr.Append(".doubleValue() <= ").Append(m_splitPoint);
				}
				else
				{
					expr.Append(".doubleValue() > ").Append(m_splitPoint);
				}
			}
			return expr.ToString();
		}
		
		/// <summary> Sets distribution associated with model.</summary>
		public override void  resetDistribution(Instances data)
		{
			
			Instances insts = new Instances(data, data.numInstances());
			for (int i = 0; i < data.numInstances(); i++)
			{
				if (whichSubset(data.instance(i)) > - 1)
				{
					insts.add(data.instance(i));
				}
			}
			Distribution newD = new Distribution(insts, this);
			newD.addInstWithUnknown(data, m_attIndex);
			m_distribution = newD;
		}
		
		/// <summary> Returns weights if instance is assigned to more than one subset.
		/// Returns null if instance is only assigned to one subset.
		/// </summary>
		public override double[] GetWeights(Instance instance)
		{
			
			double[] weights;
			int i;
			
			if (instance.isMissing(m_attIndex))
			{
				weights = new double[m_numSubsets];
				for (i = 0; i < m_numSubsets; i++)
					weights[i] = m_distribution.perBag(i) / m_distribution.total();
				return weights;
			}
			else
			{
				return null;
			}
		}
		
		/// <summary> Returns index of subset instance is assigned to.
		/// Returns -1 if instance is assigned to more than one subset.
		/// 
		/// </summary>
		/// <exception cref="Exception">if something goes wrong
		/// </exception>
		
		public override int whichSubset(Instance instance)
		{
			
			if (instance.isMissing(m_attIndex))
				return - 1;
			else
			{
				if (instance.attribute(m_attIndex).Nominal)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					if ((int) m_splitPoint == (int) instance.value_Renamed(m_attIndex))
						return 0;
					else
						return 1;
				}
				else if (Utils.smOrEq(instance.value_Renamed(m_attIndex), m_splitPoint))
					return 0;
				else
					return 1;
			}
		}
		//UPGRADE_TODO: The following method was automatically generated and it must be implemented in order to preserve the class logic. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1232'"
		override public System.Object Clone()
		{
			return null;
		}
	}
}