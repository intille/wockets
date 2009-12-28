/*
*    This program is free software; you can redistribute it and/or modify
*    it under the terms of the GNU General Public License as published by
*    the Free Software Foundation; either version 2 of the License, or
*    (at your option) any later version.
*
*    This program is distributed in the hope that it will be useful,
*    but WITHOUT ANY WARRANTY; without even the implied warranty of
*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*    GNU General Public License for more details.
*
*    You should have received a copy of the GNU General Public License
*    along with this program; if not, write to the Free Software
*    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

/*
*    ReliefFAttributeEval.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Class for Evaluating attributes individually using ReliefF. <p>
	/// 
	/// For more information see: <p>
	/// 
	/// Kira, K. and Rendell, L. A. (1992). A practical approach to feature
	/// selection. In D. Sleeman and P. Edwards, editors, <i>Proceedings of
	/// the International Conference on Machine Learning,</i> pages 249-256.
	/// Morgan Kaufmann. <p>
	/// 
	/// Kononenko, I. (1994). Estimating attributes: analysis and extensions of
	/// Relief. In De Raedt, L. and Bergadano, F., editors, <i> Machine Learning:
	/// ECML-94, </i> pages 171-182. Springer Verlag. <p>
	/// 
	/// Marko Robnik Sikonja, Igor Kononenko: An adaptation of Relief for attribute
	/// estimation on regression. In D.Fisher (ed.): <i> Machine Learning, 
	/// Proceedings of 14th International Conference on Machine Learning ICML'97, 
	/// </i> Nashville, TN, 1997. <p>
	/// 
	/// 
	/// Valid options are:
	/// 
	/// -M <number of instances> <br>
	/// Specify the number of instances to sample when estimating attributes. <br>
	/// If not specified then all instances will be used. <p>
	/// 
	/// -D <seed> <br>
	/// Seed for randomly sampling instances. <p>
	/// 
	/// -K <number of neighbours> <br>
	/// Number of nearest neighbours to use for estimating attributes. <br>
	/// (Default is 10). <p>
	/// 
	/// -W <br>
	/// Weight nearest neighbours by distance. <p>
	/// 
	/// -A <sigma> <br>
	/// Specify sigma value (used in an exp function to control how quickly <br>
	/// weights decrease for more distant instances). Use in conjunction with <br>
	/// -W. Sensible values = 1/5 to 1/10 the number of nearest neighbours. <br>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.15 $
	/// </version>
	[Serializable]
	public class ReliefFAttributeEval:AttributeEvaluator, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of ReliefFAttributeEval.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are: <p>
		/// 
		/// -M <number of instances> <br>
		/// Specify the number of instances to sample when estimating attributes. <br>
		/// If not specified then all instances will be used. <p>
		/// 
		/// -D <seed> <br>
		/// Seed for randomly sampling instances. <p>
		/// 
		/// -K <number of neighbours> <br>
		/// Number of nearest neighbours to use for estimating attributes. <br>
		/// (Default is 10). <p>
		/// 
		/// -W <br>
		/// Weight nearest neighbours by distance. <p>
		/// 
		/// -A <sigma> <br>
		/// Specify sigma value (used in an exp function to control how quickly <br>
		/// weights decrease for more distant instances). Use in conjunction with <br>
		/// -W. Sensible values = 1/5 to 1/10 the number of nearest neighbours. <br>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// 
		/// 
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] options = new System.String[9];
				int current = 0;
				
				if (WeightByDistance)
				{
					options[current++] = "-W";
				}
				
				options[current++] = "-M";
				options[current++] = "" + SampleSize;
				options[current++] = "-D";
				options[current++] = "" + Seed;
				options[current++] = "-K";
				options[current++] = "" + NumNeighbours;
				options[current++] = "-A";
				options[current++] = "" + Sigma;
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				
				return options;
			}
			
			set
			{
				System.String optionString;
				resetOptions();
				WeightByDistance = Utils.getFlag('W', value);
				optionString = Utils.getOption('M', value);
				
				if (optionString.Length != 0)
				{
					SampleSize = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('D', value);
				
				if (optionString.Length != 0)
				{
					Seed = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('K', value);
				
				if (optionString.Length != 0)
				{
					NumNeighbours = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('A', value);
				
				if (optionString.Length != 0)
				{
					WeightByDistance = true; // turn on weighting by distance
					Sigma = System.Int32.Parse(optionString);
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the value of sigma.
		/// 
		/// </summary>
		/// <returns> the sigma value.
		/// </returns>
		/// <summary> Sets the sigma value.
		/// 
		/// </summary>
		/// <param name="s">the value of sigma (> 0)
		/// </param>
		/// <exception cref="Exception">if s is not positive
		/// </exception>
		virtual public int Sigma
		{
			get
			{
				return m_sigma;
			}
			
			set
			{
				if (value <= 0)
				{
					throw new System.Exception("value of sigma must be > 0!");
				}
				
				m_sigma = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the number of nearest neighbours
		/// 
		/// </summary>
		/// <returns> the number of nearest neighbours
		/// </returns>
		/// <summary> Set the number of nearest neighbours
		/// 
		/// </summary>
		/// <param name="n">the number of nearest neighbours.
		/// </param>
		virtual public int NumNeighbours
		{
			get
			{
				return m_Knn;
			}
			
			set
			{
				m_Knn = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the seed used for randomly sampling instances.
		/// 
		/// </summary>
		/// <returns> the random number seed.
		/// </returns>
		/// <summary> Set the random number seed for randomly sampling instances.
		/// 
		/// </summary>
		/// <param name="s">the random number seed.
		/// </param>
		virtual public int Seed
		{
			get
			{
				return m_seed;
			}
			
			set
			{
				m_seed = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the number of instances used for estimating attributes
		/// 
		/// </summary>
		/// <returns> the number of instances.
		/// </returns>
		/// <summary> Set the number of instances to sample for attribute estimation
		/// 
		/// </summary>
		/// <param name="s">the number of instances to sample.
		/// </param>
		virtual public int SampleSize
		{
			get
			{
				return m_sampleM;
			}
			
			set
			{
				m_sampleM = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get whether nearest neighbours are being weighted by distance
		/// 
		/// </summary>
		/// <returns> m_weightByDiffernce
		/// </returns>
		/// <summary> Set the nearest neighbour weighting method
		/// 
		/// </summary>
		/// <param name="b">true nearest neighbours are to be weighted by distance.
		/// </param>
		virtual public bool WeightByDistance
		{
			get
			{
				return m_weightByDistance;
			}
			
			set
			{
				m_weightByDistance = value;
			}
			
		}
		
		/// <summary>The training instances </summary>
		private Instances m_trainInstances;
		
		/// <summary>The class index </summary>
		private int m_classIndex;
		
		/// <summary>The number of attributes </summary>
		private int m_numAttribs;
		
		/// <summary>The number of instances </summary>
		private int m_numInstances;
		
		/// <summary>Numeric class </summary>
		private bool m_numericClass;
		
		/// <summary>The number of classes if class is nominal </summary>
		private int m_numClasses;
		
		/// <summary> Used to hold the probability of a different class val given nearest
		/// instances (numeric class)
		/// </summary>
		private double m_ndc;
		
		/// <summary> Used to hold the prob of different value of an attribute given
		/// nearest instances (numeric class case)
		/// </summary>
		private double[] m_nda;
		
		/// <summary> Used to hold the prob of a different class val and different att
		/// val given nearest instances (numeric class case)
		/// </summary>
		private double[] m_ndcda;
		
		/// <summary>Holds the weights that relief assigns to attributes </summary>
		private double[] m_weights;
		
		/// <summary>Prior class probabilities (discrete class case) </summary>
		private double[] m_classProbs;
		
		/// <summary> The number of instances to sample when estimating attributes
		/// default == -1, use all instances
		/// </summary>
		private int m_sampleM;
		
		/// <summary>The number of nearest hits/misses </summary>
		private int m_Knn;
		
		/// <summary>k nearest scores + instance indexes for n classes </summary>
		private double[][][] m_karray;
		
		/// <summary>Upper bound for numeric attributes </summary>
		private double[] m_maxArray;
		
		/// <summary>Lower bound for numeric attributes </summary>
		private double[] m_minArray;
		
		/// <summary>Keep track of the farthest instance for each class </summary>
		private double[] m_worst;
		
		/// <summary>Index in the m_karray of the farthest instance for each class </summary>
		private int[] m_index;
		
		/// <summary>Number of nearest neighbours stored of each class </summary>
		private int[] m_stored;
		
		/// <summary>Random number seed used for sampling instances </summary>
		private int m_seed;
		
		/// <summary>  used to (optionally) weight nearest neighbours by their distance
		/// from the instance in question. Each entry holds 
		/// exp(-((rank(r_i, i_j)/sigma)^2)) where rank(r_i,i_j) is the rank of
		/// instance i_j in a sequence of instances ordered by the distance
		/// from r_i. sigma is a user defined parameter, default=20
		/// 
		/// </summary>
		private double[] m_weightsByRank;
		private int m_sigma;
		
		/// <summary>Weight by distance rather than equal weights </summary>
		private bool m_weightByDistance;
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "ReliefFAttributeEval :\n\nEvaluates the worth of an attribute by " + "repeatedly sampling an instance and considering the value of the " + "given attribute for the nearest instance of the same and different " + "class. Can operate on both discrete and continuous class data.\n";
		}
		
		/// <summary> Constructor</summary>
		public ReliefFAttributeEval()
		{
			resetOptions();
		}
		
		
		/// <summary> Returns an enumeration describing the available options.</summary>
		/// <returns> an enumeration of all the available options.
		/// 
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(4));
			newVector.Add(new Option("\tSpecify the number of instances to\n" + "\tsample when estimating attributes.\n" + "\tIf not specified, then all instances\n" + "\twill be used.", "M", 1, "-M <num instances>"));
			newVector.Add(new Option("\tSeed for randomly sampling instances.\n" + "\t(Default = 1)", "D", 1, "-D <seed>"));
			newVector.Add(new Option("\tNumber of nearest neighbours (k) used\n" + "\tto estimate attribute relevances\n" + "\t(Default = 10).", "K", 1, "-K <number of neighbours>"));
			newVector.Add(new Option("\tWeight nearest neighbours by distance\n", "W", 0, "-W"));
			newVector.Add(new Option("\tSpecify sigma value (used in an exp\n" + "\tfunction to control how quickly\n" + "\tweights for more distant instances\n" + "\tdecrease. Use in conjunction with -W.\n" + "\tSensible value=1/5 to 1/10 of the\n" + "\tnumber of nearest neighbours.\n" + "\t(Default = 2)", "A", 1, "-A <num>"));
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String sigmaTipText()
		{
			return "Set influence of nearest neighbours. Used in an exp function to " + "control how quickly weights decrease for more distant instances. " + "Use in conjunction with weightByDistance. Sensible values = 1/5 to " + "1/10 the number of nearest neighbours.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String numNeighboursTipText()
		{
			return "Number of nearest neighbours for attribute estimation.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String seedTipText()
		{
			return "Random seed for sampling instances.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String sampleSizeTipText()
		{
			return "Number of instances to sample. Default (-1) indicates that all " + "instances will be used for attribute estimation.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String weightByDistanceTipText()
		{
			return "Weight nearest neighbours by their distance.";
		}
		
		
		/// <summary> Return a description of the ReliefF attribute evaluator.
		/// 
		/// </summary>
		/// <returns> a description of the evaluator as a String.
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainInstances == null)
			{
				text.Append("ReliefF feature evaluator has not been built yet\n");
			}
			else
			{
				text.Append("\tReliefF Ranking Filter");
				text.Append("\n\tInstances sampled: ");
				
				if (m_sampleM == - 1)
				{
					text.Append("all\n");
				}
				else
				{
					text.Append(m_sampleM + "\n");
				}
				
				text.Append("\tNumber of nearest neighbours (k): " + m_Knn + "\n");
				
				if (m_weightByDistance)
				{
					text.Append("\tExponentially decreasing (with distance) " + "influence for\n" + "\tnearest neighbours. Sigma: " + m_sigma + "\n");
				}
				else
				{
					text.Append("\tEqual influence nearest neighbours\n");
				}
			}
			
			return text.ToString();
		}
		
		
		/// <summary> Initializes a ReliefF attribute evaluator. 
		/// 
		/// </summary>
		/// <param name="data">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the evaluator has not been 
		/// generated successfully
		/// </exception>
		public override void  buildEvaluator(Instances data)
		{
			int z, totalInstances;
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random r = new System.Random((System.Int32) m_seed);
			
			if (data.checkForStringAttributes())
			{
				throw new Exception("Can't handle string attributes!");
			}
			
			m_trainInstances = data;
			m_classIndex = m_trainInstances.classIndex();
			m_numAttribs = m_trainInstances.numAttributes();
			m_numInstances = m_trainInstances.numInstances();
			
			if (m_trainInstances.attribute(m_classIndex).Numeric)
			{
				m_numericClass = true;
			}
			else
			{
				m_numericClass = false;
			}
			
			if (!m_numericClass)
			{
				m_numClasses = m_trainInstances.attribute(m_classIndex).numValues();
			}
			else
			{
				m_ndc = 0;
				m_numClasses = 1;
				m_nda = new double[m_numAttribs];
				m_ndcda = new double[m_numAttribs];
			}
			
			if (m_weightByDistance)
			// set up the rank based weights
			{
				m_weightsByRank = new double[m_Knn];
				
				for (int i = 0; i < m_Knn; i++)
				{
					m_weightsByRank[i] = System.Math.Exp(- ((i / (double) m_sigma) * (i / (double) m_sigma)));
				}
			}
			
			// the final attribute weights
			m_weights = new double[m_numAttribs];
			// num classes (1 for numeric class) knn neighbours, 
			// and 0 = distance, 1 = instance index
			m_karray = new double[m_numClasses][][];
			for (int i = 0; i < m_numClasses; i++)
			{
				m_karray[i] = new double[m_Knn][];
				for (int i2 = 0; i2 < m_Knn; i2++)
				{
					m_karray[i][i2] = new double[2];
				}
			}
			
			if (!m_numericClass)
			{
				m_classProbs = new double[m_numClasses];
				
				for (int i = 0; i < m_numInstances; i++)
				{
					m_classProbs[(int) m_trainInstances.instance(i).value_Renamed(m_classIndex)]++;
				}
				
				for (int i = 0; i < m_numClasses; i++)
				{
					m_classProbs[i] /= m_numInstances;
				}
			}
			
			m_worst = new double[m_numClasses];
			m_index = new int[m_numClasses];
			m_stored = new int[m_numClasses];
			m_minArray = new double[m_numAttribs];
			m_maxArray = new double[m_numAttribs];
			
			for (int i = 0; i < m_numAttribs; i++)
			{
				m_minArray[i] = m_maxArray[i] = System.Double.NaN;
			}
			
			for (int i = 0; i < m_numInstances; i++)
			{
				updateMinMax(m_trainInstances.instance(i));
			}
			
			if ((m_sampleM > m_numInstances) || (m_sampleM < 0))
			{
				totalInstances = m_numInstances;
			}
			else
			{
				totalInstances = m_sampleM;
			}
			
			// process each instance, updating attribute weights
			for (int i = 0; i < totalInstances; i++)
			{
				if (totalInstances == m_numInstances)
				{
					z = i;
				}
				else
				{
					//UPGRADE_TODO: Method 'java.util.Random.nextInt' was converted to 'System.Random.Next' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
					z = r.Next() % m_numInstances;
				}
				
				if (z < 0)
				{
					z *= (- 1);
				}
				
				if (!(m_trainInstances.instance(z).isMissing(m_classIndex)))
				{
					// first clear the knn and worst index stuff for the classes
					for (int j = 0; j < m_numClasses; j++)
					{
						m_index[j] = m_stored[j] = 0;
						
						for (int k = 0; k < m_Knn; k++)
						{
							m_karray[j][k][0] = m_karray[j][k][1] = 0;
						}
					}
					
					findKHitMiss(z);
					
					if (m_numericClass)
					{
						updateWeightsNumericClass(z);
					}
					else
					{
						updateWeightsDiscreteClass(z);
					}
				}
			}
			
			// now scale weights by 1/m_numInstances (nominal class) or
			// calculate weights numeric class
			// System.out.println("num inst:"+m_numInstances+" r_ndc:"+r_ndc);
			for (int i = 0; i < m_numAttribs; i++)
			{
				if (i != m_classIndex)
				{
					if (m_numericClass)
					{
						m_weights[i] = m_ndcda[i] / m_ndc - ((m_nda[i] - m_ndcda[i]) / ((double) totalInstances - m_ndc));
					}
					else
					{
						m_weights[i] *= (1.0 / (double) totalInstances);
					}
					
					//	  System.out.println(r_weights[i]);
				}
			}
		}
		
		
		/// <summary> Evaluates an individual attribute using ReliefF's instance based approach.
		/// The actual work is done by buildEvaluator which evaluates all features.
		/// 
		/// </summary>
		/// <param name="attribute">the index of the attribute to be evaluated
		/// </param>
		/// <exception cref="Exception">if the attribute could not be evaluated
		/// </exception>
		public override double evaluateAttribute(int attribute)
		{
			return m_weights[attribute];
		}
		
		
		/// <summary> Reset options to their default values</summary>
		protected internal virtual void  resetOptions()
		{
			m_trainInstances = null;
			m_sampleM = - 1;
			m_Knn = 10;
			m_sigma = 2;
			m_weightByDistance = false;
			m_seed = 1;
		}
		
		
		/// <summary> Normalizes a given value of a numeric attribute.
		/// 
		/// </summary>
		/// <param name="x">the value to be normalized
		/// </param>
		/// <param name="i">the attribute's index
		/// </param>
		private double norm(double x, int i)
		{
			if (System.Double.IsNaN(m_minArray[i]) || Utils.eq(m_maxArray[i], m_minArray[i]))
			{
				return 0;
			}
			else
			{
				return (x - m_minArray[i]) / (m_maxArray[i] - m_minArray[i]);
			}
		}
		
		
		/// <summary> Updates the minimum and maximum values for all the attributes
		/// based on a new instance.
		/// 
		/// </summary>
		/// <param name="instance">the new instance
		/// </param>
		private void  updateMinMax(Instance instance)
		{
			//    for (int j = 0; j < m_numAttribs; j++) {
			try
			{
				for (int j = 0; j < instance.numValues(); j++)
				{
					if ((instance.attributeSparse(j).Numeric) && (!instance.isMissingSparse(j)))
					{
						if (System.Double.IsNaN(m_minArray[instance.index(j)]))
						{
							m_minArray[instance.index(j)] = instance.valueSparse(j);
							m_maxArray[instance.index(j)] = instance.valueSparse(j);
						}
						else
						{
							if (instance.valueSparse(j) < m_minArray[instance.index(j)])
							{
								m_minArray[instance.index(j)] = instance.valueSparse(j);
							}
							else
							{
								if (instance.valueSparse(j) > m_maxArray[instance.index(j)])
								{
									m_maxArray[instance.index(j)] = instance.valueSparse(j);
								}
							}
						}
					}
				}
			}
			catch (System.Exception ex)
			{
				//UPGRADE_TODO: Method 'java.io.PrintStream.println' was converted to 'System.Console.Error.WriteLine' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javaioPrintStreamprintln_javalangObject'"
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				System.Console.Error.WriteLine(ex);
				//SupportClass.WriteStackTrace(ex, Console.Error);
			}
		}
		
		/// <summary> Computes the difference between two given attribute
		/// values.
		/// </summary>
		private double difference(int index, double val1, double val2)
		{
			
			switch (m_trainInstances.attribute(index).type())
			{
				
				case weka.core.Attribute.NOMINAL: 
					
					// If attribute is nominal
					if (Instance.isMissingValue(val1) || Instance.isMissingValue(val2))
					{
						return (1.0 - (1.0 / ((double) m_trainInstances.attribute(index).numValues())));
					}
					else
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						if ((int) val1 != (int) val2)
						{
							return 1;
						}
						else
						{
							return 0;
						}
					}
					goto case weka.core.Attribute.NUMERIC;

                case weka.core.Attribute.NUMERIC: 
					
					// If attribute is numeric
					if (Instance.isMissingValue(val1) || Instance.isMissingValue(val2))
					{
						if (Instance.isMissingValue(val1) && Instance.isMissingValue(val2))
						{
							return 1;
						}
						else
						{
							double diff;
							if (Instance.isMissingValue(val2))
							{
								diff = norm(val1, index);
							}
							else
							{
								diff = norm(val2, index);
							}
							if (diff < 0.5)
							{
								diff = 1.0 - diff;
							}
							return diff;
						}
					}
					else
					{
						return System.Math.Abs(norm(val1, index) - norm(val2, index));
					}
					goto default;
				
				default: 
					return 0;
				
			}
		}
		
		/// <summary> Calculates the distance between two instances
		/// 
		/// </summary>
		/// <param name="test">the first instance
		/// </param>
		/// <param name="train">the second instance
		/// </param>
		/// <returns> the distance between the two given instances, between 0 and 1
		/// </returns>
		private double distance(Instance first, Instance second)
		{
			
			double distance = 0;
			int firstI, secondI;
			
			for (int p1 = 0, p2 = 0; p1 < first.numValues() || p2 < second.numValues(); )
			{
				if (p1 >= first.numValues())
				{
					firstI = m_trainInstances.numAttributes();
				}
				else
				{
					firstI = first.index(p1);
				}
				if (p2 >= second.numValues())
				{
					secondI = m_trainInstances.numAttributes();
				}
				else
				{
					secondI = second.index(p2);
				}
				if (firstI == m_trainInstances.classIndex())
				{
					p1++; continue;
				}
				if (secondI == m_trainInstances.classIndex())
				{
					p2++; continue;
				}
				double diff;
				if (firstI == secondI)
				{
					diff = difference(firstI, first.valueSparse(p1), second.valueSparse(p2));
					p1++; p2++;
				}
				else if (firstI > secondI)
				{
					diff = difference(secondI, 0, second.valueSparse(p2));
					p2++;
				}
				else
				{
					diff = difference(firstI, first.valueSparse(p1), 0);
					p1++;
				}
				//      distance += diff * diff;
				distance += diff;
			}
			
			//    return Math.sqrt(distance / m_NumAttributesUsed);
			return distance;
		}
		
		
		/// <summary> update attribute weights given an instance when the class is numeric
		/// 
		/// </summary>
		/// <param name="instNum">the index of the instance to use when updating weights
		/// </param>
		private void  updateWeightsNumericClass(int instNum)
		{
			int i, j;
			double temp, temp2;
			int[] tempSorted = null;
			double[] tempDist = null;
			double distNorm = 1.0;
			int firstI, secondI;
			
			Instance inst = m_trainInstances.instance(instNum);
			
			// sort nearest neighbours and set up normalization variable
			if (m_weightByDistance)
			{
				tempDist = new double[m_stored[0]];
				
				for (j = 0, distNorm = 0; j < m_stored[0]; j++)
				{
					// copy the distances
					tempDist[j] = m_karray[0][j][0];
					// sum normalizer
					distNorm += m_weightsByRank[j];
				}
				
				tempSorted = Utils.sort(tempDist);
			}
			
			for (i = 0; i < m_stored[0]; i++)
			{
				// P diff prediction (class) given nearest instances
				if (m_weightByDistance)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					temp = difference(m_classIndex, inst.value_Renamed(m_classIndex), m_trainInstances.instance((int) m_karray[0][tempSorted[i]][1]).value_Renamed(m_classIndex));
					temp *= (m_weightsByRank[i] / distNorm);
				}
				else
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					temp = difference(m_classIndex, inst.value_Renamed(m_classIndex), m_trainInstances.instance((int) m_karray[0][i][1]).value_Renamed(m_classIndex));
					temp *= (1.0 / (double) m_stored[0]); // equal influence
				}
				
				m_ndc += temp;
				
				Instance cmp;
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				cmp = (m_weightByDistance)?m_trainInstances.instance((int) m_karray[0][tempSorted[i]][1]):m_trainInstances.instance((int) m_karray[0][i][1]);
				
				double temp_diffP_diffA_givNearest = difference(m_classIndex, inst.value_Renamed(m_classIndex), cmp.value_Renamed(m_classIndex));
				// now the attributes
				for (int p1 = 0, p2 = 0; p1 < inst.numValues() || p2 < cmp.numValues(); )
				{
					if (p1 >= inst.numValues())
					{
						firstI = m_trainInstances.numAttributes();
					}
					else
					{
						firstI = inst.index(p1);
					}
					if (p2 >= cmp.numValues())
					{
						secondI = m_trainInstances.numAttributes();
					}
					else
					{
						secondI = cmp.index(p2);
					}
					if (firstI == m_trainInstances.classIndex())
					{
						p1++; continue;
					}
					if (secondI == m_trainInstances.classIndex())
					{
						p2++; continue;
					}
					temp = 0.0;
					temp2 = 0.0;
					
					if (firstI == secondI)
					{
						j = firstI;
						temp = difference(j, inst.valueSparse(p1), cmp.valueSparse(p2));
						p1++; p2++;
					}
					else if (firstI > secondI)
					{
						j = secondI;
						temp = difference(j, 0, cmp.valueSparse(p2));
						p2++;
					}
					else
					{
						j = firstI;
						temp = difference(j, inst.valueSparse(p1), 0);
						p1++;
					}
					
					temp2 = temp_diffP_diffA_givNearest * temp;
					// P of different prediction and different att value given
					// nearest instances
					if (m_weightByDistance)
					{
						temp2 *= (m_weightsByRank[i] / distNorm);
					}
					else
					{
						temp2 *= (1.0 / (double) m_stored[0]); // equal influence
					}
					
					m_ndcda[j] += temp2;
					
					// P of different attribute val given nearest instances
					if (m_weightByDistance)
					{
						temp *= (m_weightsByRank[i] / distNorm);
					}
					else
					{
						temp *= (1.0 / (double) m_stored[0]); // equal influence
					}
					
					m_nda[j] += temp;
				}
			}
		}
		
		
		/// <summary> update attribute weights given an instance when the class is discrete
		/// 
		/// </summary>
		/// <param name="instNum">the index of the instance to use when updating weights
		/// </param>
		private void  updateWeightsDiscreteClass(int instNum)
		{
			int i, j, k;
			int cl;
			double cc = m_numInstances;
			double temp, temp_diff, w_norm = 1.0;
			double[] tempDistClass;
			int[] tempSortedClass = null;
			double distNormClass = 1.0;
			double[] tempDistAtt;
			int[][] tempSortedAtt = null;
			double[] distNormAtt = null;
			int firstI, secondI;
			
			// store the indexes (sparse instances) of non-zero elements
			Instance inst = m_trainInstances.instance(instNum);
			
			// get the class of this instance
			cl = (int) m_trainInstances.instance(instNum).value_Renamed(m_classIndex);
			
			// sort nearest neighbours and set up normalization variables
			if (m_weightByDistance)
			{
				// do class (hits) first
				// sort the distances
				tempDistClass = new double[m_stored[cl]];
				
				for (j = 0, distNormClass = 0; j < m_stored[cl]; j++)
				{
					// copy the distances
					tempDistClass[j] = m_karray[cl][j][0];
					// sum normalizer
					distNormClass += m_weightsByRank[j];
				}
				
				tempSortedClass = Utils.sort(tempDistClass);
				// do misses (other classes)
				int[][] tmpArray = new int[m_numClasses][];
				for (int i2 = 0; i2 < m_numClasses; i2++)
				{
					tmpArray[i2] = new int[1];
				}
				tempSortedAtt = tmpArray;
				distNormAtt = new double[m_numClasses];
				
				for (k = 0; k < m_numClasses; k++)
				{
					if (k != cl)
					// already done cl
					{
						// sort the distances
						tempDistAtt = new double[m_stored[k]];
						
						for (j = 0, distNormAtt[k] = 0; j < m_stored[k]; j++)
						{
							// copy the distances
							tempDistAtt[j] = m_karray[k][j][0];
							// sum normalizer
							distNormAtt[k] += m_weightsByRank[j];
						}
						
						tempSortedAtt[k] = Utils.sort(tempDistAtt);
					}
				}
			}
			
			if (m_numClasses > 2)
			{
				// the amount of probability space left after removing the
				// probability of this instance's class value
				w_norm = (1.0 - m_classProbs[cl]);
			}
			
			// do the k nearest hits of the same class
			for (j = 0, temp_diff = 0.0; j < m_stored[cl]; j++)
			{
				Instance cmp;
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				cmp = (m_weightByDistance)?m_trainInstances.instance((int) m_karray[cl][tempSortedClass[j]][1]):m_trainInstances.instance((int) m_karray[cl][j][1]);
				
				for (int p1 = 0, p2 = 0; p1 < inst.numValues() || p2 < cmp.numValues(); )
				{
					if (p1 >= inst.numValues())
					{
						firstI = m_trainInstances.numAttributes();
					}
					else
					{
						firstI = inst.index(p1);
					}
					if (p2 >= cmp.numValues())
					{
						secondI = m_trainInstances.numAttributes();
					}
					else
					{
						secondI = cmp.index(p2);
					}
					if (firstI == m_trainInstances.classIndex())
					{
						p1++; continue;
					}
					if (secondI == m_trainInstances.classIndex())
					{
						p2++; continue;
					}
					if (firstI == secondI)
					{
						i = firstI;
						temp_diff = difference(i, inst.valueSparse(p1), cmp.valueSparse(p2));
						p1++; p2++;
					}
					else if (firstI > secondI)
					{
						i = secondI;
						temp_diff = difference(i, 0, cmp.valueSparse(p2));
						p2++;
					}
					else
					{
						i = firstI;
						temp_diff = difference(i, inst.valueSparse(p1), 0);
						p1++;
					}
					
					if (m_weightByDistance)
					{
						temp_diff *= (m_weightsByRank[j] / distNormClass);
					}
					else
					{
						if (m_stored[cl] > 0)
						{
							temp_diff /= (double) m_stored[cl];
						}
					}
					m_weights[i] -= temp_diff;
				}
			}
			
			
			// now do k nearest misses from each of the other classes
			temp_diff = 0.0;
			
			for (k = 0; k < m_numClasses; k++)
			{
				if (k != cl)
				// already done cl
				{
					for (j = 0, temp = 0.0; j < m_stored[k]; j++)
					{
						Instance cmp;
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						cmp = (m_weightByDistance)?m_trainInstances.instance((int) m_karray[k][tempSortedAtt[k][j]][1]):m_trainInstances.instance((int) m_karray[k][j][1]);
						
						for (int p1 = 0, p2 = 0; p1 < inst.numValues() || p2 < cmp.numValues(); )
						{
							if (p1 >= inst.numValues())
							{
								firstI = m_trainInstances.numAttributes();
							}
							else
							{
								firstI = inst.index(p1);
							}
							if (p2 >= cmp.numValues())
							{
								secondI = m_trainInstances.numAttributes();
							}
							else
							{
								secondI = cmp.index(p2);
							}
							if (firstI == m_trainInstances.classIndex())
							{
								p1++; continue;
							}
							if (secondI == m_trainInstances.classIndex())
							{
								p2++; continue;
							}
							if (firstI == secondI)
							{
								i = firstI;
								temp_diff = difference(i, inst.valueSparse(p1), cmp.valueSparse(p2));
								p1++; p2++;
							}
							else if (firstI > secondI)
							{
								i = secondI;
								temp_diff = difference(i, 0, cmp.valueSparse(p2));
								p2++;
							}
							else
							{
								i = firstI;
								temp_diff = difference(i, inst.valueSparse(p1), 0);
								p1++;
							}
							
							if (m_weightByDistance)
							{
								temp_diff *= (m_weightsByRank[j] / distNormAtt[k]);
							}
							else
							{
								if (m_stored[k] > 0)
								{
									temp_diff /= (double) m_stored[k];
								}
							}
							if (m_numClasses > 2)
							{
								m_weights[i] += ((m_classProbs[k] / w_norm) * temp_diff);
							}
							else
							{
								m_weights[i] += temp_diff;
							}
						}
					}
				}
			}
		}
		
		
		/// <summary> Find the K nearest instances to supplied instance if the class is numeric,
		/// or the K nearest Hits (same class) and Misses (K from each of the other
		/// classes) if the class is discrete.
		/// 
		/// </summary>
		/// <param name="instNum">the index of the instance to find nearest neighbours of
		/// </param>
		private void  findKHitMiss(int instNum)
		{
			int i, j;
			int cl;
			double ww;
			double temp_diff = 0.0;
			Instance thisInst = m_trainInstances.instance(instNum);
			
			for (i = 0; i < m_numInstances; i++)
			{
				if (i != instNum)
				{
					Instance cmpInst = m_trainInstances.instance(i);
					temp_diff = distance(cmpInst, thisInst);
					
					// class of this training instance or 0 if numeric
					if (m_numericClass)
					{
						cl = 0;
					}
					else
					{
						cl = (int) m_trainInstances.instance(i).value_Renamed(m_classIndex);
					}
					
					// add this diff to the list for the class of this instance
					if (m_stored[cl] < m_Knn)
					{
						m_karray[cl][m_stored[cl]][0] = temp_diff;
						m_karray[cl][m_stored[cl]][1] = i;
						m_stored[cl]++;
						
						// note the worst diff for this class
						for (j = 0, ww = - 1.0; j < m_stored[cl]; j++)
						{
							if (m_karray[cl][j][0] > ww)
							{
								ww = m_karray[cl][j][0];
								m_index[cl] = j;
							}
						}
						
						m_worst[cl] = ww;
					}
					/* if we already have stored knn for this class then check to
					see if this instance is better than the worst */
					else
					{
						if (temp_diff < m_karray[cl][m_index[cl]][0])
						{
							m_karray[cl][m_index[cl]][0] = temp_diff;
							m_karray[cl][m_index[cl]][1] = i;
							
							for (j = 0, ww = - 1.0; j < m_stored[cl]; j++)
							{
								if (m_karray[cl][j][0] > ww)
								{
									ww = m_karray[cl][j][0];
									m_index[cl] = j;
								}
							}
							
							m_worst[cl] = ww;
						}
					}
				}
			}
		}
		
		
		// ============
		// Test method.
		// ============
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="args">the options
		/// </param>
		
		public static void  Main(System.String[] args)
		{
			try
			{
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new ReliefFAttributeEval(), args));
			}
			catch (System.Exception e)
			{
				//SupportClass.WriteStackTrace(e, Console.Error);
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				System.Console.Out.WriteLine(e.Message);
			}
		}
	}
}