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
*    AttributeSelection.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
//UPGRADE_TODO: The type 'weka.filters.Filter' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Filter = weka.filters.Filter;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.Remove' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Remove = weka.filters.unsupervised.attribute.Remove;
namespace weka.attributeSelection
{
	
	/// <summary> Attribute selection class. Takes the name of a search class and
	/// an evaluation class on the command line. <p>
	/// 
	/// Valid options are: <p>
	/// 
	/// -h <br>
	/// Display help. <p>
	/// 
	/// -I <name of input file> <br>
	/// Specify the training arff file. <p>
	/// 
	/// -C <class index> <br>
	/// The index of the attribute to use as the class. <p>
	/// 
	/// -S <search method> <br>
	/// The full class name of the search method followed by search method options
	/// (if any).<br>
	/// Eg. -S "weka.attributeSelection.BestFirst -N 10" <p>
	/// 
	/// -X <number of folds> <br>
	/// Perform a cross validation. <p>
	/// 
	/// -N <random number seed> <br>
	/// Specify a random number seed. Use in conjuction with -X. (Default = 1). <p>
	/// 
	/// ------------------------------------------------------------------------ <p>
	/// 
	/// Example usage as the main of an attribute evaluator (called FunkyEvaluator):
	/// <code> <pre>
	/// public static void main(String [] args) {
	/// try {
	/// ASEvaluator eval = new FunkyEvaluator();
	/// System.out.println(SelectAttributes(Evaluator, args));
	/// } catch (Exception e) {
	/// System.err.println(e.getMessage());
	/// }
	/// }
	/// </code> </pre>
	/// <p>
	/// 
	/// ------------------------------------------------------------------------ <p>
	/// 
	/// </summary>
	/// <author>    Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>   $Revision: 1.35.2.3 $
	/// </version>
	[Serializable]
	public class AttributeSelection
	{
		/// <summary> set the attribute/subset evaluator</summary>
		/// <param name="evaluator">the evaluator to use
		/// </param>
		virtual public ASEvaluation Evaluator
		{
			set
			{
				m_ASEvaluator = value;
			}
			
		}
		/// <summary> set the search method</summary>
		/// <param name="search">the search method to use
		/// </param>
		virtual public ASSearch Search
		{
			set
			{
				m_searchMethod = value;
				
				if (m_searchMethod is RankedOutputSearch)
				{
					Ranking = ((RankedOutputSearch) m_searchMethod).GenerateRanking;
				}
			}
			
		}
		/// <summary> set the number of folds for cross validation</summary>
		/// <param name="folds">the number of folds
		/// </param>
		virtual public int Folds
		{
			set
			{
				m_numFolds = value;
			}
			
		}
		/// <summary> produce a ranking (if possible with the set search and evaluator)</summary>
		/// <param name="r">true if a ranking is to be produced
		/// </param>
		virtual public bool Ranking
		{
			set
			{
				m_doRank = value;
			}
			
		}
		/// <summary> do a cross validation</summary>
		/// <param name="x">true if a cross validation is to be performed
		/// </param>
		virtual public bool Xval
		{
			set
			{
				m_doXval = value;
			}
			
		}
		/// <summary> set the seed for use in cross validation</summary>
		/// <param name="s">the seed
		/// </param>
		virtual public int Seed
		{
			set
			{
				m_seed = value;
			}
			
		}
		
		/// <summary>the instances to select attributes from </summary>
		private Instances m_trainInstances;
		
		/// <summary>the attribute/subset evaluator </summary>
		private ASEvaluation m_ASEvaluator;
		
		/// <summary>the search method </summary>
		private ASSearch m_searchMethod;
		
		/// <summary>the number of folds to use for cross validation </summary>
		private int m_numFolds;
		
		/// <summary>holds a string describing the results of the attribute selection </summary>
		private System.Text.StringBuilder m_selectionResults;
		
		/// <summary>rank features (if allowed by the search method) </summary>
		private bool m_doRank;
		
		/// <summary>do cross validation </summary>
		private bool m_doXval;
		
		/// <summary>seed used to randomly shuffle instances for cross validation </summary>
		private int m_seed;
		
		/// <summary>number of attributes requested from ranked results </summary>
		private int m_numToSelect;
		
		/// <summary>the selected attributes </summary>
		private int[] m_selectedAttributeSet;
		
		/// <summary>the attribute indexes and associated merits if a ranking is produced </summary>
		private double[][] m_attributeRanking;
		
		/// <summary>if a feature selection run involves an attribute transformer </summary>
		private AttributeTransformer m_transformer = null;
		
		/// <summary>the attribute filter for processing instances with respect to
		/// the most recent feature selection run 
		/// </summary>
		private Remove m_attributeFilter = null;
		
		/// <summary>hold statistics for repeated feature selection, such as
		/// under cross validation 
		/// </summary>
		public double[][] m_rankResults = null;
		private double[] m_subsetResults = null;
		private int m_trials = 0;
		
		/// <summary> Return the number of attributes selected from the most recent
		/// run of attribute selection
		/// </summary>
		/// <returns> the number of attributes selected
		/// </returns>
		public virtual int numberAttributesSelected()
		{
			int[] att = selectedAttributes();
			return att.Length - 1;
		}
		
		/// <summary> get the final selected set of attributes.</summary>
		/// <returns> an array of attribute indexes
		/// </returns>
		/// <exception cref="Exception">if attribute selection has not been performed yet
		/// </exception>
		public virtual int[] selectedAttributes()
		{
			if (m_selectedAttributeSet == null)
			{
				throw new System.Exception("Attribute selection has not been performed yet!");
			}
			return m_selectedAttributeSet;
		}
		
		/// <summary> get the final ranking of the attributes.</summary>
		/// <returns> a two dimensional array of ranked attribute indexes and their
		/// associated merit scores as doubles.
		/// </returns>
		/// <exception cref="Exception">if a ranking has not been produced
		/// </exception>
		public virtual double[][] rankedAttributes()
		{
			if (m_attributeRanking == null)
			{
				throw new System.Exception("Ranking has not been performed");
			}
			return m_attributeRanking;
		}
		
		/// <summary> get a description of the attribute selection</summary>
		/// <returns> a String describing the results of attribute selection
		/// </returns>
		public virtual System.String toResultsString()
		{
			return m_selectionResults.ToString();
		}
		
		/// <summary> reduce the dimensionality of a set of instances to include only those 
		/// attributes chosen by the last run of attribute selection.
		/// </summary>
		/// <param name="in">the instances to be reduced
		/// </param>
		/// <returns> a dimensionality reduced set of instances
		/// </returns>
		/// <exception cref="Exception">if the instances can't be reduced
		/// </exception>
		public virtual Instances reduceDimensionality(Instances in_Renamed)
		{
			if (m_attributeFilter == null)
			{
				throw new System.Exception("No feature selection has been performed yet!");
			}
			
			if (m_transformer != null)
			{
				Instances transformed = new Instances(m_transformer.transformedHeader(), in_Renamed.numInstances());
				for (int i = 0; i < in_Renamed.numInstances(); i++)
				{
					transformed.add(m_transformer.convertInstance(in_Renamed.instance(i)));
				}
				return Filter.useFilter(transformed, m_attributeFilter);
			}
			
			return Filter.useFilter(in_Renamed, m_attributeFilter);
		}
		
		/// <summary> reduce the dimensionality of a single instance to include only those 
		/// attributes chosen by the last run of attribute selection.
		/// </summary>
		/// <param name="in">the instance to be reduced
		/// </param>
		/// <returns> a dimensionality reduced instance
		/// </returns>
		/// <exception cref="Exception">if the instance can't be reduced
		/// </exception>
		public virtual Instance reduceDimensionality(Instance in_Renamed)
		{
			if (m_attributeFilter == null)
			{
				throw new System.Exception("No feature selection has been performed yet!");
			}
			if (m_transformer != null)
			{
				in_Renamed = m_transformer.convertInstance(in_Renamed);
			}
			m_attributeFilter.input(in_Renamed);
			m_attributeFilter.batchFinished();
			Instance result = m_attributeFilter.output();
			return result;
		}
		
		/// <summary> constructor. Sets defaults for each member varaible. Default
		/// attribute evaluator is CfsSubsetEval; default search method is
		/// BestFirst.
		/// </summary>
		public AttributeSelection()
		{
			Folds = 10;
			Ranking = false;
			Xval = false;
			Seed = 1;
			Evaluator = new CfsSubsetEval();
			Search = new GreedyStepwise();
			m_selectionResults = new System.Text.StringBuilder();
			m_selectedAttributeSet = null;
			m_attributeRanking = null;
		}
		
		/// <summary> Perform attribute selection with a particular evaluator and
		/// a set of options specifying search method and input file etc.
		/// 
		/// </summary>
		/// <param name="ASEvaluator">an evaluator object
		/// </param>
		/// <param name="options">an array of options, not only for the evaluator
		/// but also the search method (if any) and an input data file
		/// </param>
		/// <returns> the results of attribute selection as a String
		/// </returns>
		/// <exception cref="Exception">if no training file is set
		/// </exception>
		public static System.String SelectAttributes(ASEvaluation ASEvaluator, System.String[] options)
		{
			System.String trainFileName, searchName;
			Instances train = null;
			ASSearch searchMethod = null;
			
			try
			{
				// get basic options (options the same for all attribute selectors
				trainFileName = Utils.getOption('I', options);
				
				if (trainFileName.Length == 0)
				{
					searchName = Utils.getOption('S', options);
					
					if (searchName.Length != 0)
					{
						//UPGRADE_TODO: The differences in the format  of parameters for method 'java.lang.Class.forName'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
						searchMethod = (ASSearch) System.Activator.CreateInstance(System.Type.GetType(searchName));
					}
					
					throw new System.Exception("No training file given.");
				}
			}
			catch (System.Exception e)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception('\n' + e.Message + makeOptionString(ASEvaluator, searchMethod));
			}
			
			//UPGRADE_TODO: Constructor 'java.io.FileReader.FileReader' was converted to 'System.IO.StreamReader' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073'"
			train = new Instances(new System.IO.StreamReader(trainFileName, System.Text.Encoding.Default));
			return SelectAttributes(ASEvaluator, options, train);
		}


        public int[] CVRanks=null;
		/// <summary> returns a string summarizing the results of repeated attribute
		/// selection runs on splits of a dataset.
		/// </summary>
		/// <returns> a summary of attribute selection results
		/// </returns>
		/// <exception cref="Exception">if no attribute selection has been performed.
		/// </exception>
		public virtual System.String CVResultsString()
		{
			System.Text.StringBuilder CvString = new System.Text.StringBuilder();
			
			if ((m_subsetResults == null && m_rankResults == null) || (m_trainInstances == null))
			{
				throw new System.Exception("Attribute selection has not been performed yet!");
			}
			
			int fieldWidth = (int) (Math.Log(m_trainInstances.numAttributes()) + 1.0);
			
			CvString.Append("\n\n=== Attribute selection " + m_numFolds + " fold cross-validation ");
			
			if (!(m_ASEvaluator is UnsupervisedSubsetEvaluator) && !(m_ASEvaluator is UnsupervisedAttributeEvaluator) && (m_trainInstances.classAttribute().Nominal))
			{
				CvString.Append("(stratified), seed: ");
				CvString.Append(m_seed + " ===\n\n");
			}
			else
			{
				CvString.Append("seed: " + m_seed + " ===\n\n");
			}
			
			if ((m_searchMethod is RankedOutputSearch) && (m_doRank == true))
			{
				CvString.Append("average merit      average rank  attribute\n");
				
				// calcualte means and std devs
				for (int i = 0; i < m_rankResults[0].Length; i++)
				{
					m_rankResults[0][i] /= m_numFolds; // mean merit
					double var = m_rankResults[0][i] * m_rankResults[0][i] * m_numFolds;
					var = (m_rankResults[2][i] - var);
					var /= m_numFolds;
					
					if (var <= 0.0)
					{
						var = 0.0;
						m_rankResults[2][i] = 0;
					}
					else
					{
						m_rankResults[2][i] = System.Math.Sqrt(var);
					}
					
					m_rankResults[1][i] /= m_numFolds; // mean rank
					var = m_rankResults[1][i] * m_rankResults[1][i] * m_numFolds;
					var = (m_rankResults[3][i] - var);
					var /= m_numFolds;
					
					if (var <= 0.0)
					{
						var = 0.0;
						m_rankResults[3][i] = 0;
					}
					else
					{
						m_rankResults[3][i] = System.Math.Sqrt(var);
					}
				}
				
				// now sort them by mean rank
				int[] s = Utils.sort(m_rankResults[1]);
                CVRanks=new int[s.Length];
                s.CopyTo(CVRanks, 0);
				for (int i = 0; i < s.Length; i++)
				{
					if (m_rankResults[1][s[i]] > 0)
					{
						CvString.Append(Utils.doubleToString(System.Math.Abs(m_rankResults[0][s[i]]), 6, 3) + " +-" + Utils.doubleToString(m_rankResults[2][s[i]], 6, 3) + "   " + Utils.doubleToString(m_rankResults[1][s[i]], fieldWidth + 2, 1) + " +-" + Utils.doubleToString(m_rankResults[3][s[i]], 5, 2) + "  " + Utils.doubleToString(((double) (s[i] + 1)), fieldWidth, 0) + " " + m_trainInstances.attribute(s[i]).name() + "\n");
					}
				}
			}
			else
			{
				CvString.Append("number of folds (%)  attribute\n");
				
				for (int i = 0; i < m_subsetResults.Length; i++)
				{
					if ((m_ASEvaluator is UnsupervisedSubsetEvaluator) || (i != m_trainInstances.classIndex()))
					{
						CvString.Append(Utils.doubleToString(m_subsetResults[i], 12, 0) + "(" + Utils.doubleToString((m_subsetResults[i] / m_numFolds * 100.0), 3, 0) + " %)  " + Utils.doubleToString(((double) (i + 1)), fieldWidth, 0) + " " + m_trainInstances.attribute(i).name() + "\n");
					}
				}
			}
			
			return CvString.ToString();
		}
		
		/// <summary> Select attributes for a split of the data. Calling this function
		/// updates the statistics on attribute selection. CVResultsString()
		/// returns a string summarizing the results of repeated calls to
		/// this function. Assumes that splits are from the same dataset---
		/// ie. have the same number and types of attributes as previous
		/// splits.
		/// 
		/// </summary>
		/// <param name="split">the instances to select attributes from
		/// </param>
		/// <exception cref="Exception">if an error occurs
		/// </exception>
		public virtual void  selectAttributesCVSplit(Instances split)
		{
			double[][] attributeRanking = null;
			
			// if the train instances are null then set equal to this split.
			// If this is the case then this function is more than likely being
			// called from outside this class in order to obtain CV statistics
			// and all we need m_trainIstances for is to get at attribute names
			// and types etc.
			if (m_trainInstances == null)
			{
				m_trainInstances = split;
			}
			
			// create space to hold statistics
			if (m_rankResults == null && m_subsetResults == null)
			{
				m_subsetResults = new double[split.numAttributes()];
				double[][] tmpArray = new double[4][];
				for (int i = 0; i < 4; i++)
				{
					tmpArray[i] = new double[split.numAttributes()];
				}
				m_rankResults = tmpArray;
			}
			
			m_ASEvaluator.buildEvaluator(split);
			// Do the search
			int[] attributeSet = m_searchMethod.search(m_ASEvaluator, split);
			// Do any postprocessing that a attribute selection method might 
			// require
			attributeSet = m_ASEvaluator.postProcess(attributeSet);
			
			if ((m_searchMethod is RankedOutputSearch) && (m_doRank == true))
			{
				attributeRanking = ((RankedOutputSearch) m_searchMethod).rankedAttributes();
				
				// System.out.println(attributeRanking[0][1]);
				for (int j = 0; j < attributeRanking.Length; j++)
				{
					// merit
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_rankResults[0][(int) attributeRanking[j][0]] += attributeRanking[j][1];
					// squared merit
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_rankResults[2][(int) attributeRanking[j][0]] += (attributeRanking[j][1] * attributeRanking[j][1]);
					// rank
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_rankResults[1][(int) attributeRanking[j][0]] += (j + 1);
					// squared rank
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_rankResults[3][(int) attributeRanking[j][0]] += (j + 1) * (j + 1);
					// += (attributeRanking[j][0] * attributeRanking[j][0]);
				}
			}
			else
			{
				for (int j = 0; j < attributeSet.Length; j++)
				{
					m_subsetResults[attributeSet[j]]++;
				}
			}
			
			m_trials++;
		}
		
		/// <summary> Perform a cross validation for attribute selection. With subset
		/// evaluators the number of times each attribute is selected over
		/// the cross validation is reported. For attribute evaluators, the
		/// average merit and average ranking + std deviation is reported for
		/// each attribute.
		/// 
		/// </summary>
		/// <returns> the results of cross validation as a String
		/// </returns>
		/// <exception cref="Exception">if an error occurs during cross validation
		/// </exception>
		public virtual System.String CrossValidateAttributes()
		{
			Instances cvData = new Instances(m_trainInstances);
			Instances train;
			double[][] rankResults;
			double[] subsetResults;
			double[][] attributeRanking = null;
			
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random random = new System.Random((System.Int32) m_seed);
			cvData.randomize(random);
			
			if (!(m_ASEvaluator is UnsupervisedSubsetEvaluator) && !(m_ASEvaluator is UnsupervisedAttributeEvaluator))
			{
				if (cvData.classAttribute().Nominal)
				{
					cvData.stratify(m_numFolds);
				}
			}
			
			for (int i = 0; i < m_numFolds; i++)
			{
				// Perform attribute selection
				train = cvData.trainCV(m_numFolds, i, random);
				selectAttributesCVSplit(train);
			}
			
			return CVResultsString();
		}
		
		/// <summary> Perform attribute selection on the supplied training instances.
		/// 
		/// </summary>
		/// <param name="data">the instances to select attributes from
		/// </param>
		/// <exception cref="Exception">if there is a problem during selection
		/// </exception>
		public virtual void  SelectAttributes(Instances data)
		{
			int[] attributeSet;
			
			m_transformer = null;
			m_attributeFilter = null;
			m_trainInstances = data;
			
			if (m_doXval == true && (m_ASEvaluator is AttributeTransformer))
			{
				throw new System.Exception("Can't cross validate an attribute transformer.");
			}
			
			if (m_ASEvaluator is SubsetEvaluator && m_searchMethod is Ranker)
			{
				throw new System.Exception(m_ASEvaluator.GetType().FullName + " must use a search method other than Ranker");
			}
			
			if (m_ASEvaluator is AttributeEvaluator && !(m_searchMethod is Ranker))
			{
				//      System.err.println("AttributeEvaluators must use a Ranker search "
				//			 +"method. Switching to Ranker...");
				//      m_searchMethod = new Ranker();
				throw new System.Exception("AttributeEvaluators must use the Ranker search " + "method");
			}
			
			if (m_searchMethod is RankedOutputSearch)
			{
				m_doRank = ((RankedOutputSearch) m_searchMethod).GenerateRanking;
			}
			
			if (m_ASEvaluator is UnsupervisedAttributeEvaluator || m_ASEvaluator is UnsupervisedSubsetEvaluator)
			{
				// unset the class index
				//      m_trainInstances.setClassIndex(-1);
			}
			else
			{
				// check that a class index has been set
				if (m_trainInstances.classIndex() < 0)
				{
					m_trainInstances.ClassIndex=m_trainInstances.numAttributes() - 1;
				}
			}
			
			// Initialize the attribute evaluator
			m_ASEvaluator.buildEvaluator(m_trainInstances);
			if (m_ASEvaluator is AttributeTransformer)
			{
				m_trainInstances = ((AttributeTransformer) m_ASEvaluator).transformedHeader();
				m_transformer = (AttributeTransformer) m_ASEvaluator;
			}
			int fieldWidth = (int) (Math.Log(m_trainInstances.numAttributes()) + 1.0);
			
			// Do the search
			attributeSet = m_searchMethod.search(m_ASEvaluator, m_trainInstances);
			
			// try and determine if the search method uses an attribute transformer---
			// this is a bit of a hack to make things work properly with RankSearch
			// using PrincipalComponents as its attribute ranker
			/*try
			{
				//UPGRADE_ISSUE: Interface 'java.beans.BeanInfo' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javabeansBeanInfo'"
				//UPGRADE_ISSUE: Method 'java.beans.Introspector.getBeanInfo' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javabeansIntrospector'"
				BeanInfo bi = Introspector.getBeanInfo(m_searchMethod.GetType());
				System.ComponentModel.PropertyDescriptor[] properties;
				//UPGRADE_ISSUE: Class 'java.beans.MethodDescriptor' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javabeansMethodDescriptor'"
				MethodDescriptor[] methods;
				//       methods = bi.getMethodDescriptors();
				//UPGRADE_ISSUE: Method 'java.beans.BeanInfo.getPropertyDescriptors' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javabeansBeanInfo'"
				properties = bi.getPropertyDescriptors();
				for (int i = 0; i < properties.Length; i++)
				{
					System.String name = properties[i].DisplayName;
					//UPGRADE_ISSUE: Method 'java.beans.PropertyDescriptor.getReadMethod' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javabeansPropertyDescriptorgetReadMethod'"
					System.Reflection.MethodInfo meth = properties[i].getReadMethod();
					System.Object retType = meth.ReturnType;
					if (retType.Equals(typeof(ASEvaluation)))
					{
						System.Type[] args = new System.Type[]{};
						ASEvaluation tempEval = (ASEvaluation) (meth.Invoke(m_searchMethod, (System.Object[]) args));
						if (tempEval is AttributeTransformer)
						{
							// grab the transformed data header
							m_trainInstances = ((AttributeTransformer) tempEval).transformedHeader();
							m_transformer = (AttributeTransformer) tempEval;
						}
					}
				}
			}
			//UPGRADE_ISSUE: Class 'java.beans.IntrospectionException' was not converted. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1000_javabeansIntrospectionException'"
			catch (IntrospectionException ex)
			{
				System.Console.Error.WriteLine("AttributeSelection: Couldn't " + "introspect");
			}
			*/
			
			// Do any postprocessing that a attribute selection method might require
			attributeSet = m_ASEvaluator.postProcess(attributeSet);
			if (!m_doRank)
			{
				m_selectionResults.Append(printSelectionResults());
			}
			
			if ((m_searchMethod is RankedOutputSearch) && m_doRank == true)
			{
				m_attributeRanking = ((RankedOutputSearch) m_searchMethod).rankedAttributes();
				m_selectionResults.Append(printSelectionResults());
				m_selectionResults.Append("Ranked attributes:\n");
				
				// retrieve the number of attributes to retain
				m_numToSelect = ((RankedOutputSearch) m_searchMethod).CalculatedNumToSelect;
				
				// determine fieldwidth for merit
				int f_p = 0;
				int w_p = 0;
				
				for (int i = 0; i < m_numToSelect; i++)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					double precision = (System.Math.Abs(m_attributeRanking[i][1]) - (int) (System.Math.Abs(m_attributeRanking[i][1])));
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					double intPart = (int) (System.Math.Abs(m_attributeRanking[i][1]));
					
					if (precision > 0)
					{
						precision = System.Math.Abs((System.Math.Log(System.Math.Abs(precision)) / System.Math.Log(10))) + 3;
					}
					if (precision > f_p)
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						f_p = (int) precision;
					}
					
					if (intPart == 0)
					{
						if (w_p < 2)
						{
							w_p = 2;
						}
					}
					else if ((System.Math.Abs((System.Math.Log(System.Math.Abs(m_attributeRanking[i][1])) / System.Math.Log(10))) + 1) > w_p)
					{
						if (m_attributeRanking[i][1] > 0)
						{
							//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
							w_p = (int) System.Math.Abs((System.Math.Log(System.Math.Abs(m_attributeRanking[i][1])) / System.Math.Log(10))) + 1;
						}
					}
				}
				
				for (int i = 0; i < m_numToSelect; i++)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_selectionResults.Append((Utils.doubleToString(m_attributeRanking[i][1], f_p + w_p + 1, f_p) + Utils.doubleToString((m_attributeRanking[i][0] + 1), fieldWidth + 1, 0)) + " " + m_trainInstances.attribute((int) m_attributeRanking[i][0]).name() + "\n");
				}
				
				// set up the selected attributes array - usable by a filter or
				// whatever
				if (m_trainInstances.classIndex() >= 0)
				{
					if ((!(m_ASEvaluator is UnsupervisedSubsetEvaluator) && !(m_ASEvaluator is UnsupervisedAttributeEvaluator)) || m_ASEvaluator is AttributeTransformer)
					{
						// one more for the class
						m_selectedAttributeSet = new int[m_numToSelect + 1];
						m_selectedAttributeSet[m_numToSelect] = m_trainInstances.classIndex();
					}
					else
					{
						m_selectedAttributeSet = new int[m_numToSelect];
					}
				}
				else
				{
					m_selectedAttributeSet = new int[m_numToSelect];
				}
				
				m_selectionResults.Append("\nSelected attributes: ");
				
				for (int i = 0; i < m_numToSelect; i++)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					m_selectedAttributeSet[i] = (int) m_attributeRanking[i][0];
					
					if (i == m_numToSelect - 1)
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						m_selectionResults.Append(((int) m_attributeRanking[i][0] + 1) + " : " + (i + 1) + "\n");
					}
					else
					{
						//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
						m_selectionResults.Append(((int) m_attributeRanking[i][0] + 1));
						m_selectionResults.Append(",");
					}
				}
			}
			else
			{
				// set up the selected attributes array - usable by a filter or
				// whatever
				if ((!(m_ASEvaluator is UnsupervisedSubsetEvaluator) && !(m_ASEvaluator is UnsupervisedAttributeEvaluator)) || m_trainInstances.classIndex() >= 0)
				// one more for the class
				{
					m_selectedAttributeSet = new int[attributeSet.Length + 1];
					m_selectedAttributeSet[attributeSet.Length] = m_trainInstances.classIndex();
				}
				else
				{
					m_selectedAttributeSet = new int[attributeSet.Length];
				}
				
				for (int i = 0; i < attributeSet.Length; i++)
				{
					m_selectedAttributeSet[i] = attributeSet[i];
				}
				
				m_selectionResults.Append("Selected attributes: ");
				
				for (int i = 0; i < attributeSet.Length; i++)
				{
					if (i == (attributeSet.Length - 1))
					{
						m_selectionResults.Append((attributeSet[i] + 1) + " : " + attributeSet.Length + "\n");
					}
					else
					{
						m_selectionResults.Append((attributeSet[i] + 1) + ",");
					}
				}
				
				for (int i = 0; i < attributeSet.Length; i++)
				{
					m_selectionResults.Append("                     " + m_trainInstances.attribute(attributeSet[i]).name() + "\n");
				}
			}
			
			// Cross validation should be called from here
			if (m_doXval == true)
			{
				m_selectionResults.Append(CrossValidateAttributes());
			}
			
			// set up the attribute filter with the selected attributes
			if (m_selectedAttributeSet != null && !m_doXval)
			{
				m_attributeFilter = new Remove();
				m_attributeFilter.SetAttributeIndicesArray(m_selectedAttributeSet);
				m_attributeFilter.set_InvertSelection(true);
				m_attributeFilter.setInputFormat(m_trainInstances);
			}
			
			// Save space
			m_trainInstances = new Instances(m_trainInstances, 0);
		}
		
		/// <summary> Perform attribute selection with a particular evaluator and
		/// a set of options specifying search method and options for the
		/// search method and evaluator.
		/// 
		/// </summary>
		/// <param name="ASEvaluator">an evaluator object
		/// </param>
		/// <param name="options">an array of options, not only for the evaluator
		/// but also the search method (if any) and an input data file
		/// </param>
		/// <param name="outAttributes">index 0 will contain the array of selected
		/// attribute indices
		/// </param>
		/// <param name="train">the input instances
		/// </param>
		/// <returns> the results of attribute selection as a String
		/// </returns>
		/// <exception cref="Exception">if incorrect options are supplied
		/// </exception>
		public static System.String SelectAttributes(ASEvaluation ASEvaluator, System.String[] options, Instances train)
		{
			int seed = 1, folds = 10;
			System.String cutString, foldsString, seedString, searchName;
			System.String classString;
			System.String searchClassName;
			System.String[] searchOptions = null; //new String [1];
			System.Random random;
			ASSearch searchMethod = null;
			bool doCrossVal = false;
			Range initialRange;
			int classIndex = - 1;
			int[] selectedAttributes;
			//UPGRADE_TODO: The equivalent in .NET for field 'java.lang.Double.MAX_VALUE' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			double cutoff = - System.Double.MaxValue;
			bool helpRequested = false;
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			initialRange = new Range();
			AttributeSelection trainSelector = new AttributeSelection();
			
			try
			{
				if (Utils.getFlag('h', options))
				{
					helpRequested = true;
				}
				
				// get basic options (options the same for all attribute selectors
				classString = Utils.getOption('C', options);
				
				if (classString.Length != 0)
				{
					if (classString.Equals("first"))
					{
						classIndex = 1;
					}
					else if (classString.Equals("last"))
					{
						classIndex = train.numAttributes();
					}
					else
					{
						classIndex = System.Int32.Parse(classString);
					}
				}
				
				if ((classIndex != - 1) && ((classIndex == 0) || (classIndex > train.numAttributes())))
				{
					throw new System.Exception("Class index out of range.");
				}
				
				if (classIndex != - 1)
				{
					train.ClassIndex=classIndex - 1;
				}
				else
				{
					//	classIndex = train.numAttributes();
					//	train.setClassIndex(classIndex - 1);
				}
				
				foldsString = Utils.getOption('X', options);
				
				if (foldsString.Length != 0)
				{
					folds = System.Int32.Parse(foldsString);
					doCrossVal = true;
				}
				
				trainSelector.Folds = folds;
				trainSelector.Xval = doCrossVal;
				
				seedString = Utils.getOption('N', options);
				
				if (seedString.Length != 0)
				{
					seed = System.Int32.Parse(seedString);
				}
				
				trainSelector.Seed = seed;
				
				searchName = Utils.getOption('S', options);
				
				if ((searchName.Length == 0) && (!(ASEvaluator is AttributeEvaluator)))
				{
					throw new System.Exception("No search method given.");
				}
				
				if (searchName.Length != 0)
				{
					searchName = searchName.Trim();
					// split off any search options
					int breakLoc = searchName.IndexOf(' ');
					searchClassName = searchName;
					System.String searchOptionsString = "";
					
					if (breakLoc != - 1)
					{
						searchClassName = searchName.Substring(0, (breakLoc) - (0));
						searchOptionsString = searchName.Substring(breakLoc).Trim();
						searchOptions = Utils.splitOptions(searchOptionsString);
					}
				}
				else
				{
					try
					{
						searchClassName = new System.Text.StringBuilder("weka.attributeSelection.Ranker").ToString();
						//UPGRADE_TODO: The differences in the format  of parameters for method 'java.lang.Class.forName'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
						searchMethod = (ASSearch) System.Activator.CreateInstance(System.Type.GetType(searchClassName));
					}
					catch (System.Exception e)
					{
						throw new System.Exception("Can't create Ranker object");
					}
				}
				
				// if evaluator is a subset evaluator
				// create search method and set its options (if any)
				if (searchMethod == null)
				{
					searchMethod = ASSearch.forName(searchClassName, searchOptions);
				}
				
				// set the search method
				trainSelector.Search = searchMethod;
			}
			catch (System.Exception e)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception('\n' + e.Message + makeOptionString(ASEvaluator, searchMethod));
			}
			
			try
			{
				// Set options for ASEvaluator
				if (ASEvaluator is OptionHandler)
				{
					((OptionHandler) ASEvaluator).Options=options;
				}
				
				/* // Set options for Search method
				if (searchMethod instanceof OptionHandler)
				{
				if (searchOptions != null)
				{
				((OptionHandler)searchMethod).setOptions(searchOptions);
				}
				}
				Utils.checkForRemainingOptions(searchOptions); */
			}
			catch (System.Exception e)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception("\n" + e.Message + makeOptionString(ASEvaluator, searchMethod));
			}
			
			try
			{
				Utils.checkForRemainingOptions(options);
			}
			catch (System.Exception e)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				throw new System.Exception('\n' + e.Message + makeOptionString(ASEvaluator, searchMethod));
			}
			
			if (helpRequested)
			{
				System.Console.Out.WriteLine(makeOptionString(ASEvaluator, searchMethod));
				//System.Environment.Exit(0);
			}
			
			// set the attribute evaluator
			trainSelector.Evaluator = ASEvaluator;
			
			// do the attribute selection
			trainSelector.SelectAttributes(train);
			
			// return the results string
			return trainSelector.toResultsString();
		}
		
		
		/// <summary> Assembles a text description of the attribute selection results.
		/// 
		/// </summary>
		/// <returns> a string describing the results of attribute selection.
		/// </returns>
		private System.String printSelectionResults()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			text.Append("\n\n=== Attribute Selection on all input data ===\n\n" + "Search Method:\n");
			//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			text.Append(m_searchMethod.ToString());
			text.Append("\nAttribute ");
			
			if (m_ASEvaluator is SubsetEvaluator)
			{
				text.Append("Subset Evaluator (");
			}
			else
			{
				text.Append("Evaluator (");
			}
			
			if (!(m_ASEvaluator is UnsupervisedSubsetEvaluator) && !(m_ASEvaluator is UnsupervisedAttributeEvaluator))
			{
				text.Append("supervised, ");
				text.Append("Class (");
				
				if (m_trainInstances.attribute(m_trainInstances.classIndex()).Numeric)
				{
					text.Append("numeric): ");
				}
				else
				{
					text.Append("nominal): ");
				}
				
				text.Append((m_trainInstances.classIndex() + 1) + " " + m_trainInstances.attribute(m_trainInstances.classIndex()).name() + "):\n");
			}
			else
			{
				text.Append("unsupervised):\n");
			}
			
			//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Object.toString' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
			text.Append(m_ASEvaluator.ToString() + "\n");
			return text.ToString();
		}
		
		
		/// <summary> Make up the help string giving all the command line options
		/// 
		/// </summary>
		/// <param name="ASEvaluator">the attribute evaluator to include options for
		/// </param>
		/// <param name="searchMethod">the search method to include options for
		/// </param>
		/// <returns> a string detailing the valid command line options
		/// </returns>
		private static System.String makeOptionString(ASEvaluation ASEvaluator, ASSearch searchMethod)
		{
			System.Text.StringBuilder optionsText = new System.Text.StringBuilder("");
			// General options
			optionsText.Append("\n\nGeneral options:\n\n");
			optionsText.Append("-h display this help\n");
			optionsText.Append("-I <name of input file>\n");
			optionsText.Append("\tSets training file.\n");
			optionsText.Append("-C <class index>\n");
			optionsText.Append("\tSets the class index for supervised attribute\n");
			optionsText.Append("\tselection. Default=last column.\n");
			optionsText.Append("-S <Class name>\n");
			optionsText.Append("\tSets search method for subset evaluators.\n");
			optionsText.Append("-X <number of folds>\n");
			optionsText.Append("\tPerform a cross validation.\n");
			optionsText.Append("-N <random number seed>\n");
			optionsText.Append("\tUse in conjunction with -X.\n");
			
			// Get attribute evaluator-specific options
			if (ASEvaluator is OptionHandler)
			{
				optionsText.Append("\nOptions specific to " + ASEvaluator.GetType().FullName + ":\n\n");
				System.Collections.IEnumerator enu = ((OptionHandler) ASEvaluator).listOptions();
				
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					Option option = (Option) enu.Current;
					optionsText.Append(option.synopsis() + '\n');
					optionsText.Append(option.description() + "\n");
				}
			}
			
			if (searchMethod != null)
			{
				if (searchMethod is OptionHandler)
				{
					optionsText.Append("\nOptions specific to " + searchMethod.GetType().FullName + ":\n\n");
					System.Collections.IEnumerator enu = ((OptionHandler) searchMethod).listOptions();
					
					//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
					while (enu.MoveNext())
					{
						//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
						Option option = (Option) enu.Current;
						optionsText.Append(option.synopsis() + '\n');
						optionsText.Append(option.description() + "\n");
					}
				}
			}
			else
			{
				if (ASEvaluator is SubsetEvaluator)
				{
					System.Console.Out.WriteLine("No search method given.");
				}
			}
			
			return optionsText.ToString();
		}
		
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="args">the options
		/// </param>
		
		public static void  Main(System.String[] args)
		{
			try
			{
				if (args.Length == 0)
				{
					throw new System.Exception("The first argument must be the name of an " + "attribute/subset evaluator");
				}
				
				System.String EvaluatorName = args[0];
				args[0] = "";
				ASEvaluation newEval = ASEvaluation.forName(EvaluatorName, null);
				System.Console.Out.WriteLine(SelectAttributes(newEval, args));
			}
			catch (System.Exception e)
			{
				//UPGRADE_TODO: The equivalent in .NET for method 'java.lang.Throwable.getMessage' may return a different value. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1043'"
				System.Console.Out.WriteLine(e.Message);
			}
		}
	}
}