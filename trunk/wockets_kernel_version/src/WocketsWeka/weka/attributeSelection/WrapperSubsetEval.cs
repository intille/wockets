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
*    WrapperSubsetEval.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
//UPGRADE_TODO: The package 'weka.classifiers' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.classifiers;
//UPGRADE_TODO: The type 'weka.classifiers.rules.ZeroR' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using ZeroR = weka.classifiers.rules.ZeroR;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.Remove' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Remove = weka.filters.unsupervised.attribute.Remove;
//UPGRADE_TODO: The type 'weka.filters.Filter' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Filter = weka.filters.Filter;
namespace weka.attributeSelection
{
	
	/// <summary> Wrapper attribute subset evaluator. <p>
	/// For more information see: <br>
	/// 
	/// Kohavi, R., John G., Wrappers for Feature Subset Selection. 
	/// In <i>Artificial Intelligence journal</i>, special issue on relevance, 
	/// Vol. 97, Nos 1-2, pp.273-324. <p>
	/// 
	/// Valid options are:<p>
	/// 
	/// -B <base learner> <br>
	/// Class name of base learner to use for accuracy estimation.
	/// Place any classifier options last on the command line following a
	/// "--". Eg  -B weka.classifiers.bayes.NaiveBayes ... -- -K <p>
	/// 
	/// -F <num> <br>
	/// Number of cross validation folds to use for estimating accuracy.
	/// <default=5> <p>
	/// 
	/// -T <num> <br>
	/// Threshold by which to execute another cross validation (standard deviation
	/// ---expressed as a percentage of the mean). <p>
	/// 
	/// -R <seed> <br>
	/// Seed for cross validation accuracy estimation.
	/// (default = 1) <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.22.2.1 $
	/// </version>
	[Serializable]
	public class WrapperSubsetEval:SubsetEvaluator, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current settings of WrapperSubsetEval.
		/// 
		/// </summary>
		/// <returns> an array of strings suitable for passing to setOptions()
		/// </returns>
		/// <summary> Parses a given list of options.
		/// 
		/// Valid options are:<p>
		/// 
		/// -B <base learner> <br>
		/// Class name of base learner to use for accuracy estimation.
		/// Place any classifier options last on the command line following a
		/// "--". Eg  -B weka.classifiers.bayes.NaiveBayes ... -- -K <p>
		/// 
		/// -F <num> <br>
		/// Number of cross validation folds to use for estimating accuracy.
		/// <default=5> <p>
		/// 
		/// -T <num> <br>
		/// Threshold by which to execute another cross validation (standard deviation
		/// ---expressed as a percentage of the mean). <p>
		/// 
		/// -R <seed> <br>
		/// Seed for cross validation accuracy estimation.
		/// (default = 1) <p>
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
				System.String[] classifierOptions = new System.String[0];
				
				if ((m_BaseClassifier != null) && (m_BaseClassifier is OptionHandler))
				{
					classifierOptions = ((OptionHandler) m_BaseClassifier).Options;
				}
				
				System.String[] options = new System.String[9 + classifierOptions.Length];
				int current = 0;
				
				if (Classifier != null)
				{
					options[current++] = "-B";
                    options[current++] = Classifier.GetType().ToString();//.getClass().getName();
				}
				
				options[current++] = "-F";
				options[current++] = "" + Folds;
				options[current++] = "-T";
				options[current++] = "" + Threshold;
				options[current++] = "-R";
				options[current++] = "" + Seed;
				options[current++] = "--";
				Array.Copy(classifierOptions, 0, options, current, classifierOptions.Length);
				current += classifierOptions.Length;
				
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
				optionString = Utils.getOption('B', value);
				
				if (optionString.Length == 0)
				{
					throw new System.Exception("A learning scheme must be specified with" + "-B option");
				}
				
				Classifier = Classifier.forName(optionString, Utils.partitionOptions(value));
				optionString = Utils.getOption('F', value);
				
				if (optionString.Length != 0)
				{
					Folds = System.Int32.Parse(optionString);
				}
				
				optionString = Utils.getOption('R', value);
				if (optionString.Length != 0)
				{
					Seed = System.Int32.Parse(optionString);
				}
				
				//       optionString = Utils.getOption('S',options);
				//       if (optionString.length() != 0)
				//         {
				//  	 seed = Integer.parseInt(optionString);
				//         }
				optionString = Utils.getOption('T', value);
				
				if (optionString.Length != 0)
				{
					System.Double temp;
					temp = System.Double.Parse(optionString);
					Threshold = temp;
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the value of the threshold
		/// 
		/// </summary>
		/// <returns> the threshold as a double
		/// </returns>
		/// <summary> Set the value of the threshold for repeating cross validation
		/// 
		/// </summary>
		/// <param name="t">the value of the threshold
		/// </param>
		virtual public double Threshold
		{
			get
			{
				return m_threshold;
			}
			
			set
			{
				m_threshold = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the number of folds used for accuracy estimation
		/// 
		/// </summary>
		/// <returns> the number of folds
		/// </returns>
		/// <summary> Set the number of folds to use for accuracy estimation
		/// 
		/// </summary>
		/// <param name="f">the number of folds
		/// </param>
		virtual public int Folds
		{
			get
			{
				return m_folds;
			}
			
			set
			{
				m_folds = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the random number seed used for cross validation
		/// 
		/// </summary>
		/// <returns> the seed
		/// </returns>
		/// <summary> Set the seed to use for cross validation
		/// 
		/// </summary>
		/// <param name="s">the seed
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
		/// <summary> Get the classifier used as the base learner.
		/// 
		/// </summary>
		/// <returns> the classifier used as the classifier
		/// </returns>
		/// <summary> Set the classifier to use for accuracy estimation
		/// 
		/// </summary>
		/// <param name="newClassifier">the Classifier to use.
		/// </param>
		virtual public Classifier Classifier
		{
			get
			{
				return m_BaseClassifier;
			}
			
			set
			{
				m_BaseClassifier = value;
			}
			
		}
		
		/// <summary>training instances </summary>
		private Instances m_trainInstances;
		/// <summary>class index </summary>
		private int m_classIndex;
		/// <summary>number of attributes in the training data </summary>
		private int m_numAttribs;
		/// <summary>number of instances in the training data </summary>
		private int m_numInstances;
		/// <summary>holds an evaluation object </summary>
		private Evaluation m_Evaluation;
		/// <summary>holds the base classifier object </summary>
		private Classifier m_BaseClassifier;
		/// <summary>number of folds to use for cross validation </summary>
		private int m_folds;
		/// <summary>random number seed </summary>
		private int m_seed;
		/// <summary> the threshold by which to do further cross validations when
		/// estimating the accuracy of a subset
		/// </summary>
		private double m_threshold;
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "WrapperSubsetEval:\n\n" + "Evaluates attribute sets by using a learning scheme. Cross " + "validation is used to estimate the accuracy of the learning " + "scheme for a set of attributes.\n";
		}
		
		/// <summary> Constructor. Calls restOptions to set default options
		/// 
		/// </summary>
		public WrapperSubsetEval()
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
			newVector.Add(new Option("\tclass name of base learner to use for" + "\n\taccuracy estimation. Place any" + "\n\tclassifier options LAST on the" + "\n\tcommand line following a \"--\"." + "\n\teg. -B weka.classifiers.bayes.NaiveBayes ... " + "-- -K", "B", 1, "-B <base learner>"));
			newVector.Add(new Option("\tnumber of cross validation folds to " + "use\n\tfor estimating accuracy." + "\n\t(default=5)", "F", 1, "-F <num>"));
			newVector.Add(new Option("\tSeed for cross validation accuracy " + "\n\testimation." + "\n\t(default = 1)", "R", 1, "-R <seed>"));
			newVector.Add(new Option("\tthreshold by which to execute " + "another cross validation" + "\n\t(standard deviation---" + "expressed as a percentage of the " + "mean).\n\t(default=0.01(1%))", "T", 1, "-T <num>"));
			
			if ((m_BaseClassifier != null) && (m_BaseClassifier is OptionHandler))
			{
                newVector.Add(new Option("", "", 0, "\nOptions specific to" + "scheme " + m_BaseClassifier.GetType().ToString() + ":"));
				System.Collections.IEnumerator enu = ((OptionHandler) m_BaseClassifier).listOptions();
				
				//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
				while (enu.MoveNext())
				{
					//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
					newVector.Add(enu.Current);
				}
			}
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String thresholdTipText()
		{
			return "Repeat xval if stdev of mean exceeds this value.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String foldsTipText()
		{
			return "Number of xval folds to use when estimating subset accuracy.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String seedTipText()
		{
			return "Seed to use for randomly generating xval splits.";
		}
		
		/// <summary> Returns the tip text for this property</summary>
		/// <returns> tip text for this property suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String classifierTipText()
		{
			return "Classifier to use for estimating the accuracy of subsets";
		}
		
		
		protected internal virtual void  resetOptions()
		{
			m_trainInstances = null;
			m_Evaluation = null;
			m_BaseClassifier = new ZeroR();
			m_folds = 5;
			m_seed = 1;
			m_threshold = 0.01;
		}
		
		
		/// <summary> Generates a attribute evaluator. Has to initialize all fields of the 
		/// evaluator that are not being set via options.
		/// 
		/// </summary>
		/// <param name="data">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the evaluator has not been 
		/// generated successfully
		/// </exception>
		public override void  buildEvaluator(Instances data)
		{
			if (data.checkForStringAttributes())
			{
				throw new Exception("Can't handle string attributes!");
			}
			
			m_trainInstances = data;
			m_classIndex = m_trainInstances.classIndex();
			m_numAttribs = m_trainInstances.numAttributes();
			m_numInstances = m_trainInstances.numInstances();
		}
		
		
		/// <summary> Evaluates a subset of attributes
		/// 
		/// </summary>
		/// <param name="subset">a bitset representing the attribute subset to be 
		/// evaluated 
		/// </param>
		/// <exception cref="Exception">if the subset could not be evaluated
		/// </exception>
		public override double evaluateSubset(System.Collections.BitArray subset)
		{
			double errorRate = 0;
			double[] repError = new double[5];
			bool ok = true;
			int numAttributes = 0;
			int i, j;
			//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
			System.Random Rnd = new System.Random((System.Int32) m_seed);
			Remove delTransform = new Remove();
            delTransform.set_InvertSelection(true);//.setInvertSelection(true);
			// copy the instances
			Instances trainCopy = new Instances(m_trainInstances);
			
			// count attributes set in the BitSet
			for (i = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					numAttributes++;
				}
			}
			
			// set up an array of attribute indexes for the filter (+1 for the class)
			int[] featArray = new int[numAttributes + 1];
			
			for (i = 0, j = 0; i < m_numAttribs; i++)
			{
				if (subset.Get(i))
				{
					featArray[j++] = i;
				}
			}
			
			featArray[j] = m_classIndex;
			delTransform.SetAttributeIndicesArray(featArray);
			delTransform.setInputFormat(trainCopy);
			trainCopy = Filter.useFilter(trainCopy, delTransform);
			
			// max of 5 repititions ofcross validation
			for (i = 0; i < 5; i++)
			{
				m_Evaluation = new Evaluation(trainCopy);
				m_Evaluation.crossValidateModel(m_BaseClassifier, trainCopy, m_folds, Rnd);
				repError[i] = m_Evaluation.errorRate();
				
				// check on the standard deviation
				if (!repeat(repError, i + 1))
				{
					i++;
					break;
				}
			}
			
			for (j = 0; j < i; j++)
			{
				errorRate += repError[j];
			}
			
			errorRate /= (double) i;
			m_Evaluation = null;
			return - errorRate;
		}
		
		
		/// <summary> Returns a string describing the wrapper
		/// 
		/// </summary>
		/// <returns> the description as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainInstances == null)
			{
				text.Append("\tWrapper subset evaluator has not been built yet\n");
			}
			else
			{
				text.Append("\tWrapper Subset Evaluator\n");
                text.Append("\tLearning scheme: " + Classifier.GetType().ToString() + "\n");
				text.Append("\tScheme options: ");
				System.String[] classifierOptions = new System.String[0];
				
				if (m_BaseClassifier is OptionHandler)
				{
					classifierOptions = ((OptionHandler) m_BaseClassifier).Options;
					
					for (int i = 0; i < classifierOptions.Length; i++)
					{
						text.Append(classifierOptions[i] + " ");
					}
				}
				
				text.Append("\n");
				if (m_trainInstances.attribute(m_classIndex).Numeric)
				{
					text.Append("\tAccuracy estimation: RMSE\n");
				}
				else
				{
					text.Append("\tAccuracy estimation: classification error\n");
				}
				
				text.Append("\tNumber of folds for accuracy estimation: " + m_folds + "\n");
			}
			
			return text.ToString();
		}
		
		
		/// <summary> decides whether to do another repeat of cross validation. If the
		/// standard deviation of the cross validations
		/// is greater than threshold% of the mean (default 1%) then another 
		/// repeat is done. 
		/// 
		/// </summary>
		/// <param name="repError">an array of cross validation results
		/// </param>
		/// <param name="entries">the number of cross validations done so far
		/// </param>
		/// <returns> true if another cv is to be done
		/// </returns>
		private bool repeat(double[] repError, int entries)
		{
			int i;
			double mean = 0;
			double variance = 0;
			
			if (entries == 1)
			{
				return true;
			}
			
			for (i = 0; i < entries; i++)
			{
				mean += repError[i];
			}
			
			mean /= (double) entries;
			
			for (i = 0; i < entries; i++)
			{
				variance += ((repError[i] - mean) * (repError[i] - mean));
			}
			
			variance /= (double) entries;
			
			if (variance > 0)
			{
				variance = System.Math.Sqrt(variance);
			}
			
			if ((variance / mean) > m_threshold)
			{
				return true;
			}
			
			return false;
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
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new WrapperSubsetEval(), args));
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