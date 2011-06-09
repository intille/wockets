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
*    OneRAttributeEval.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
//UPGRADE_TODO: The package 'weka.classifiers' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.classifiers;
//UPGRADE_TODO: The type 'weka.filters.unsupervised.attribute.Remove' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Remove = weka.filters.unsupervised.attribute.Remove;
//UPGRADE_TODO: The type 'weka.filters.Filter' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Filter = weka.filters.Filter;
namespace weka.attributeSelection
{
	
	/// <summary> Class for Evaluating attributes individually by using the OneR
	/// classifier. <p>
	/// 
	/// -S <seed> <br>
	/// Set the seed for cross validation (default = 1). <p>
	/// 
	/// -F <folds> <br>
	/// Set the number of folds for cross validation (default = 10). <p>
	/// 
	/// -B <minimum bucket size> <br>
	/// Set the minimum number of objects per bucket (passed on to
	/// OneR, default = 6). <p>
	/// 
	/// -D <br>
	/// Use the training data to evaluate attributes rather than cross validation. <p>
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.14 $
	/// </version>
	[Serializable]
	public class OneRAttributeEval:AttributeEvaluator, OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the random number seed
		/// 
		/// </summary>
		/// <returns> an <code>int</code> value
		/// </returns>
		/// <summary> Set the random number seed for cross validation
		/// 
		/// </summary>
		/// <param name="seed">the seed to use
		/// </param>
		virtual public int Seed
		{
			get
			{
				return m_randomSeed;
			}
			
			set
			{
				m_randomSeed = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the number of folds used for cross validation
		/// 
		/// </summary>
		/// <returns> the number of folds
		/// </returns>
		/// <summary> Set the number of folds to use for cross validation
		/// 
		/// </summary>
		/// <param name="folds">the number of folds
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
				if (m_folds < 2)
				{
					m_folds = 2;
				}
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Returns true if the training data is to be used for evaluation
		/// 
		/// </summary>
		/// <returns> true if training data is to be used for evaluation
		/// </returns>
		/// <summary> Use the training data to evaluate attributes rather than cross validation
		/// 
		/// </summary>
		/// <param name="e">true if training data is to be used for evaluation
		/// </param>
		virtual public bool EvalUsingTrainingData
		{
			get
			{
				return m_evalUsingTrainingData;
			}
			
			set
			{
				m_evalUsingTrainingData = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Get the minimum bucket size used by oneR
		/// 
		/// </summary>
		/// <returns> the minimum bucket size used
		/// </returns>
		/// <summary> Set the minumum bucket size used by OneR
		/// 
		/// </summary>
		/// <param name="minB">the minimum bucket size to use
		/// </param>
		virtual public int MinimumBucketSize
		{
			get
			{
				return m_minBucketSize;
			}
			
			set
			{
				m_minBucketSize = value;
			}
			
		}
		/// <summary> Parses a given list of options. Valid options are:<p>
		/// 
		/// -S <seed> <br>
		/// Set the seed for cross validation (default = 1). <p>
		/// 
		/// -F <folds> <br>
		/// Set the number of folds for cross validation (default = 10). <p>
		/// 
		/// -B <minimum bucket size> <br>
		/// Set the minimum number of objects per bucket (passed on to
		/// OneR, default = 6). <p>
		/// 
		/// -D <br>
		/// Use the training data to evaluate attributes rather than cross validation. <p>
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// </exception>
		virtual public System.String[] Options
		{
			get
			{
				System.String[] options = new System.String[7];
				int current = 0;
				
				if (EvalUsingTrainingData)
				{
					options[current++] = "-D";
				}
				
				options[current++] = "-S";
				options[current++] = "" + Seed;
				options[current++] = "-F";
				options[current++] = "" + Folds;
				options[current++] = "-B";
				options[current++] = "" + MinimumBucketSize;
				
				while (current < options.Length)
				{
					options[current++] = "";
				}
				return options;
			}
			
			set
			{
				System.String temp = Utils.getOption('S', value);
				
				if (temp.Length != 0)
				{
					Seed = System.Int32.Parse(temp);
				}
				
				temp = Utils.getOption('F', value);
				if (temp.Length != 0)
				{
					Folds = System.Int32.Parse(temp);
				}
				
				temp = Utils.getOption('B', value);
				if (temp.Length != 0)
				{
					MinimumBucketSize = System.Int32.Parse(temp);
				}
				
				EvalUsingTrainingData = Utils.getFlag('D', value);
				Utils.checkForRemainingOptions(value);
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
		
		/// <summary>Random number seed </summary>
		private int m_randomSeed;
		
		/// <summary>Number of folds for cross validation </summary>
		private int m_folds;
		
		/// <summary>Use training data to evaluate merit rather than x-val </summary>
		private bool m_evalUsingTrainingData;
		
		/// <summary>Passed on to OneR </summary>
		private int m_minBucketSize;
		
		
		/// <summary> Returns a string describing this attribute evaluator</summary>
		/// <returns> a description of the evaluator suitable for
		/// displaying in the explorer/experimenter gui
		/// </returns>
		public virtual System.String globalInfo()
		{
			return "OneRAttributeEval :\n\nEvaluates the worth of an attribute by " + "using the OneR classifier.\n";
		}
		
		/// <summary> Returns a string for this option suitable for display in the gui
		/// as a tip text
		/// 
		/// </summary>
		/// <returns> a string describing this option
		/// </returns>
		public virtual System.String seedTipText()
		{
			return "Set the seed for use in cross validation.";
		}
		
		/// <summary> Returns a string for this option suitable for display in the gui
		/// as a tip text
		/// 
		/// </summary>
		/// <returns> a string describing this option
		/// </returns>
		public virtual System.String foldsTipText()
		{
			return "Set the number of folds for cross validation.";
		}
		
		/// <summary> Returns a string for this option suitable for display in the gui
		/// as a tip text
		/// 
		/// </summary>
		/// <returns> a string describing this option
		/// </returns>
		public virtual System.String evalUsingTrainingDataTipText()
		{
			return "Use the training data to evaluate attributes rather than " + "cross validation.";
		}
		
		/// <summary> Returns a string for this option suitable for display in the gui
		/// as a tip text
		/// 
		/// </summary>
		/// <returns> a string describing this option
		/// </returns>
		public virtual System.String minimumBucketSizeTipText()
		{
			return "The minimum number of objects in a bucket " + "(passed to OneR).";
		}
		
		/// <summary> Returns an enumeration describing the available options.
		/// 
		/// </summary>
		/// <returns> an enumeration of all the available options.
		/// </returns>
		public virtual System.Collections.IEnumerator listOptions()
		{
			
			System.Collections.ArrayList newVector = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(4));
			
			newVector.Add(new Option("\tRandom number seed for cross validation (default = 1)", "S", 1, "-S <seed>"));
			
			newVector.Add(new Option("\tNumber of folds for cross validation (default = 10)", "F", 1, "-F <folds>"));
			
			newVector.Add(new Option("\tUse training data for evaluation rather than cross validaton", "D", 0, "-D"));
			
			newVector.Add(new Option("\tMinimum number of objects in a bucket (passed on to " + "OneR, default = 6)", "B", 1, "-B <minimum bucket size>"));
			
			return newVector.GetEnumerator();
		}
		
		/// <summary> Constructor</summary>
		public OneRAttributeEval()
		{
			resetOptions();
		}
		
		
		/// <summary> Initializes a OneRAttribute attribute evaluator.
		/// Discretizes all attributes that are numeric.
		/// 
		/// </summary>
		/// <param name="data">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the evaluator has not been 
		/// generated successfully
		/// </exception>
		public override void  buildEvaluator(Instances data)
		{
			m_trainInstances = data;
			
			if (m_trainInstances.checkForStringAttributes())
			{
				throw new Exception("Can't handle string attributes!");
			}
			
			m_classIndex = m_trainInstances.classIndex();
			m_numAttribs = m_trainInstances.numAttributes();
			m_numInstances = m_trainInstances.numInstances();
			
			if (m_trainInstances.attribute(m_classIndex).Numeric)
			{
				throw new System.Exception("Class must be nominal!");
			}
		}
		
		
		/// <summary> rests to defaults.</summary>
		protected internal virtual void  resetOptions()
		{
			m_trainInstances = null;
			m_randomSeed = 1;
			m_folds = 10;
			m_evalUsingTrainingData = false;
			m_minBucketSize = 6; // default used by OneR
		}
		
		
		/// <summary> evaluates an individual attribute by measuring the amount
		/// of information gained about the class given the attribute.
		/// 
		/// </summary>
		/// <param name="attribute">the index of the attribute to be evaluated
		/// </param>
		/// <exception cref="Exception">if the attribute could not be evaluated
		/// </exception>
		public override double evaluateAttribute(int attribute)
		{
			int[] featArray = new int[2]; // feat + class
			double errorRate;
			Evaluation o_Evaluation;
			Remove delTransform = new Remove();
			delTransform.set_InvertSelection(true);
			// copy the instances
			Instances trainCopy = new Instances(m_trainInstances);
			featArray[0] = attribute;
			featArray[1] = trainCopy.classIndex();
			delTransform.SetAttributeIndicesArray(featArray);
			delTransform.setInputFormat(trainCopy);
			trainCopy = Filter.useFilter(trainCopy, delTransform);
			o_Evaluation = new Evaluation(trainCopy);
			System.String[] oneROpts = new System.String[]{"-B", "" + MinimumBucketSize};
			Classifier oneR = Classifier.forName("weka.classifiers.rules.OneR", oneROpts);
			if (m_evalUsingTrainingData)
			{
				oneR.buildClassifier(trainCopy);
				o_Evaluation.evaluateModel(oneR, trainCopy);
			}
			else
			{
				/*      o_Evaluation.crossValidateModel("weka.classifiers.rules.OneR", 
				trainCopy, 10, 
				null, new Random(m_randomSeed)); */
				//UPGRADE_TODO: The differences in the expected value  of parameters for constructor 'java.util.Random.Random'  may cause compilation errors.  "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1092'"
				o_Evaluation.crossValidateModel(oneR, trainCopy, m_folds, new System.Random((System.Int32) m_randomSeed));
			}
			errorRate = o_Evaluation.errorRate();
			return (1 - errorRate) * 100.0;
		}
		
		
		/// <summary> Return a description of the evaluator</summary>
		/// <returns> description as a string
		/// </returns>
		public override System.String ToString()
		{
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			
			if (m_trainInstances == null)
			{
				text.Append("\tOneR feature evaluator has not been built yet");
			}
			else
			{
				text.Append("\tOneR feature evaluator.\n\n");
				text.Append("\tUsing ");
				if (m_evalUsingTrainingData)
				{
					text.Append("training data for evaluation of attributes.");
				}
				else
				{
					text.Append("" + Folds + " fold cross validation for evaluating " + "attributes.");
				}
				text.Append("\n\tMinimum bucket size for OneR: " + MinimumBucketSize);
			}
			
			text.Append("\n");
			return text.ToString();
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
				System.Console.Out.WriteLine(AttributeSelection.SelectAttributes(new OneRAttributeEval(), args));
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