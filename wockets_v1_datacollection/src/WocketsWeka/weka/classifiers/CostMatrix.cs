/*
*    CostMatrix.java
*    Copyright (C) 2001 Richard Kirkby
*
*/
using System;
using Matrix = weka.core.Matrix;
using Instances = weka.core.Instances;
using Utils = weka.core.Utils;
using WocketsWeka.Utils;

namespace weka.classifiers
{
	
	/// <summary> Class for storing and manipulating a misclassification cost matrix.
	/// The element at position i,j in the matrix is the penalty for classifying
	/// an instance of class j as class i.
	/// 
	/// </summary>
	/// <author>  Richard Kirkby (rkirkby@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.9.2.1 $
	/// </version>
    /// 
#if !PocketPC
    [Serializable()]  
#endif
	public class CostMatrix:Matrix
	{
		
		/// <summary>The deafult file extension for cost matrix files </summary>
		public static System.String FILE_EXTENSION = ".cost";
		
		/// <summary> Creates a cost matrix that is a copy of another.
		/// 
		/// </summary>
		/// <param name="toCopy">the matrix to copy.
		/// </param>
		public CostMatrix(CostMatrix toCopy):base(toCopy.size(), toCopy.size())
		{
			
			for (int x = 0; x < toCopy.size(); x++)
				for (int y = 0; y < toCopy.size(); y++)
					setXmlElement(x, y, toCopy.getXmlElement(x, y));
		}
		
		/// <summary> Creates a default cost matrix of a particular size. All values will be 0.
		/// 
		/// </summary>
		/// <param name="numOfClasses">the number of classes that the cost matrix holds.
		/// </param>
		public CostMatrix(int numOfClasses):base(numOfClasses, numOfClasses)
		{
		}
		
		/// <summary> Creates a cost matrix from a reader.
		/// 
		/// </summary>
		/// <param name="reader">the reader to get the values from.
		/// </param>
		/// <exception cref="Exception">if the matrix is invalid.
		/// </exception>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public CostMatrix(System.IO.StreamReader reader):base(reader)
		{
			
			// make sure that the matrix is square
			if (numRows() != numColumns())
				throw new System.Exception("Trying to create a non-square cost matrix");
		}
		
		/// <summary> Sets the cost of all correct classifications to 0, and all
		/// misclassifications to 1.
		/// 
		/// </summary>
		public virtual void  initialize()
		{
			
			for (int i = 0; i < size(); i++)
			{
				for (int j = 0; j < size(); j++)
				{
					setXmlElement(i, j, i == j?0.0:1.0);
				}
			}
		}
		
		/// <summary> Gets the size of the matrix.
		/// 
		/// </summary>
		/// <returns> the size.
		/// </returns>
		public virtual int size()
		{
			
			return numColumns();
		}
		
		/// <summary> Applies the cost matrix to a set of instances. If a random number generator is 
		/// supplied the instances will be resampled, otherwise they will be rewighted. 
		/// Adapted from code once sitting in Instances.java
		/// 
		/// </summary>
		/// <param name="data">the instances to reweight.
		/// </param>
		/// <param name="random">a random number generator for resampling, if null then instances are
		/// rewighted.
		/// </param>
		/// <returns> a new dataset reflecting the cost of misclassification.
		/// </returns>
		/// <exception cref="Exception">if the data has no class or the matrix in inappropriate.
		/// </exception>
		public virtual Instances applyCostMatrix(Instances data, System.Random random)
		{
			
			double sumOfWeightFactors = 0, sumOfMissClassWeights, sumOfWeights;
			double[] weightOfInstancesInClass, weightFactor, weightOfInstances;
			Instances newData;
			
			if (data.classIndex() < 0)
			{
				throw new System.Exception("Class index is not set!");
			}
			
			if (size() != data.numClasses())
			{
				throw new System.Exception("Misclassification cost matrix has " + "wrong format!");
			}
			
			weightFactor = new double[data.numClasses()];
			weightOfInstancesInClass = new double[data.numClasses()];
			for (int j = 0; j < data.numInstances(); j++)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				weightOfInstancesInClass[(int) data.instance(j).classValue()] += data.instance(j).weight();
			}
			sumOfWeights = Utils.sum(weightOfInstancesInClass);
			
			// normalize the matrix if not already
			for (int i = 0; i < size(); i++)
				if (!Utils.eq(getXmlElement(i, i), 0))
				{
					CostMatrix normMatrix = new CostMatrix(this);
					normMatrix.normalize();
					return normMatrix.applyCostMatrix(data, random);
				}
			
			for (int i = 0; i < data.numClasses(); i++)
			{
				
				// Using Kai Ming Ting's formula for deriving weights for 
				// the classes and Breiman's heuristic for multiclass 
				// problems.
				sumOfMissClassWeights = 0;
				for (int j = 0; j < data.numClasses(); j++)
				{
					if (Utils.sm(getXmlElement(i, j), 0))
					{
						throw new System.Exception("Neg. weights in misclassification " + "cost matrix!");
					}
					sumOfMissClassWeights += getXmlElement(i, j);
				}
				weightFactor[i] = sumOfMissClassWeights * sumOfWeights;
				sumOfWeightFactors += sumOfMissClassWeights * weightOfInstancesInClass[i];
			}
			for (int i = 0; i < data.numClasses(); i++)
			{
				weightFactor[i] /= sumOfWeightFactors;
			}
			
			// Store new weights
			weightOfInstances = new double[data.numInstances()];
			for (int i = 0; i < data.numInstances(); i++)
			{
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				weightOfInstances[i] = data.instance(i).weight() * weightFactor[(int) data.instance(i).classValue()];
			}
			
			// Change instances weight or do resampling
			if (random != null)
			{
				return data.resampleWithWeights(random, weightOfInstances);
			}
			else
			{
				Instances instances = new Instances(data);
				for (int i = 0; i < data.numInstances(); i++)
				{
					instances.instance(i).Weight = weightOfInstances[i];
				}
				return instances;
			}
		}
		
		/// <summary> Calculates the expected misclassification cost for each possible class value,
		/// given class probability estimates. 
		/// 
		/// </summary>
		/// <param name="classProbs">the class probability estimates.
		/// </param>
		/// <returns> the expected costs.
		/// </returns>
		/// <exception cref="Exception">if the wrong number of class probabilities is supplied.
		/// </exception>
		public virtual double[] expectedCosts(double[] classProbs)
		{
			
			if (classProbs.Length != size())
				throw new System.Exception("Length of probability estimates don't match cost matrix");
			
			double[] costs = new double[size()];
			
			for (int x = 0; x < size(); x++)
				for (int y = 0; y < size(); y++)
					costs[x] += classProbs[y] * getXmlElement(y, x);
			
			return costs;
		}
		
		/// <summary> Gets the maximum cost for a particular class value.
		/// 
		/// </summary>
		/// <param name="classVal">the class value.
		/// </param>
		/// <returns> the maximum cost.
		/// </returns>
		public virtual double getMaxCost(int classVal)
		{
			
			double maxCost = System.Double.NegativeInfinity;
			
			for (int i = 0; i < size(); i++)
			{
				double cost = getXmlElement(classVal, i);
				if (cost > maxCost)
					maxCost = cost;
			}
			
			return maxCost;
		}
		
		/// <summary> Normalizes the matrix so that the diagonal contains zeros.
		/// 
		/// </summary>
		public virtual void  normalize()
		{
			
			for (int y = 0; y < size(); y++)
			{
				double diag = getXmlElement(y, y);
				for (int x = 0; x < size(); x++)
					setXmlElement(x, y, getXmlElement(x, y) - diag);
			}
		}
		
		/// <summary> Loads a cost matrix in the old format from a reader. Adapted from code once sitting 
		/// in Instances.java
		/// 
		/// </summary>
		/// <param name="reader">the reader to get the values from.
		/// </param>
		/// <exception cref="Exception">if the matrix cannot be read correctly.
		/// </exception>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.io.Reader' and 'System.IO.StreamReader' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public virtual void  readOldFormat(System.IO.StreamReader reader)
		{
			
			StreamTokenizer tokenizer;
			Token currentToken;
			double firstIndex, secondIndex, weight;
			
			tokenizer = new StreamTokenizer(reader);
			
			initialize();
			
			tokenizer.Settings.CommentChar('%');
			tokenizer.Settings.GrabEol=true;
            tokenizer.NextToken(out currentToken);
			//while (SupportClass.StreamTokenizerSupport.TT_EOF != (currentToken = tokenizer.NextToken()))
            while (!(currentToken is EofToken))
			{
				
				// Skip empty lines 
				//if (currentToken == SupportClass.StreamTokenizerSupport.TT_EOL)
                if (currentToken is EolToken)
				{
					continue;
				}
				
				// Get index of first class.
				//if (currentToken != SupportClass.StreamTokenizerSupport.TT_NUMBER)
                if (!((currentToken is FloatToken)|| (currentToken is IntToken)))
				{
					throw new System.Exception("Only numbers and comments allowed " + "in cost file!");
				}
				//firstIndex = tokenizer.nval;
                firstIndex = Convert.ToDouble(currentToken.StringValue);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if (!Utils.eq((double) firstIndex, firstIndex))
				{
					throw new System.Exception("First number in line has to be " + "index of a class!");
				}
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if ((int) firstIndex >= size())
				{
					throw new System.Exception("Class index out of range!");
				}
				
				// Get index of second class.
				//if (SupportClass.StreamTokenizerSupport.TT_EOF == (currentToken = tokenizer.NextToken()))
                tokenizer.NextToken(out currentToken);
                if (currentToken is EofToken)
				{
					throw new System.Exception("Premature end of file!");
				}
				//if (currentToken == SupportClass.StreamTokenizerSupport.TT_EOL)
                if (currentToken is EolToken)
				{
					throw new System.Exception("Premature end of line!");
				}
				//if (currentToken != SupportClass.StreamTokenizerSupport.TT_NUMBER)
                if  (!((currentToken is IntToken) || (currentToken is FloatToken)))
				{
					throw new System.Exception("Only numbers and comments allowed " + "in cost file!");
				}
				//secondIndex = tokenizer.nval;
                secondIndex = Convert.ToDouble(currentToken.StringValue);
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if (!Utils.eq((double) secondIndex, secondIndex))
				{
					throw new System.Exception("Second number in line has to be " + "index of a class!");
				}
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if ((int) secondIndex >= size())
				{
					throw new System.Exception("Class index out of range!");
				}
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if ((int) secondIndex == (int) firstIndex)
				{
					throw new System.Exception("Diagonal of cost matrix non-zero!");
				}
				
				// Get cost factor.

                tokenizer.NextToken(out currentToken);
                if (currentToken is EofToken)

				//if (SupportClass.StreamTokenizerSupport.TT_EOF == (currentToken = tokenizer.NextToken()))
				{
					throw new System.Exception("Premature end of file!");
				}
				//if (currentToken == SupportClass.StreamTokenizerSupport.TT_EOL)
                if (currentToken is EolToken)
				{
					throw new System.Exception("Premature end of line!");
				}

				//if (currentToken != SupportClass.StreamTokenizerSupport.TT_NUMBER)
                if (!((currentToken is IntToken) || (currentToken is FloatToken)))
				{
					throw new System.Exception("Only numbers and comments allowed " + "in cost file!");
				}
                weight = Convert.ToDouble(currentToken.StringValue);
				if (!Utils.gr(weight, 0))
				{
					throw new System.Exception("Only positive weights allowed!");
				}
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				setXmlElement((int) firstIndex, (int) secondIndex, weight);

                tokenizer.NextToken(out currentToken);
			}
		}
	}
}