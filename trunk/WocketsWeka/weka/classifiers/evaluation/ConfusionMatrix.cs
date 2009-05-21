/*
*    NominalPrediction.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
//UPGRADE_TODO: The type 'weka.core.Matrix' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Matrix = weka.core.Matrix;
using FastVector = weka.core.FastVector;
using Utils = weka.core.Utils;
//UPGRADE_TODO: The type 'weka.classifiers.CostMatrix' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using CostMatrix = weka.classifiers.CostMatrix;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Cells of this matrix correspond to counts of the number (or weight)
	/// of predictions for each actual value / predicted value combination.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.5.2.1 $
	/// </version>
	public class ConfusionMatrix:Matrix
	{
		
		/// <summary>Stores the names of the classes </summary>
		protected internal System.String[] m_ClassNames;
		
		/// <summary> Creates the confusion matrix with the given class names.
		/// 
		/// </summary>
		/// <param name="classNames">an array containing the names the classes.
		/// </param>
		public ConfusionMatrix(System.String[] classNames):base(classNames.Length, classNames.Length)
		{
			m_ClassNames = new System.String[classNames.Length];
			classNames.CopyTo(m_ClassNames, 0);
		}
		
		/// <summary> Makes a copy of this ConfusionMatrix after applying the
		/// supplied CostMatrix to the cells. The resulting ConfusionMatrix
		/// can be used to get cost-weighted statistics.
		/// 
		/// </summary>
		/// <param name="costs">the CostMatrix.
		/// </param>
		/// <returns> a ConfusionMatrix that has had costs applied.
		/// </returns>
		/// <exception cref="Exception">if the CostMatrix is not of the same size
		/// as this ConfusionMatrix.
		/// </exception>
		public virtual ConfusionMatrix makeWeighted(CostMatrix costs)
		{
			
			if (costs.size() != size())
			{
				throw new System.Exception("Cost and confusion matrices must be the same size");
			}
			ConfusionMatrix weighted = new ConfusionMatrix(m_ClassNames);
			for (int row = 0; row < size(); row++)
			{
				for (int col = 0; col < size(); col++)
				{
					weighted.setXmlElement(row, col, getXmlElement(row, col) * costs.getXmlElement(row, col));
				}
			}
			return weighted;
		}
		
		
		/// <summary> Creates and returns a clone of this object.
		/// 
		/// </summary>
		/// <returns> a clone of this instance.
		/// </returns>
		public virtual System.Object clone()
		{
			
			ConfusionMatrix m = (ConfusionMatrix) base.Clone();
			m.m_ClassNames = new System.String[m_ClassNames.Length];
			m_ClassNames.CopyTo(m.m_ClassNames, 0);
			return m;
		}
		
		/// <summary> Gets the number of classes.
		/// 
		/// </summary>
		/// <returns> the number of classes
		/// </returns>
		public virtual int size()
		{
			
			return m_ClassNames.Length;
		}
		
		/// <summary> Gets the name of one of the classes.
		/// 
		/// </summary>
		/// <param name="index">the index of the class.
		/// </param>
		/// <returns> the class name.
		/// </returns>
		public virtual System.String className(int index)
		{
			
			return m_ClassNames[index];
		}
		
		/// <summary> Includes a prediction in the confusion matrix.
		/// 
		/// </summary>
		/// <param name="pred">the NominalPrediction to include
		/// </param>
		/// <exception cref="Exception">if no valid prediction was made (i.e. 
		/// unclassified).
		/// </exception>
		public virtual void  addPrediction(NominalPrediction pred)
		{
			
			if (pred.predicted() == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE)
			{
				throw new System.Exception("No predicted value given.");
			}
			if (pred.actual() == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE)
			{
				throw new System.Exception("No actual value given.");
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			addElement((int) pred.actual(), (int) pred.predicted(), pred.weight());
		}
		
		/// <summary> Includes a whole bunch of predictions in the confusion matrix.
		/// 
		/// </summary>
		/// <param name="predictions">a FastVector containing the NominalPredictions
		/// to include
		/// </param>
		/// <exception cref="Exception">if no valid prediction was made (i.e. 
		/// unclassified).
		/// </exception>
		public virtual void  addPredictions(FastVector predictions)
		{
			
			for (int i = 0; i < predictions.size(); i++)
			{
				addPrediction((NominalPrediction) predictions.elementAt(i));
			}
		}
		
		
		/// <summary> Gets the performance with respect to one of the classes
		/// as a TwoClassStats object.
		/// 
		/// </summary>
		/// <param name="classIndex">the index of the class of interest.
		/// </param>
		/// <returns> the generated TwoClassStats object.
		/// </returns>
		public virtual TwoClassStats getTwoClassStats(int classIndex)
		{
			
			double fp = 0, tp = 0, fn = 0, tn = 0;
			for (int row = 0; row < size(); row++)
			{
				for (int col = 0; col < size(); col++)
				{
					if (row == classIndex)
					{
						if (col == classIndex)
						{
							tp += getXmlElement(row, col);
						}
						else
						{
							fn += getXmlElement(row, col);
						}
					}
					else
					{
						if (col == classIndex)
						{
							fp += getXmlElement(row, col);
						}
						else
						{
							tn += getXmlElement(row, col);
						}
					}
				}
			}
			return new TwoClassStats(tp, fp, tn, fn);
		}
		
		/// <summary> Gets the number of correct classifications (that is, for which a
		/// correct prediction was made). (Actually the sum of the weights of
		/// these classifications)
		/// 
		/// </summary>
		/// <returns> the number of correct classifications 
		/// </returns>
		public virtual double correct()
		{
			
			double correct = 0;
			for (int i = 0; i < size(); i++)
			{
				correct += getXmlElement(i, i);
			}
			return correct;
		}
		
		/// <summary> Gets the number of incorrect classifications (that is, for which an
		/// incorrect prediction was made). (Actually the sum of the weights of
		/// these classifications)
		/// 
		/// </summary>
		/// <returns> the number of incorrect classifications 
		/// </returns>
		public virtual double incorrect()
		{
			
			double incorrect = 0;
			for (int row = 0; row < size(); row++)
			{
				for (int col = 0; col < size(); col++)
				{
					if (row != col)
					{
						incorrect += getXmlElement(row, col);
					}
				}
			}
			return incorrect;
		}
		
		/// <summary> Gets the number of predictions that were made
		/// (actually the sum of the weights of predictions where the
		/// class value was known).
		/// 
		/// </summary>
		/// <returns> the number of predictions with known class
		/// </returns>
		public virtual double total()
		{
			
			double total = 0;
			for (int row = 0; row < size(); row++)
			{
				for (int col = 0; col < size(); col++)
				{
					total += getXmlElement(row, col);
				}
			}
			return total;
		}
		
		/// <summary> Returns the estimated error rate.
		/// 
		/// </summary>
		/// <returns> the estimated error rate (between 0 and 1).
		/// </returns>
		public virtual double errorRate()
		{
			
			return incorrect() / total();
		}
		
		/// <summary> Calls toString() with a default title.
		/// 
		/// </summary>
		/// <returns> the confusion matrix as a string
		/// </returns>
		public virtual System.String toString()
		{
			
			return toString("=== Confusion Matrix ===\n");
		}
		
		/// <summary> Outputs the performance statistics as a classification confusion
		/// matrix. For each class value, shows the distribution of 
		/// predicted class values.
		/// 
		/// </summary>
		/// <param name="title">the title for the confusion matrix
		/// </param>
		/// <returns> the confusion matrix as a String
		/// </returns>
		public virtual System.String toString(System.String title)
		{
			
			System.Text.StringBuilder text = new System.Text.StringBuilder();
			char[] IDChars = new char[]{'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'};
			int IDWidth;
			bool fractional = false;
			
			// Find the maximum value in the matrix
			// and check for fractional display requirement 
			double maxval = 0;
			for (int i = 0; i < size(); i++)
			{
				for (int j = 0; j < size(); j++)
				{
					double current = getXmlElement(i, j);
					if (current < 0)
					{
						current *= (- 10);
					}
					if (current > maxval)
					{
						maxval = current;
					}
					double fract = current - System.Math.Round((double) current);
					if (!fractional && ((System.Math.Log(fract) / System.Math.Log(10)) >= - 2))
					{
						fractional = true;
					}
				}
			}
			
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			IDWidth = 1 + System.Math.Max((int) (System.Math.Log(maxval) / System.Math.Log(10) + (fractional?3:0)), (int) (System.Math.Log(size()) / System.Math.Log(IDChars.Length)));
			text.Append(title).Append("\n");
			for (int i = 0; i < size(); i++)
			{
				if (fractional)
				{
					text.Append(" ").Append(num2ShortID(i, IDChars, IDWidth - 3)).Append("   ");
				}
				else
				{
					text.Append(" ").Append(num2ShortID(i, IDChars, IDWidth));
				}
			}
			text.Append("     actual class\n");
			for (int i = 0; i < size(); i++)
			{
				for (int j = 0; j < size(); j++)
				{
					text.Append(" ").Append(Utils.doubleToString(getXmlElement(i, j), IDWidth, (fractional?2:0)));
				}
				text.Append(" | ").Append(num2ShortID(i, IDChars, IDWidth)).Append(" = ").Append(m_ClassNames[i]).Append("\n");
			}
			return text.ToString();
		}
		
		/// <summary> Method for generating indices for the confusion matrix.
		/// 
		/// </summary>
		/// <param name="num">integer to format
		/// </param>
		/// <returns> the formatted integer as a string
		/// </returns>
		private static System.String num2ShortID(int num, char[] IDChars, int IDWidth)
		{
			
			char[] ID = new char[IDWidth];
			int i;
			
			for (i = IDWidth - 1; i >= 0; i--)
			{
				ID[i] = IDChars[num % IDChars.Length];
				num = num / IDChars.Length - 1;
				if (num < 0)
				{
					break;
				}
			}
			for (i--; i >= 0; i--)
			{
				ID[i] = ' ';
			}
			
			return new System.String(ID);
		}
	}
}