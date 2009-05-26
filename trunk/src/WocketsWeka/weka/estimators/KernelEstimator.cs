/*
*    KernelEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.estimators
{
	
	/// <summary> Simple kernel density estimator. Uses one gaussian kernel per observed
	/// data value.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class KernelEstimator : Estimator
	{
		/// <summary>Vector containing all of the values seen </summary>
		private double[] m_Values;
		
		/// <summary>Vector containing the associated weights </summary>
		private double[] m_Weights;
		
		/// <summary>Number of values stored in m_Weights and m_Values so far </summary>
		private int m_NumValues;
		
		/// <summary>The sum of the weights so far </summary>
		private double m_SumOfWeights;
		
		/// <summary>The standard deviation </summary>
		private double m_StandardDev;
		
		/// <summary>The precision of data values </summary>
		private double m_Precision;
		
		/// <summary>Whether we can optimise the kernel summation </summary>
		private bool m_AllWeightsOne;
		
		/// <summary>Maximum percentage error permitted in probability calculations </summary>
		private static double MAX_ERROR = 0.01;
		
		
		/// <summary> Execute a binary search to locate the nearest data value
		/// 
		/// </summary>
		/// <param name="the">data value to locate
		/// </param>
		/// <returns> the index of the nearest data value
		/// </returns>
		private int findNearestValue(double key)
		{
			
			int low = 0;
			int high = m_NumValues;
			int middle = 0;
			while (low < high)
			{
				middle = (low + high) / 2;
				double current = m_Values[middle];
				if (current == key)
				{
					return middle;
				}
				if (current > key)
				{
					high = middle;
				}
				else if (current < key)
				{
					low = middle + 1;
				}
			}
			return low;
		}
		
		/// <summary> Round a data value using the defined precision for this estimator
		/// 
		/// </summary>
		/// <param name="data">the value to round
		/// </param>
		/// <returns> the rounded data value
		/// </returns>
		private double round(double data)
		{
			
			return System.Math.Round((double) (data / m_Precision)) * m_Precision;
		}
		
		// ===============
		// Public methods.
		// ===============
		
		/// <summary> Constructor that takes a precision argument.
		/// 
		/// </summary>
		/// <param name="precision">the  precision to which numeric values are given. For
		/// example, if the precision is stated to be 0.1, the values in the
		/// interval (0.25,0.35] are all treated as 0.3. 
		/// </param>
		public KernelEstimator(double precision)
		{
			
			m_Values = new double[50];
			m_Weights = new double[50];
			m_NumValues = 0;
			m_SumOfWeights = 0;
			m_AllWeightsOne = true;
			m_Precision = precision;
			// precision cannot be zero
			if (m_Precision < Utils.SMALL)
				m_Precision = Utils.SMALL;
			//    m_StandardDev = 1e10 * m_Precision; // Set the standard deviation initially very wide
			m_StandardDev = m_Precision / (2 * 3);
		}
		
		/// <summary> Add a new data value to the current estimator.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		public virtual void  addValue(double data, double weight)
		{
			
			if (weight == 0)
			{
				return ;
			}
			data = round(data);
			int insertIndex = findNearestValue(data);
			if ((m_NumValues <= insertIndex) || (m_Values[insertIndex] != data))
			{
				if (m_NumValues < m_Values.Length)
				{
					int left = m_NumValues - insertIndex;
					Array.Copy(m_Values, insertIndex, m_Values, insertIndex + 1, left);
					Array.Copy(m_Weights, insertIndex, m_Weights, insertIndex + 1, left);
					
					m_Values[insertIndex] = data;
					m_Weights[insertIndex] = weight;
					m_NumValues++;
				}
				else
				{
					double[] newValues = new double[m_Values.Length * 2];
					double[] newWeights = new double[m_Values.Length * 2];
					int left = m_NumValues - insertIndex;
					Array.Copy(m_Values, 0, newValues, 0, insertIndex);
					Array.Copy(m_Weights, 0, newWeights, 0, insertIndex);
					newValues[insertIndex] = data;
					newWeights[insertIndex] = weight;
					Array.Copy(m_Values, insertIndex, newValues, insertIndex + 1, left);
					Array.Copy(m_Weights, insertIndex, newWeights, insertIndex + 1, left);
					m_NumValues++;
					m_Values = newValues;
					m_Weights = newWeights;
				}
				if (weight != 1)
				{
					m_AllWeightsOne = false;
				}
			}
			else
			{
				m_Weights[insertIndex] += weight;
				m_AllWeightsOne = false;
			}
			m_SumOfWeights += weight;
			double range = m_Values[m_NumValues - 1] - m_Values[0];
			if (range > 0)
			{
				m_StandardDev = System.Math.Max(range / System.Math.Sqrt(m_SumOfWeights), m_Precision / (2 * 3));
			}
		}
		
		/// <summary> Get a probability estimate for a value.
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <returns> the estimated probability of the supplied value
		/// </returns>
		public virtual double getProbability(double data)
		{
			
			double delta = 0, sum = 0, currentProb = 0;
			double zLower = 0, zUpper = 0;
			if (m_NumValues == 0)
			{
				zLower = (data - (m_Precision / 2)) / m_StandardDev;
				zUpper = (data + (m_Precision / 2)) / m_StandardDev;
				return (Statistics.normalProbability(zUpper) - Statistics.normalProbability(zLower));
			}
			double weightSum = 0;
			int start = findNearestValue(data);
			for (int i = start; i < m_NumValues; i++)
			{
				delta = m_Values[i] - data;
				zLower = (delta - (m_Precision / 2)) / m_StandardDev;
				zUpper = (delta + (m_Precision / 2)) / m_StandardDev;
				currentProb = (Statistics.normalProbability(zUpper) - Statistics.normalProbability(zLower));
				sum += currentProb * m_Weights[i];
				/*
				System.out.print("zL" + (i + 1) + ": " + zLower + " ");
				System.out.print("zU" + (i + 1) + ": " + zUpper + " ");
				System.out.print("P" + (i + 1) + ": " + currentProb + " ");
				System.out.println("total: " + (currentProb * m_Weights[i]) + " ");
				*/
				weightSum += m_Weights[i];
				if (currentProb * (m_SumOfWeights - weightSum) < sum * MAX_ERROR)
				{
					break;
				}
			}
			for (int i = start - 1; i >= 0; i--)
			{
				delta = m_Values[i] - data;
				zLower = (delta - (m_Precision / 2)) / m_StandardDev;
				zUpper = (delta + (m_Precision / 2)) / m_StandardDev;
				currentProb = (Statistics.normalProbability(zUpper) - Statistics.normalProbability(zLower));
				sum += currentProb * m_Weights[i];
				weightSum += m_Weights[i];
				if (currentProb * (m_SumOfWeights - weightSum) < sum * MAX_ERROR)
				{
					break;
				}
			}
			return sum / m_SumOfWeights;
		}
		
		/// <summary>Display a representation of this estimator </summary>
		public override System.String ToString()
		{
			
			System.String result = m_NumValues + " Normal Kernels. \nStandardDev = " + Utils.doubleToString(m_StandardDev, 6, 4) + " Precision = " + m_Precision;
			if (m_NumValues == 0)
			{
				result += "  \nMean = 0";
			}
			else
			{
				result += "  \nMeans =";
				for (int i = 0; i < m_NumValues; i++)
				{
					result += (" " + m_Values[i]);
				}
				if (!m_AllWeightsOne)
				{
					result += "\nWeights = ";
					for (int i = 0; i < m_NumValues; i++)
					{
						result += (" " + m_Weights[i]);
					}
				}
			}
			return result + "\n";
		}
		
		/// <summary> Main method for testing this class.
		/// 
		/// </summary>
		/// <param name="argv">should contain a sequence of numeric values
		/// </param>
		//	public static void main(String [] argv) 
		//	{
		//
		//		try 
		//		{
		//			if (argv.length < 2) 
		//			{
		//				System.out.println("Please specify a set of instances.");
		//				return;
		//			}
		//			KernelEstimator newEst = new KernelEstimator(0.01);
		//			for (int i = 0; i < argv.length - 3; i += 2) 
		//			{
		//				newEst.addValue(Double.valueOf(argv[i]).doubleValue(), 
		//					Double.valueOf(argv[i + 1]).doubleValue());
		//			}
		//			System.out.println(newEst);
		//
		//			double start = Double.valueOf(argv[argv.length - 2]).doubleValue();
		//			double finish = Double.valueOf(argv[argv.length - 1]).doubleValue();
		//			for (double current = start; current < finish; 
		//				current += (finish - start) / 50) 
		//			{
		//				System.out.println("Data: " + current + " " 
		//					+ newEst.getProbability(current));
		//			}
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}