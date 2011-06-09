/*
*    NNConditionalEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.estimators
{
	
	/// <summary> Conditional probability estimator for a numeric domain conditional upon
	/// a numeric domain (using Mahalanobis distance).
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.4 $
	/// </version>
	public class NNConditionalEstimator : ConditionalEstimator
	{
		
		/// <summary>Vector containing all of the values seen </summary>
		private System.Collections.ArrayList m_Values = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(10));
		
		/// <summary>Vector containing all of the conditioning values seen </summary>
		private System.Collections.ArrayList m_CondValues = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(10));
		
		/// <summary>Vector containing the associated weights </summary>
		private System.Collections.ArrayList m_Weights = System.Collections.ArrayList.Synchronized(new System.Collections.ArrayList(10));
		
		/// <summary>The sum of the weights so far </summary>
		private double m_SumOfWeights;
		
		/// <summary>Current Conditional mean </summary>
		private double m_CondMean;
		
		/// <summary>Current Values mean </summary>
		private double m_ValueMean;
		
		/// <summary>Current covariance matrix </summary>
		private Matrix m_Covariance;
		
		/// <summary>Whether we can optimise the kernel summation </summary>
		private bool m_AllWeightsOne = true;
		
		/// <summary>2 * PI </summary>
		private static double TWO_PI = 2 * System.Math.PI;
		
		// ===============
		// Private methods
		// ===============
		
		/// <summary> Execute a binary search to locate the nearest data value
		/// 
		/// </summary>
		/// <param name="key">the data value to locate
		/// </param>
		/// <param name="secondaryKey">the data value to locate
		/// </param>
		/// <returns> the index of the nearest data value
		/// </returns>
		private int findNearestPair(double key, double secondaryKey)
		{
			
			int low = 0;
			int high = m_CondValues.Count;
			int middle = 0;
			while (low < high)
			{
				middle = (low + high) / 2;
				double current = ((System.Double) m_CondValues[middle]);
				if (current == key)
				{
					double secondary = ((System.Double) m_Values[middle]);
					if (secondary == secondaryKey)
					{
						return middle;
					}
					if (secondary > secondaryKey)
					{
						high = middle;
					}
					else if (secondary < secondaryKey)
					{
						low = middle + 1;
					}
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
		
		/// <summary>Calculate covariance and value means </summary>
		private void  calculateCovariance()
		{
			
			double sumValues = 0, sumConds = 0;
			for (int i = 0; i < m_Values.Count; i++)
			{
				sumValues += ((System.Double) m_Values[i]) * ((System.Double) m_Weights[i]);
				sumConds += ((System.Double) m_CondValues[i]) * ((System.Double) m_Weights[i]);
			}
			m_ValueMean = sumValues / m_SumOfWeights;
			m_CondMean = sumConds / m_SumOfWeights;
			double c00 = 0, c01 = 0, c10 = 0, c11 = 0;
			for (int i = 0; i < m_Values.Count; i++)
			{
				double x = ((System.Double) m_Values[i]);
				double y = ((System.Double) m_CondValues[i]);
				double weight = ((System.Double) m_Weights[i]);
				c00 += (x - m_ValueMean) * (x - m_ValueMean) * weight;
				c01 += (x - m_ValueMean) * (y - m_CondMean) * weight;
				c11 += (y - m_CondMean) * (y - m_CondMean) * weight;
			}
			c00 /= (m_SumOfWeights - 1.0);
			c01 /= (m_SumOfWeights - 1.0);
			c10 = c01;
			c11 /= (m_SumOfWeights - 1.0);
			m_Covariance = new Matrix(2, 2);
			m_Covariance.setXmlElement(0, 0, c00);
			m_Covariance.setXmlElement(0, 1, c01);
			m_Covariance.setXmlElement(1, 0, c10);
			m_Covariance.setXmlElement(1, 1, c11);
		}
		
		/// <summary> Returns value for normal kernel
		/// 
		/// </summary>
		/// <param name="x">the argument to the kernel function
		/// </param>
		/// <param name="variance">the variance
		/// </param>
		/// <returns> the value for a normal kernel
		/// </returns>
		private double normalKernel(double x, double variance)
		{
			
			return System.Math.Exp((- x) * x / (2 * variance)) / System.Math.Sqrt(variance * TWO_PI);
		}
		
		/// <summary> Add a new data value to the current estimator.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		public virtual void  addValue(double data, double given, double weight)
		{
			
			int insertIndex = findNearestPair(given, data);
			if ((m_Values.Count <= insertIndex) || (((System.Double) m_CondValues[insertIndex]) != given) || (((System.Double) m_Values[insertIndex]) != data))
			{
				m_CondValues.Insert(insertIndex, (double) given);
				m_Values.Insert(insertIndex, (double) data);
				m_Weights.Insert(insertIndex, (double) weight);
				if (weight != 1)
				{
					m_AllWeightsOne = false;
				}
			}
			else
			{
				double newWeight = ((System.Double) m_Weights[insertIndex]);
				newWeight += weight;
				m_Weights[insertIndex] = (double) newWeight;
				m_AllWeightsOne = false;
			}
			m_SumOfWeights += weight;
			// Invalidate any previously calculated covariance matrix
			m_Covariance = null;
		}
		
		/// <summary> Get a probability estimator for a value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <returns> the estimator for the supplied value given the condition
		/// </returns>
		public virtual Estimator getEstimator(double given)
		{
			
			if (m_Covariance == null)
			{
				calculateCovariance();
			}
			Estimator result = new MahalanobisEstimator(m_Covariance, given - m_CondMean, m_ValueMean);
			return result;
		}
		
		/// <summary> Get a probability estimate for a value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <param name="given">the new value that data is conditional upon 
		/// </param>
		/// <returns> the estimated probability of the supplied value
		/// </returns>
		public virtual double getProbability(double data, double given)
		{
			
			return getEstimator(given).getProbability(data);
		}
		
		/// <summary>Display a representation of this estimator </summary>
		public override System.String ToString()
		{
			
			if (m_Covariance == null)
			{
				calculateCovariance();
			}
			System.String result = "NN Conditional Estimator. " + m_CondValues.Count + " data points.  Mean = " + Utils.doubleToString(m_ValueMean, 4, 2) + "  Conditional mean = " + Utils.doubleToString(m_CondMean, 4, 2);
			result += ("  Covariance Matrix: \n" + m_Covariance);
			return result;
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
		//			int seed = 42;
		//			if (argv.length > 0) 
		//			{
		//				seed = Integer.parseInt(argv[0]);
		//			}
		//			NNConditionalEstimator newEst = new NNConditionalEstimator();
		//
		//			// Create 100 random points and add them
		//			Random r = new Random(seed);
		//      
		//			int numPoints = 50;
		//			if (argv.length > 2) 
		//			{
		//				numPoints = Integer.parseInt(argv[2]);
		//			}
		//			for(int i = 0; i < numPoints; i++) 
		//			{
		//				int x = Math.abs(r.nextInt() % 100);
		//				int y = Math.abs(r.nextInt() % 100);
		//				System.out.println("# " + x + "  " + y);
		//				newEst.addValue(x, y, 1);
		//			}
		//			//    System.out.println(newEst);
		//			int cond;
		//			if (argv.length > 1) 
		//			{
		//				cond = Integer.parseInt(argv[1]);
		//			}
		//			else cond = Math.abs(r.nextInt() % 100);
		//			System.out.println("## Conditional = " + cond);
		//			Estimator result = newEst.getEstimator(cond);
		//			for(int i = 0; i <= 100; i+= 5) 
		//			{
		//				System.out.println(" " + i + "  " + result.getProbability(i));
		//			}
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}