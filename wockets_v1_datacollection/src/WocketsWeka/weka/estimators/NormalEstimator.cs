/*
*    NormalEstimator.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
using weka.core;
namespace weka.estimators
{
	
	/// <summary> Simple probability estimator that places a single normal distribution
	/// over the observed values.
	/// 
	/// </summary>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class NormalEstimator : Estimator
	{
		
		/// <summary>The sum of the weights </summary>
		private double m_SumOfWeights;
		
		/// <summary>The sum of the values seen </summary>
		private double m_SumOfValues;
		
		/// <summary>The sum of the values squared </summary>
		private double m_SumOfValuesSq;
		
		/// <summary>The current mean </summary>
		private double m_Mean;
		
		/// <summary>The current standard deviation </summary>
		private double m_StandardDev;
		
		/// <summary>The precision of numeric values ( = minimum std dev permitted) </summary>
		private double m_Precision;
		
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
		/// <param name="precision">the precision to which numeric values are given. For
		/// example, if the precision is stated to be 0.1, the values in the
		/// interval (0.25,0.35] are all treated as 0.3. 
		/// </param>
		public NormalEstimator(double precision)
		{
			
			m_Precision = precision;
			
			// Allow at most 3 sd's within one interval
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
			m_SumOfWeights += weight;
			m_SumOfValues += data * weight;
			m_SumOfValuesSq += data * data * weight;
			
			if (m_SumOfWeights > 0)
			{
				m_Mean = m_SumOfValues / m_SumOfWeights;
				double stdDev = System.Math.Sqrt(System.Math.Abs(m_SumOfValuesSq - m_Mean * m_SumOfValues) / m_SumOfWeights);
				// If the stdDev ~= 0, we really have no idea of scale yet, 
				// so stick with the default. Otherwise...
				if (stdDev > 1e-10)
				{
					m_StandardDev = System.Math.Max(m_Precision / (2 * 3), stdDev);
				}
			}
		}
		
		/// <summary> Get a probability estimate for a value
		/// 
		/// </summary>
		/// <param name="data">the value to estimate the probability of
		/// </param>
		/// <returns> the estimated probability of the supplied value
		/// </returns>
		public virtual double getProbability(double data)
		{
			
			data = round(data);
			double zLower = (data - m_Mean - (m_Precision / 2)) / m_StandardDev;
			double zUpper = (data - m_Mean + (m_Precision / 2)) / m_StandardDev;
			
			double pLower = Statistics.normalProbability(zLower);
			double pUpper = Statistics.normalProbability(zUpper);
			return pUpper - pLower;
		}
		
		/// <summary> Display a representation of this estimator</summary>
		public override System.String ToString()
		{
			
			return "Normal Distribution. Mean = " + Utils.doubleToString(m_Mean, 4) + " StandardDev = " + Utils.doubleToString(m_StandardDev, 4) + " WeightSum = " + Utils.doubleToString(m_SumOfWeights, 4) + " Precision = " + m_Precision + "\n";
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
		//
		//			if (argv.length == 0) 
		//			{
		//				System.out.println("Please specify a set of instances.");
		//				return;
		//			}
		//			NormalEstimator newEst = new NormalEstimator(0.01);
		//			for(int i = 0; i < argv.length; i++) 
		//			{
		//				double current = Double.valueOf(argv[i]).doubleValue();
		//				System.out.println(newEst);
		//				System.out.println("Prediction for " + current 
		//					+ " = " + newEst.getProbability(current));
		//				newEst.addValue(current, 1);
		//			}
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}