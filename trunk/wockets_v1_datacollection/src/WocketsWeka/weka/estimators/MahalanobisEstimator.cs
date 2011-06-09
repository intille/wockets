/*
*    MahalanobisEstimator.java
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
	/// <version>  $Revision: 1.4 $
	/// </version>
#if !PocketPC
    [Serializable]
#endif
	public class MahalanobisEstimator : Estimator
	{
		
		/// <summary>The inverse of the covariance matrix </summary>
		private Matrix m_CovarianceInverse;
		
		/// <summary>The determinant of the covariance matrix </summary>
		private double m_Determinant;
		
		/// <summary> The difference between the conditioning value and the conditioning mean</summary>
		private double m_ConstDelta;
		
		/// <summary>The mean of the values </summary>
		private double m_ValueMean;
		
		/// <summary>2 * PI </summary>
		private static double TWO_PI = 2 * System.Math.PI;
		
		/// <summary> Returns value for normal kernel
		/// 
		/// </summary>
		/// <param name="x">the argument to the kernel function
		/// </param>
		/// <param name="variance">the variance
		/// </param>
		/// <returns> the value for a normal kernel
		/// </returns>
		private double normalKernel(double x)
		{
			
			Matrix thisPoint = new Matrix(1, 2);
			thisPoint.setXmlElement(0, 0, x);
			thisPoint.setXmlElement(0, 1, m_ConstDelta);
			return Math.Exp((- thisPoint.multiply(m_CovarianceInverse).multiply(thisPoint.transpose()).getXmlElement(0, 0)) / 2) / (System.Math.Sqrt(TWO_PI) * m_Determinant);
		}
		
		/// <summary> Constructor
		/// 
		/// </summary>
		/// <param name="the">number of possible symbols
		/// </param>
		public MahalanobisEstimator(Matrix covariance, double constDelta, double valueMean)
		{
			
			m_CovarianceInverse = null;
			if ((covariance.numRows() == 2) && (covariance.numColumns() == 2))
			{
				double a = covariance.getXmlElement(0, 0);
				double b = covariance.getXmlElement(0, 1);
				double c = covariance.getXmlElement(1, 0);
				double d = covariance.getXmlElement(1, 1);
				if (a == 0)
				{
					a = c; c = 0;
					double temp = b;
					b = d; d = temp;
				}
				if (a == 0)
				{
					return ;
				}
				double denom = d - c * b / a;
				if (denom == 0)
				{
					return ;
				}
				m_Determinant = covariance.getXmlElement(0, 0) * covariance.getXmlElement(1, 1) - covariance.getXmlElement(1, 0) * covariance.getXmlElement(0, 1);
				m_CovarianceInverse = new Matrix(2, 2);
				m_CovarianceInverse.setXmlElement(0, 0, 1.0 / a + b * c / a / a / denom);
				m_CovarianceInverse.setXmlElement(0, 1, (- b) / a / denom);
				m_CovarianceInverse.setXmlElement(1, 0, (- c) / a / denom);
				m_CovarianceInverse.setXmlElement(1, 1, 1.0 / denom);
				m_ConstDelta = constDelta;
				m_ValueMean = valueMean;
			}
		}
		
		/// <summary> Add a new data value to the current estimator. Does nothing because the
		/// data is provided in the constructor.
		/// 
		/// </summary>
		/// <param name="data">the new data value 
		/// </param>
		/// <param name="weight">the weight assigned to the data value 
		/// </param>
		public virtual void  addValue(double data, double weight)
		{
			
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
			
			double delta = data - m_ValueMean;
			if (m_CovarianceInverse == null)
			{
				return 0;
			}
			return normalKernel(delta);
		}
		
		/// <summary>Display a representation of this estimator </summary>
		public override System.String ToString()
		{
			
			if (m_CovarianceInverse == null)
			{
				return "No covariance inverse\n";
			}
			return "Mahalanovis Distribution. Mean = " + Utils.doubleToString(m_ValueMean, 4, 2) + "  ConditionalOffset = " + Utils.doubleToString(m_ConstDelta, 4, 2) + "\n" + "Covariance Matrix: Determinant = " + m_Determinant + "  Inverse:\n" + m_CovarianceInverse;
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
		//			double delta = 0.5;
		//			double xmean = 0;
		//			double lower = 0;
		//			double upper = 10;
		//			Matrix covariance = new Matrix(2, 2);
		//			covariance.setXmlElement(0, 0, 2);
		//			covariance.setXmlElement(0, 1, -3);
		//			covariance.setXmlElement(1, 0, -4);
		//			covariance.setXmlElement(1, 1, 5);
		//			if (argv.length > 0) 
		//			{
		//				covariance.setXmlElement(0, 0, Double.valueOf(argv[0]).doubleValue());
		//			}
		//			if (argv.length > 1) 
		//			{
		//				covariance.setXmlElement(0, 1, Double.valueOf(argv[1]).doubleValue());
		//			}
		//			if (argv.length > 2) 
		//			{
		//				covariance.setXmlElement(1, 0, Double.valueOf(argv[2]).doubleValue());
		//			}
		//			if (argv.length > 3) 
		//			{
		//				covariance.setXmlElement(1, 1, Double.valueOf(argv[3]).doubleValue());
		//			}
		//			if (argv.length > 4) 
		//			{
		//				delta = Double.valueOf(argv[4]).doubleValue();
		//			}
		//			if (argv.length > 5) 
		//			{
		//				xmean = Double.valueOf(argv[5]).doubleValue();
		//			}
		//      
		//			MahalanobisEstimator newEst = new MahalanobisEstimator(covariance,
		//				delta, xmean);
		//			if (argv.length > 6) 
		//			{
		//				lower = Double.valueOf(argv[6]).doubleValue();
		//				if (argv.length > 7) 
		//				{
		//					upper = Double.valueOf(argv[7]).doubleValue();
		//				}
		//				double increment = (upper - lower) / 50;
		//				for(double current = lower; current <= upper; current+= increment)
		//					System.out.println(current + "  " + newEst.getProbability(current));
		//			} 
		//			else 
		//			{
		//				System.out.println("Covariance Matrix\n" + covariance);
		//				System.out.println(newEst);
		//			}
		//		} 
		//		catch (Exception e) 
		//		{
		//			System.out.println(e.getMessage());
		//		}
		//	}
	}
}