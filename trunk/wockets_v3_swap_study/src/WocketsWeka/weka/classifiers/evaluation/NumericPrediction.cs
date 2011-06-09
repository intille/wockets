/*
*    NumericPrediction.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Encapsulates an evaluatable numeric prediction: the predicted class value
	/// plus the actual class value.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
    /// 
#if !PocketPC
	[Serializable]
#endif
	public class NumericPrediction : Prediction
	{
		
		/// <summary>The actual class value </summary>
		private double m_Actual = weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
		
		/// <summary>The predicted class value </summary>
		private double m_Predicted = weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
		
		/// <summary>The weight assigned to this prediction </summary>
		private double m_Weight = 1;
		
		/// <summary> Creates the NumericPrediction object with a default weight of 1.0.
		/// 
		/// </summary>
		/// <param name="actual">the actual value, or MISSING_VALUE.
		/// </param>
		/// <param name="predicted">the predicted value, or MISSING_VALUE.
		/// </param>
		public NumericPrediction(double actual, double predicted):this(actual, predicted, 1)
		{
		}
		
		/// <summary> Creates the NumericPrediction object.
		/// 
		/// </summary>
		/// <param name="actual">the actual value, or MISSING_VALUE.
		/// </param>
		/// <param name="predicted">the predicted value, or MISSING_VALUE.
		/// </param>
		/// <param name="weight">the weight assigned to the prediction.
		/// </param>
		public NumericPrediction(double actual, double predicted, double weight)
		{
			
			m_Actual = actual;
			m_Predicted = predicted;
			m_Weight = weight;
		}
		
		/// <summary> Gets the actual class value.
		/// 
		/// </summary>
		/// <returns> the actual class value, or MISSING_VALUE if no
		/// prediction was made.  
		/// </returns>
		public virtual double actual()
		{
			
			return m_Actual;
		}
		
		/// <summary> Gets the predicted class value.
		/// 
		/// </summary>
		/// <returns> the predicted class value, or MISSING_VALUE if no
		/// prediction was made.  
		/// </returns>
		public virtual double predicted()
		{
			
			return m_Predicted;
		}
		
		/// <summary> Gets the weight assigned to this prediction. This is typically the weight
		/// of the test instance the prediction was made for.
		/// 
		/// </summary>
		/// <returns> the weight assigned to this prediction.
		/// </returns>
		public virtual double weight()
		{
			
			return m_Weight;
		}
		
		/// <summary> Calculates the prediction error. This is defined as the predicted
		/// value minus the actual value.
		/// 
		/// </summary>
		/// <returns> the error for this prediction, or
		/// MISSING_VALUE if either the actual or predicted value
		/// is missing.  
		/// </returns>
		public virtual double error()
		{
			
			if ((m_Actual == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE) || (m_Predicted == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE))
			{
				return weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
			}
			return m_Predicted - m_Actual;
		}
		
		/// <summary> Gets a human readable representation of this prediction.
		/// 
		/// </summary>
		/// <returns> a human readable representation of this prediction.
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder sb = new System.Text.StringBuilder();
			sb.Append("NUM: ").Append(actual()).Append(' ').Append(predicted());
			sb.Append(' ').Append(weight());
			return sb.ToString();
		}
	}
}