/*
*    NominalPrediction.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Encapsulates an evaluatable nominal prediction: the predicted probability
	/// distribution plus the actual class value.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.9 $
	/// </version>
    /// 
#if !PocketPC
	[Serializable]
#endif
	public class NominalPrediction : Prediction
	{
		
		/// <summary> Remove this if you change this class so that serialization would be
		/// affected.
		/// </summary>
		internal const long serialVersionUID = - 8871333992740492788L;
		
		/// <summary>The predicted probabilities </summary>
		private double[] m_Distribution;
		
		/// <summary>The actual class value </summary>
		private double m_Actual = weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
		
		/// <summary>The predicted class value </summary>
		private double m_Predicted = weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
		
		/// <summary>The weight assigned to this prediction </summary>
		private double m_Weight = 1;
		
		/// <summary> Creates the NominalPrediction object with a default weight of 1.0.
		/// 
		/// </summary>
		/// <param name="actual">the actual value, or MISSING_VALUE.
		/// </param>
		/// <param name="distribution">the predicted probability distribution. Use 
		/// NominalPrediction.makeDistribution() if you only know the predicted value.
		/// </param>
		public NominalPrediction(double actual, double[] distribution):this(actual, distribution, 1)
		{
		}
		
		/// <summary> Creates the NominalPrediction object.
		/// 
		/// </summary>
		/// <param name="actual">the actual value, or MISSING_VALUE.
		/// </param>
		/// <param name="distribution">the predicted probability distribution. Use 
		/// NominalPrediction.makeDistribution() if you only know the predicted value.
		/// </param>
		/// <param name="weight">the weight assigned to the prediction.
		/// </param>
		public NominalPrediction(double actual, double[] distribution, double weight)
		{
			
			if (distribution == null)
			{
				throw new System.NullReferenceException("Null distribution in NominalPrediction.");
			}
			m_Actual = actual;
			m_Distribution = distribution;
			m_Weight = weight;
			updatePredicted();
		}
		
		/// <summary>Gets the predicted probabilities </summary>
		public virtual double[] distribution()
		{
			
			return m_Distribution;
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
		
		/// <summary> Calculates the prediction margin. This is defined as the difference
		/// between the probability predicted for the actual class and the highest
		/// predicted probability of the other classes.
		/// 
		/// </summary>
		/// <returns> the margin for this prediction, or
		/// MISSING_VALUE if either the actual or predicted value
		/// is missing.  
		/// </returns>
		public virtual double margin()
		{
			
			if ((m_Actual == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE) || (m_Predicted == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE))
			{
				return weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			double probActual = m_Distribution[(int) m_Actual];
			double probNext = 0;
			for (int i = 0; i < m_Distribution.Length; i++)
				if ((i != m_Actual) && (m_Distribution[i] > probNext))
					probNext = m_Distribution[i];
			
			return probActual - probNext;
		}
		
		/// <summary> Convert a single prediction into a probability distribution
		/// with all zero probabilities except the predicted value which
		/// has probability 1.0. If no prediction was made, all probabilities
		/// are zero.
		/// 
		/// </summary>
		/// <param name="predictedClass">the index of the predicted class, or 
		/// MISSING_VALUE if no prediction was made.
		/// </param>
		/// <param name="numClasses">the number of possible classes for this nominal
		/// prediction.
		/// </param>
		/// <returns> the probability distribution.  
		/// </returns>
		public static double[] makeDistribution(double predictedClass, int numClasses)
		{
			
			double[] dist = new double[numClasses];
			if (predictedClass == weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE)
			{
				return dist;
			}
			//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
			dist[(int) predictedClass] = 1.0;
			return dist;
		}
		
		/// <summary> Creates a uniform probability distribution -- where each of the
		/// possible classes is assigned equal probability.
		/// 
		/// </summary>
		/// <param name="numClasses">the number of possible classes for this nominal
		/// prediction.
		/// </param>
		/// <returns> the probability distribution.  
		/// </returns>
		public static double[] makeUniformDistribution(int numClasses)
		{
			
			double[] dist = new double[numClasses];
			for (int i = 0; i < numClasses; i++)
			{
				dist[i] = 1.0 / numClasses;
			}
			return dist;
		}
		
		/// <summary> Determines the predicted class (doesn't detect multiple 
		/// classifications). If no prediction was made (i.e. all zero
		/// probababilities in the distribution), m_Prediction is set to
		/// MISSING_VALUE.
		/// </summary>
		private void  updatePredicted()
		{
			
			int predictedClass = - 1;
			double bestProb = 0.0;
			for (int i = 0; i < m_Distribution.Length; i++)
			{
				if (m_Distribution[i] > bestProb)
				{
					predictedClass = i;
					bestProb = m_Distribution[i];
				}
			}
			
			if (predictedClass != - 1)
			{
				m_Predicted = predictedClass;
			}
			else
			{
				m_Predicted = weka.classifiers.evaluation.Prediction_Fields.MISSING_VALUE;
			}
		}
		
		/// <summary> Gets a human readable representation of this prediction.
		/// 
		/// </summary>
		/// <returns> a human readable representation of this prediction.
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder sb = new System.Text.StringBuilder();
			sb.Append("NOM: ").Append(actual()).Append(" ").Append(predicted());
			sb.Append(' ').Append(weight());
			double[] dist = distribution();
			for (int i = 0; i < dist.Length; i++)
			{
				sb.Append(' ').Append(dist[i]);
			}
			return sb.ToString();
		}
	}
}