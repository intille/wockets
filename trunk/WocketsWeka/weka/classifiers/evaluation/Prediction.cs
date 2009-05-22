/*
*    Prediction.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Encapsulates a single evaluatable prediction: the predicted value plus the 
	/// actual class value.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
	public struct Prediction_Fields{
		/// <summary> Constant representing a missing value. This should have the same value
		/// as weka.core.Instance.MISSING_VALUE 
		/// </summary>
		public readonly static double MISSING_VALUE;
		static Prediction_Fields()
		{
			MISSING_VALUE = weka.core.Instance.missingValue();
		}
	}
	public interface Prediction
	{
		//UPGRADE_NOTE: Members of interface 'Prediction' were extracted into structure 'Prediction_Fields'. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1045'"
		
		/// <summary> Gets the weight assigned to this prediction. This is typically the weight
		/// of the test instance the prediction was made for.
		/// 
		/// </summary>
		/// <returns> the weight assigned to this prediction.
		/// </returns>
		double weight();
		
		/// <summary> Gets the actual class value.
		/// 
		/// </summary>
		/// <returns> the actual class value, or MISSING_VALUE if no
		/// prediction was made.  
		/// </returns>
		double actual();
		
		/// <summary> Gets the predicted class value.
		/// 
		/// </summary>
		/// <returns> the predicted class value, or MISSING_VALUE if no
		/// prediction was made.  
		/// </returns>
		double predicted();
	}
}