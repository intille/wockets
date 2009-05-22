/*
*    TwoClassStats.java
*    Copyright (C) 2002 University of Waikato
*
*/
using System;
namespace weka.classifiers.evaluation
{
	
	/// <summary> Encapsulates performance functions for two-class problems.
	/// 
	/// </summary>
	/// <author>  Len Trigg (len@reeltwo.com)
	/// </author>
	/// <version>  $Revision: 1.7 $
	/// </version>
	public class TwoClassStats
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary>Gets the number of positive instances predicted as positive </summary>
		/// <summary>Sets the number of positive instances predicted as positive </summary>
		virtual public double TruePositive
		{
			get
			{
				return m_TruePos;
			}
			
			set
			{
				m_TruePos = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary>Gets the number of negative instances predicted as positive </summary>
		/// <summary>Sets the number of negative instances predicted as positive </summary>
		virtual public double FalsePositive
		{
			get
			{
				return m_FalsePos;
			}
			
			set
			{
				m_FalsePos = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary>Gets the number of negative instances predicted as negative </summary>
		/// <summary>Sets the number of negative instances predicted as negative </summary>
		virtual public double TrueNegative
		{
			get
			{
				return m_TrueNeg;
			}
			
			set
			{
				m_TrueNeg = value;
			}
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary>Gets the number of positive instances predicted as negative </summary>
		/// <summary>Sets the number of positive instances predicted as negative </summary>
		virtual public double FalseNegative
		{
			get
			{
				return m_FalseNeg;
			}
			
			set
			{
				m_FalseNeg = value;
			}
			
		}
		/// <summary> Calculate the true positive rate. 
		/// This is defined as<p>
		/// <pre>
		/// correctly classified positives
		/// ------------------------------
		/// total positives
		/// </pre>
		/// 
		/// </summary>
		/// <returns> the true positive rate
		/// </returns>
		virtual public double TruePositiveRate
		{
			get
			{
				if (0 == (m_TruePos + m_FalseNeg))
				{
					return 0;
				}
				else
				{
					return m_TruePos / (m_TruePos + m_FalseNeg);
				}
			}
			
		}
		/// <summary> Calculate the false positive rate. 
		/// This is defined as<p>
		/// <pre>
		/// incorrectly classified negatives
		/// --------------------------------
		/// total negatives
		/// </pre>
		/// 
		/// </summary>
		/// <returns> the false positive rate
		/// </returns>
		virtual public double FalsePositiveRate
		{
			get
			{
				if (0 == (m_FalsePos + m_TrueNeg))
				{
					return 0;
				}
				else
				{
					return m_FalsePos / (m_FalsePos + m_TrueNeg);
				}
			}
			
		}
		/// <summary> Calculate the precision. 
		/// This is defined as<p>
		/// <pre>
		/// correctly classified positives
		/// ------------------------------
		/// total predicted as positive
		/// </pre>
		/// 
		/// </summary>
		/// <returns> the precision
		/// </returns>
		virtual public double Precision
		{
			get
			{
				if (0 == (m_TruePos + m_FalsePos))
				{
					return 0;
				}
				else
				{
					return m_TruePos / (m_TruePos + m_FalsePos);
				}
			}
			
		}
		/// <summary> Calculate the recall. 
		/// This is defined as<p>
		/// <pre>
		/// correctly classified positives
		/// ------------------------------
		/// total positives
		/// </pre><p>
		/// (Which is also the same as the truePositiveRate.)
		/// 
		/// </summary>
		/// <returns> the recall
		/// </returns>
		virtual public double Recall
		{
			get
			{
				return TruePositiveRate;
			}
			
		}
		/// <summary> Calculate the F-Measure. 
		/// This is defined as<p>
		/// <pre>
		/// 2 * recall * precision
		/// ----------------------
		/// recall + precision
		/// </pre>
		/// 
		/// </summary>
		/// <returns> the F-Measure
		/// </returns>
		virtual public double FMeasure
		{
			get
			{
				
				double precision = Precision;
				double recall = Recall;
				if ((precision + recall) == 0)
				{
					return 0;
				}
				return 2 * precision * recall / (precision + recall);
			}
			
		}
		/// <summary> Calculate the fallout. 
		/// This is defined as<p>
		/// <pre>
		/// incorrectly classified negatives
		/// --------------------------------
		/// total predicted as positive
		/// </pre>
		/// 
		/// </summary>
		/// <returns> the fallout
		/// </returns>
		virtual public double Fallout
		{
			get
			{
				if (0 == (m_TruePos + m_FalsePos))
				{
					return 0;
				}
				else
				{
					return m_FalsePos / (m_TruePos + m_FalsePos);
				}
			}
			
		}
		/// <summary> Generates a <code>ConfusionMatrix</code> representing the current
		/// two-class statistics, using class names "negative" and "positive".
		/// 
		/// </summary>
		/// <returns> a <code>ConfusionMatrix</code>.
		/// </returns>
		virtual public ConfusionMatrix ConfusionMatrix
		{
			get
			{
				
				ConfusionMatrix cm = new ConfusionMatrix(CATEGORY_NAMES);
				cm.setXmlElement(0, 0, m_TrueNeg);
				cm.setXmlElement(0, 1, m_FalsePos);
				cm.setXmlElement(1, 0, m_FalseNeg);
				cm.setXmlElement(1, 1, m_TruePos);
				return cm;
			}
			
		}
		
		/// <summary>The names used when converting this object to a confusion matrix </summary>
		//UPGRADE_NOTE: Final was removed from the declaration of 'CATEGORY_NAMES'. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1003'"
		private static readonly System.String[] CATEGORY_NAMES = new System.String[]{"negative", "positive"};
		
		/// <summary>Pos predicted as pos </summary>
		private double m_TruePos;
		
		/// <summary>Neg predicted as pos </summary>
		private double m_FalsePos;
		
		/// <summary>Neg predicted as neg </summary>
		private double m_TrueNeg;
		
		/// <summary>Pos predicted as neg </summary>
		private double m_FalseNeg;
		
		/// <summary> Creates the TwoClassStats with the given initial performance values.
		/// 
		/// </summary>
		/// <param name="tp">the number of correctly classified positives
		/// </param>
		/// <param name="fp">the number of incorrectly classified negatives
		/// </param>
		/// <param name="tn">the number of correctly classified negatives
		/// </param>
		/// <param name="fn">the number of incorrectly classified positives
		/// </param>
		public TwoClassStats(double tp, double fp, double tn, double fn)
		{
			
			TruePositive = tp;
			FalsePositive = fp;
			TrueNegative = tn;
			FalseNegative = fn;
		}
		
		/// <summary> Returns a string containing the various performance measures
		/// for the current object 
		/// </summary>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder res = new System.Text.StringBuilder();
			res.Append("TP:").Append(TruePositive.ToString("0.00")).Append('\n');
            res.Append("FN:").Append(FalseNegative.ToString("0.00")).Append('\n');
            res.Append("TN:").Append(TrueNegative.ToString("0.00")).Append('\n');
            res.Append("FP:").Append(FalsePositive.ToString("0.00")).Append('\n');
            res.Append("FP Rate:").Append(FalsePositiveRate.ToString("0.00")).Append('\n');
            res.Append("TP Rate:").Append(TruePositiveRate.ToString("0.00")).Append('\n');
            res.Append("Precision:").Append(Precision.ToString("0.00")).Append('\n');
            res.Append("Recall:").Append(Recall.ToString("0.00")).Append('\n');
            res.Append("FMeasure:").Append(FMeasure.ToString("0.00")).Append('\n');
            res.Append("Fallout:").Append(Fallout.ToString("0.00")).Append('\n');
			return res.ToString();
		}
	}
}