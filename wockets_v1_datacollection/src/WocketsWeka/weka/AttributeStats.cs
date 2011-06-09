/*
*    AttributeStats.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> A Utility class that contains summary information on an
	/// the values that appear in a dataset for a particular attribute.
	/// 
	/// </summary>
	/// <author>  <a href="mailto:len@reeltwo.com">Len Trigg</a>
	/// </author>
	/// <version>  $Revision: 1.7 $
	/// </version>

	public class AttributeStats
	{
		
		/// <summary>The number of int-like values </summary>
		public int intCount = 0;
		
		/// <summary>The number of real-like values (i.e. have a fractional part) </summary>
		public int realCount = 0;
		
		/// <summary>The number of missing values </summary>
		public int missingCount = 0;
		
		/// <summary>The number of distinct values </summary>
		public int distinctCount = 0;
		
		/// <summary>The number of values that only appear once </summary>
		public int uniqueCount = 0;
		
		/// <summary>The total number of values (i.e. number of instances) </summary>
		public int totalCount = 0;
		
		/// <summary>Stats on numeric value distributions </summary>
		// perhaps Stats should be moved from weka.experiment to weka.core
		//public weka.experiment.Stats numericStats;
		
		/// <summary>Counts of each nominal value </summary>
		public int[] nominalCounts;
		
		/// <summary> Updates the counters for one more observed distinct value.
		/// 
		/// </summary>
		/// <param name="value">the value that has just been seen
		/// </param>
		/// <param name="count">the number of times the value appeared
		/// </param>
		protected internal virtual void  addDistinct(double value_Renamed, int count)
		{
			
			if (count > 0)
			{
				if (count == 1)
				{
					uniqueCount++;
				}
				//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
				if (Utils.eq(value_Renamed, (double) ((int) value_Renamed)))
				{
					intCount += count;
				}
				else
				{
					realCount += count;
				}
				if (nominalCounts != null)
				{
					//UPGRADE_WARNING: Data types in Visual C# might be different.  Verify the accuracy of narrowing conversions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1042'"
					nominalCounts[(int) value_Renamed] = count;
				}
				//if (numericStats != null)
				//{
				//	numericStats.add(value_Renamed, count);
				//	numericStats.calculateDerived();
				//}
			}
			distinctCount++;
		}
		
		/// <summary> Returns a human readable representation of this AttributeStats instance.
		/// 
		/// </summary>
		/// <returns> a String represtinging these AttributeStats.
		/// </returns>
		public override System.String ToString()
		{
			
			System.Text.StringBuilder sb = new System.Text.StringBuilder();
			sb.Append(Utils.padLeft("Type", 4)).Append(Utils.padLeft("Nom", 5));
			sb.Append(Utils.padLeft("Int", 5)).Append(Utils.padLeft("Real", 5));
			sb.Append(Utils.padLeft("Missing", 12));
			sb.Append(Utils.padLeft("Unique", 12));
			sb.Append(Utils.padLeft("Dist", 6));
			if (nominalCounts != null)
			{
				sb.Append(' ');
				for (int i = 0; i < nominalCounts.Length; i++)
				{
					sb.Append(Utils.padLeft("C[" + i + "]", 5));
				}
			}
			sb.Append('\n');
			
			long percent;
			//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
			percent = (long) System.Math.Round(100.0 * intCount / totalCount);
			if (nominalCounts != null)
			{
				sb.Append(Utils.padLeft("Nom", 4)).Append(' ');
				sb.Append(Utils.padLeft("" + percent, 3)).Append("% ");
				sb.Append(Utils.padLeft("" + 0, 3)).Append("% ");
			}
			else
			{
				sb.Append(Utils.padLeft("Num", 4)).Append(' ');
				sb.Append(Utils.padLeft("" + 0, 3)).Append("% ");
				sb.Append(Utils.padLeft("" + percent, 3)).Append("% ");
			}
			//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
			percent = (long) System.Math.Round(100.0 * realCount / totalCount);
			sb.Append(Utils.padLeft("" + percent, 3)).Append("% ");
			sb.Append(Utils.padLeft("" + missingCount, 5)).Append(" /");
			//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
			percent = (long) System.Math.Round(100.0 * missingCount / totalCount);
			sb.Append(Utils.padLeft("" + percent, 3)).Append("% ");
			sb.Append(Utils.padLeft("" + uniqueCount, 5)).Append(" /");
			//UPGRADE_TODO: Method 'java.lang.Math.round' was converted to 'System.Math.Round' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javalangMathround_double'"
			percent = (long) System.Math.Round(100.0 * uniqueCount / totalCount);
			sb.Append(Utils.padLeft("" + percent, 3)).Append("% ");
			sb.Append(Utils.padLeft("" + distinctCount, 5)).Append(' ');
			if (nominalCounts != null)
			{
				for (int i = 0; i < nominalCounts.Length; i++)
				{
					sb.Append(Utils.padLeft("" + nominalCounts[i], 5));
				}
			}
			sb.Append('\n');
			return sb.ToString();
		}
	}
}