/*
*    ContingencyTables.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class implementing some statistical routines for contingency tables.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	public class ContingencyTables
	{
		
		/// <summary>The natural logarithm of 2 </summary>
		private static double log2 = System.Math.Log(2);
		
		/// <summary> Returns chi-squared probability for a given matrix.
		/// 
		/// </summary>
		/// <param name="matrix">the contigency table
		/// </param>
		/// <param name="yates">is Yates' correction to be used?
		/// </param>
		/// <returns> the chi-squared probability
		/// </returns>
		
		public static double chiSquared(double[][] matrix, bool yates)
		{
			
			int df = (matrix.Length - 1) * (matrix[0].Length - 1);
			
			return Statistics.chiSquaredProbability(chiVal(matrix, yates), df);
		}
		
		/// <summary> Computes chi-squared statistic for a contingency table.
		/// 
		/// </summary>
		/// <param name="matrix">the contigency table
		/// </param>
		/// <param name="yates">is Yates' correction to be used?
		/// </param>
		/// <returns> the value of the chi-squared statistic
		/// </returns>
		public static double chiVal(double[][] matrix, bool useYates)
		{
			
			int df, nrows, ncols, row, col;
			double[] rtotal, ctotal;
			double expect = 0, chival = 0, n = 0;
			bool yates = true;
			
			nrows = matrix.Length;
			ncols = matrix[0].Length;
			rtotal = new double[nrows];
			ctotal = new double[ncols];
			for (row = 0; row < nrows; row++)
			{
				for (col = 0; col < ncols; col++)
				{
					rtotal[row] += matrix[row][col];
					ctotal[col] += matrix[row][col];
					n += matrix[row][col];
				}
			}
			df = (nrows - 1) * (ncols - 1);
			if ((df > 1) || (!useYates))
			{
				yates = false;
			}
			else if (df <= 0)
			{
				return 0;
			}
			chival = 0.0;
			for (row = 0; row < nrows; row++)
			{
				if (Utils.gr(rtotal[row], 0))
				{
					for (col = 0; col < ncols; col++)
					{
						if (Utils.gr(ctotal[col], 0))
						{
							expect = (ctotal[col] * rtotal[row]) / n;
							chival += chiCell(matrix[row][col], expect, yates);
						}
					}
				}
			}
			return chival;
		}
		
		/// <summary> Tests if Cochran's criterion is fullfilled for the given
		/// contingency table. Rows and columns with all zeros are not considered
		/// relevant.
		/// 
		/// </summary>
		/// <param name="matrix">the contigency table to be tested
		/// </param>
		/// <returns> true if contingency table is ok, false if not
		/// </returns>
		public static bool cochransCriterion(double[][] matrix)
		{
			
			double[] rtotal, ctotal;
			double n = 0, expect, smallfreq = 5;
			int smallcount = 0, nonZeroRows = 0, nonZeroColumns = 0, nrows, ncols, row, col;
			
			nrows = matrix.Length;
			ncols = matrix[0].Length;
			
			rtotal = new double[nrows];
			ctotal = new double[ncols];
			for (row = 0; row < nrows; row++)
			{
				for (col = 0; col < ncols; col++)
				{
					rtotal[row] += matrix[row][col];
					ctotal[col] += matrix[row][col];
					n += matrix[row][col];
				}
			}
			for (row = 0; row < nrows; row++)
			{
				if (Utils.gr(rtotal[row], 0))
				{
					nonZeroRows++;
				}
			}
			for (col = 0; col < ncols; col++)
			{
				if (Utils.gr(ctotal[col], 0))
				{
					nonZeroColumns++;
				}
			}
			for (row = 0; row < nrows; row++)
			{
				if (Utils.gr(rtotal[row], 0))
				{
					for (col = 0; col < ncols; col++)
					{
						if (Utils.gr(ctotal[col], 0))
						{
							expect = (ctotal[col] * rtotal[row]) / n;
							if (Utils.sm(expect, smallfreq))
							{
								if (Utils.sm(expect, 1))
								{
									return false;
								}
								else
								{
									smallcount++;
									if (smallcount > (nonZeroRows * nonZeroColumns) / smallfreq)
									{
										return false;
									}
								}
							}
						}
					}
				}
			}
			return true;
		}
		
		/// <summary> Computes Cramer's V for a contingency table.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> Cramer's V
		/// </returns>
		public static double CramersV(double[][] matrix)
		{
			
			int row, col, nrows, ncols, min;
			double n = 0;
			
			nrows = matrix.Length;
			ncols = matrix[0].Length;
			for (row = 0; row < nrows; row++)
			{
				for (col = 0; col < ncols; col++)
				{
					n += matrix[row][col];
				}
			}
			min = nrows < ncols?nrows - 1:ncols - 1;
			if ((min == 0) || Utils.eq(n, 0))
				return 0;
			return System.Math.Sqrt(chiVal(matrix, false) / (n * (double) min));
		}
		
		/// <summary> Computes the entropy of the given array.
		/// 
		/// </summary>
		/// <param name="array">the array
		/// </param>
		/// <returns> the entropy
		/// </returns>
		public static double entropy(double[] array)
		{
			
			double returnValue = 0, sum = 0;
			
			for (int i = 0; i < array.Length; i++)
			{
				returnValue -= lnFunc(array[i]);
				sum += array[i];
			}
			if (Utils.eq(sum, 0))
			{
				return 0;
			}
			else
			{
				return (returnValue + lnFunc(sum)) / (sum * log2);
			}
		}
		
		/// <summary> Computes conditional entropy of the rows given
		/// the columns.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the conditional entropy of the rows given the columns
		/// </returns>
		public static double entropyConditionedOnColumns(double[][] matrix)
		{
			
			double returnValue = 0, sumForColumn, total = 0;
			
			for (int j = 0; j < matrix[0].Length; j++)
			{
				sumForColumn = 0;
				for (int i = 0; i < matrix.Length; i++)
				{
					returnValue = returnValue + lnFunc(matrix[i][j]);
					sumForColumn += matrix[i][j];
				}
				returnValue = returnValue - lnFunc(sumForColumn);
				total += sumForColumn;
			}
			if (Utils.eq(total, 0))
			{
				return 0;
			}
			return (- returnValue) / (total * log2);
		}
		
		/// <summary> Computes conditional entropy of the columns given
		/// the rows.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the conditional entropy of the columns given the rows
		/// </returns>
		public static double entropyConditionedOnRows(double[][] matrix)
		{
			
			double returnValue = 0, sumForRow, total = 0;
			
			for (int i = 0; i < matrix.Length; i++)
			{
				sumForRow = 0;
				for (int j = 0; j < matrix[0].Length; j++)
				{
					returnValue = returnValue + lnFunc(matrix[i][j]);
					sumForRow += matrix[i][j];
				}
				returnValue = returnValue - lnFunc(sumForRow);
				total += sumForRow;
			}
			if (Utils.eq(total, 0))
			{
				return 0;
			}
			return (- returnValue) / (total * log2);
		}
		
		/// <summary> Computes conditional entropy of the columns given the rows
		/// of the test matrix with respect to the train matrix. Uses a
		/// Laplace prior. Does NOT normalize the entropy.
		/// 
		/// </summary>
		/// <param name="train">the train matrix 
		/// </param>
		/// <param name="test">the test matrix
		/// </param>
		/// <param name="the">number of symbols for Laplace
		/// </param>
		/// <returns> the entropy
		/// </returns>
		public static double entropyConditionedOnRows(double[][] train, double[][] test, double numClasses)
		{
			
			double returnValue = 0, trainSumForRow, testSumForRow, testSum = 0;
			
			for (int i = 0; i < test.Length; i++)
			{
				trainSumForRow = 0;
				testSumForRow = 0;
				for (int j = 0; j < test[0].Length; j++)
				{
					returnValue -= test[i][j] * System.Math.Log(train[i][j] + 1);
					trainSumForRow += train[i][j];
					testSumForRow += test[i][j];
				}
				testSum = testSumForRow;
				returnValue += testSumForRow * System.Math.Log(trainSumForRow + numClasses);
			}
			return returnValue / (testSum * log2);
		}
		
		/// <summary> Computes the rows' entropy for the given contingency table.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the rows' entropy
		/// </returns>
		public static double entropyOverRows(double[][] matrix)
		{
			
			double returnValue = 0, sumForRow, total = 0;
			
			for (int i = 0; i < matrix.Length; i++)
			{
				sumForRow = 0;
				for (int j = 0; j < matrix[0].Length; j++)
				{
					sumForRow += matrix[i][j];
				}
				returnValue = returnValue - lnFunc(sumForRow);
				total += sumForRow;
			}
			if (Utils.eq(total, 0))
			{
				return 0;
			}
			return (returnValue + lnFunc(total)) / (total * log2);
		}
		
		/// <summary> Computes the columns' entropy for the given contingency table.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the columns' entropy
		/// </returns>
		public static double entropyOverColumns(double[][] matrix)
		{
			
			double returnValue = 0, sumForColumn, total = 0;
			
			for (int j = 0; j < matrix[0].Length; j++)
			{
				sumForColumn = 0;
				for (int i = 0; i < matrix.Length; i++)
				{
					sumForColumn += matrix[i][j];
				}
				returnValue = returnValue - lnFunc(sumForColumn);
				total += sumForColumn;
			}
			if (Utils.eq(total, 0))
			{
				return 0;
			}
			return (returnValue + lnFunc(total)) / (total * log2);
		}
		
		/// <summary> Computes gain ratio for contingency table (split on rows).
		/// Returns Double.MAX_VALUE if the split entropy is 0.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the gain ratio
		/// </returns>
		public static double gainRatio(double[][] matrix)
		{
			
			double preSplit = 0, postSplit = 0, splitEnt = 0, sumForRow, sumForColumn, total = 0, infoGain;
			
			// Compute entropy before split
			for (int i = 0; i < matrix[0].Length; i++)
			{
				sumForColumn = 0;
				for (int j = 0; j < matrix.Length; j++)
					sumForColumn += matrix[j][i];
				preSplit += lnFunc(sumForColumn);
				total += sumForColumn;
			}
			preSplit -= lnFunc(total);
			
			// Compute entropy after split and split entropy
			for (int i = 0; i < matrix.Length; i++)
			{
				sumForRow = 0;
				for (int j = 0; j < matrix[0].Length; j++)
				{
					postSplit += lnFunc(matrix[i][j]);
					sumForRow += matrix[i][j];
				}
				splitEnt += lnFunc(sumForRow);
			}
			postSplit -= splitEnt;
			splitEnt -= lnFunc(total);
			
			infoGain = preSplit - postSplit;
			if (Utils.eq(splitEnt, 0))
				return 0;
			return infoGain / splitEnt;
		}
		
		/// <summary> Returns negative base 2 logarithm of multiple hypergeometric
		/// probability for a contingency table.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the log of the hypergeometric probability of the contingency table 
		/// </returns>
		public static double log2MultipleHypergeometric(double[][] matrix)
		{
			
			double sum = 0, sumForRow, sumForColumn, total = 0;
			
			for (int i = 0; i < matrix.Length; i++)
			{
				sumForRow = 0;
				for (int j = 0; j < matrix[i].Length; j++)
				{
					sumForRow += matrix[i][j];
				}
				sum += SpecialFunctions.lnFactorial(sumForRow);
				total += sumForRow;
			}
			for (int j = 0; j < matrix[0].Length; j++)
			{
				sumForColumn = 0;
				for (int i = 0; i < matrix.Length; i++)
				{
					sumForColumn += matrix[i][j];
				}
				sum += SpecialFunctions.lnFactorial(sumForColumn);
			}
			for (int i = 0; i < matrix.Length; i++)
			{
				for (int j = 0; j < matrix[i].Length; j++)
				{
					sum -= SpecialFunctions.lnFactorial(matrix[i][j]);
				}
			}
			sum -= SpecialFunctions.lnFactorial(total);
			return (- sum) / log2;
		}
		
		/// <summary> Reduces a matrix by deleting all zero rows and columns.
		/// 
		/// </summary>
		/// <param name="matrix">the matrix to be reduced
		/// </param>
		/// <param name="the">matrix with all zero rows and columns deleted
		/// </param>
		public static double[][] reduceMatrix(double[][] matrix)
		{
			
			int row, col, currCol, currRow, nrows, ncols, nonZeroRows = 0, nonZeroColumns = 0;
			double[] rtotal, ctotal;
			double[][] newMatrix;
			
			nrows = matrix.Length;
			ncols = matrix[0].Length;
			rtotal = new double[nrows];
			ctotal = new double[ncols];
			for (row = 0; row < nrows; row++)
			{
				for (col = 0; col < ncols; col++)
				{
					rtotal[row] += matrix[row][col];
					ctotal[col] += matrix[row][col];
				}
			}
			for (row = 0; row < nrows; row++)
			{
				if (Utils.gr(rtotal[row], 0))
				{
					nonZeroRows++;
				}
			}
			for (col = 0; col < ncols; col++)
			{
				if (Utils.gr(ctotal[col], 0))
				{
					nonZeroColumns++;
				}
			}
			newMatrix = new double[nonZeroRows][];
			for (int i = 0; i < nonZeroRows; i++)
			{
				newMatrix[i] = new double[nonZeroColumns];
			}
			currRow = 0;
			for (row = 0; row < nrows; row++)
			{
				if (Utils.gr(rtotal[row], 0))
				{
					currCol = 0;
					for (col = 0; col < ncols; col++)
					{
						if (Utils.gr(ctotal[col], 0))
						{
							newMatrix[currRow][currCol] = matrix[row][col];
							currCol++;
						}
					}
					currRow++;
				}
			}
			return newMatrix;
		}
		
		/// <summary> Calculates the symmetrical uncertainty for base 2.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <returns> the calculated symmetrical uncertainty
		/// 
		/// </returns>
		public static double symmetricalUncertainty(double[][] matrix)
		{
			
			double sumForColumn, sumForRow, total = 0, columnEntropy = 0, rowEntropy = 0, entropyConditionedOnRows = 0, infoGain = 0;
			
			// Compute entropy for columns
			for (int i = 0; i < matrix[0].Length; i++)
			{
				sumForColumn = 0;
				for (int j = 0; j < matrix.Length; j++)
				{
					sumForColumn += matrix[j][i];
				}
				columnEntropy += lnFunc(sumForColumn);
				total += sumForColumn;
			}
			columnEntropy -= lnFunc(total);
			
			// Compute entropy for rows and conditional entropy
			for (int i = 0; i < matrix.Length; i++)
			{
				sumForRow = 0;
				for (int j = 0; j < matrix[0].Length; j++)
				{
					sumForRow += matrix[i][j];
					entropyConditionedOnRows += lnFunc(matrix[i][j]);
				}
				rowEntropy += lnFunc(sumForRow);
			}
			entropyConditionedOnRows -= rowEntropy;
			rowEntropy -= lnFunc(total);
			infoGain = columnEntropy - entropyConditionedOnRows;
			if (Utils.eq(columnEntropy, 0) || Utils.eq(rowEntropy, 0))
				return 0;
			return 2.0 * (infoGain / (columnEntropy + rowEntropy));
		}
		
		/// <summary> Computes Goodman and Kruskal's tau-value for a contingency table.
		/// 
		/// </summary>
		/// <param name="matrix">the contingency table
		/// </param>
		/// <param name="Goodman">and Kruskal's tau-value
		/// </param>
		public static double tauVal(double[][] matrix)
		{
			
			int nrows, ncols, row, col;
			double[] ctotal;
			double maxcol = 0, max, maxtotal = 0, n = 0;
			
			nrows = matrix.Length;
			ncols = matrix[0].Length;
			ctotal = new double[ncols];
			for (row = 0; row < nrows; row++)
			{
				max = 0;
				for (col = 0; col < ncols; col++)
				{
					if (Utils.gr(matrix[row][col], max))
						max = matrix[row][col];
					ctotal[col] += matrix[row][col];
					n += matrix[row][col];
				}
				maxtotal += max;
			}
			if (Utils.eq(n, 0))
			{
				return 0;
			}
			maxcol = ctotal[Utils.maxIndex(ctotal)];
			return (maxtotal - maxcol) / (n - maxcol);
		}
		
		/// <summary> Help method for computing entropy.</summary>
		private static double lnFunc(double num)
		{
			
			// Constant hard coded for efficiency reasons
			if (num < 1e-6)
			{
				return 0;
			}
			else
			{
				return num * System.Math.Log(num);
			}
		}
		
		/// <summary> Computes chi-value for one cell in a contingency table.
		/// 
		/// </summary>
		/// <param name="freq">the observed frequency in the cell
		/// </param>
		/// <param name="expected">the expected frequency in the cell
		/// </param>
		/// <returns> the chi-value for that cell; 0 if the expected value is
		/// too close to zero 
		/// </returns>
		private static double chiCell(double freq, double expected, bool yates)
		{
			
			// Cell in empty row and column?
			if (Utils.smOrEq(expected, 0))
			{
				return 0;
			}
			
			// Compute difference between observed and expected value
			double diff = System.Math.Abs(freq - expected);
			if (yates)
			{
				
				// Apply Yates' correction if wanted
				diff -= 0.5;
				
				// The difference should never be negative
				if (diff < 0)
				{
					diff = 0;
				}
			}
			
			// Return chi-value for the cell
			return (diff * diff / expected);
		}
		
		/// <summary> Main method for testing this class.</summary>
		//	public static void main(String[] ops) 
		//	{
		//		double[] firstRow = {10, 5, 20};
		//		double[] secondRow = {2, 10, 6};
		//		double[] thirdRow = {5, 10, 10};
		//		double[][] matrix = new double[3][0];
		//
		//		matrix[0] = firstRow; matrix[1] = secondRow; matrix[2] = thirdRow;
		//		for (int i = 0; i < matrix.length; i++) 
		//		{
		//			for (int j = 0; j < matrix[i].length; j++) 
		//			{
		//				System.out.print(matrix[i][j] + " ");
		//			}
		//			System.out.println();
		//		}
		//		System.out.println("Chi-squared probability: " +
		//			ContingencyTables.chiSquared(matrix, false));
		//		System.out.println("Chi-squared value: " +
		//			ContingencyTables.chiVal(matrix, false));
		//		System.out.println("Cochran's criterion fullfilled: " +
		//			ContingencyTables.cochransCriterion(matrix));
		//		System.out.println("Cramer's V: " +
		//			ContingencyTables.CramersV(matrix));
		//		System.out.println("Entropy of first row: " +
		//			ContingencyTables.entropy(firstRow));
		//		System.out.println("Entropy conditioned on columns: " +
		//			ContingencyTables.entropyConditionedOnColumns(matrix));
		//		System.out.println("Entropy conditioned on rows: " +
		//			ContingencyTables.entropyConditionedOnRows(matrix));
		//		System.out.println("Entropy conditioned on rows (with Laplace): " +
		//			ContingencyTables.entropyConditionedOnRows(matrix, matrix, 3));
		//		System.out.println("Entropy of rows: " +
		//			ContingencyTables.entropyOverRows(matrix));
		//		System.out.println("Entropy of columns: " +
		//			ContingencyTables.entropyOverColumns(matrix));
		//		System.out.println("Gain ratio: " +
		//			ContingencyTables.gainRatio(matrix));
		//		System.out.println("Negative log2 of multiple hypergeometric probability: " +
		//			ContingencyTables.log2MultipleHypergeometric(matrix));
		//		System.out.println("Symmetrical uncertainty: " +
		//			ContingencyTables.symmetricalUncertainty(matrix));
		//		System.out.println("Tau value: " +
		//			ContingencyTables.tauVal(matrix));
		//		double[][] newMatrix = new double[3][3];
		//		newMatrix[0][0] = 1; newMatrix[0][1] = 0; newMatrix[0][2] = 1;
		//		newMatrix[1][0] = 0; newMatrix[1][1] = 0; newMatrix[1][2] = 0;
		//		newMatrix[2][0] = 1; newMatrix[2][1] = 0; newMatrix[2][2] = 1;
		//		System.out.println("Matrix with empty row and column: ");
		//		for (int i = 0; i < newMatrix.length; i++) 
		//		{
		//			for (int j = 0; j < newMatrix[i].length; j++) 
		//			{
		//				System.out.print(newMatrix[i][j] + " ");
		//			}
		//			System.out.println();
		//		}
		//		System.out.println("Reduced matrix: ");
		//		newMatrix = ContingencyTables.reduceMatrix(newMatrix);
		//		for (int i = 0; i < newMatrix.length; i++) 
		//		{
		//			for (int j = 0; j < newMatrix[i].length; j++) 
		//			{
		//				System.out.print(newMatrix[i][j] + " ");
		//			}
		//			System.out.println();
		//		}
		//	}
	}
}