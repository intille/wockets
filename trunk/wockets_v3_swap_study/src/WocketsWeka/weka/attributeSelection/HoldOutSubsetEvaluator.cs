/*
*    This program is free software; you can redistribute it and/or modify
*    it under the terms of the GNU General Public License as published by
*    the Free Software Foundation; either version 2 of the License, or
*    (at your option) any later version.
*
*    This program is distributed in the hope that it will be useful,
*    but WITHOUT ANY WARRANTY; without even the implied warranty of
*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
*    GNU General Public License for more details.
*
*    You should have received a copy of the GNU General Public License
*    along with this program; if not, write to the Free Software
*    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

/*
*    HoldOutSubsetEvaluator.java
*    Copyright (C) 2000 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Abstract attribute subset evaluator capable of evaluating subsets with
	/// respect to a data set that is distinct from that used to initialize/
	/// train the subset evaluator.
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.3 $
	/// </version>
	[Serializable]
	public abstract class HoldOutSubsetEvaluator:SubsetEvaluator
	{
		
		/// <summary> Evaluates a subset of attributes with respect to a set of instances.</summary>
		/// <param name="subset">a bitset representing the attribute subset to be
		/// evaluated
		/// </param>
		/// <param name="holdOut">a set of instances (possibly seperate and distinct
		/// from those use to build/train the evaluator) with which to
		/// evaluate the merit of the subset
		/// </param>
		/// <returns> the "merit" of the subset on the holdOut data
		/// </returns>
		/// <exception cref="Exception">if the subset cannot be evaluated
		/// </exception>
		public abstract double evaluateSubset(System.Collections.BitArray subset, Instances holdOut);
		
		/// <summary> Evaluates a subset of attributes with respect to a single instance.</summary>
		/// <param name="subset">a bitset representing the attribute subset to be
		/// evaluated
		/// </param>
		/// <param name="holdOut">a single instance (possibly not one of those used to
		/// build/train the evaluator) with which to evaluate the merit of the subset
		/// </param>
		/// <param name="retrain">true if the classifier should be retrained with respect
		/// to the new subset before testing on the holdOut instance.
		/// </param>
		/// <returns> the "merit" of the subset on the holdOut instance
		/// </returns>
		/// <exception cref="Exception">if the subset cannot be evaluated
		/// </exception>
		public abstract double evaluateSubset(System.Collections.BitArray subset, Instance holdOut, bool retrain);
	}
}