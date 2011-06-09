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
*    SubsetEvaluator.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Abstract attribute subset evaluator.
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.7 $
	/// </version>
	[Serializable]
	public abstract class SubsetEvaluator:ASEvaluation
	{
		
		// ===============
		// Public methods.
		// ===============
		
		/// <summary> evaluates a subset of attributes
		/// 
		/// </summary>
		/// <param name="subset">a bitset representing the attribute subset to be 
		/// evaluated 
		/// </param>
		/// <returns> the "merit" of the subset
		/// </returns>
		/// <exception cref="Exception">if the subset could not be evaluated
		/// </exception>
		public abstract double evaluateSubset(System.Collections.BitArray subset);
	}
}