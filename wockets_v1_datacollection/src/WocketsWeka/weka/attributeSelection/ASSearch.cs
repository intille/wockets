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
*    ASSearch.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Abstract attribute selection search class.
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8 $
	/// </version>
	[Serializable]
	public abstract class ASSearch
	{
		
		// ===============
		// Public methods.
		// ===============
		
		/// <summary> Searches the attribute subset/ranking space.
		/// 
		/// </summary>
		/// <param name="ASEvaluator">the attribute evaluator to guide the search
		/// </param>
		/// <param name="data">the training instances.
		/// </param>
		/// <returns> an array (not necessarily ordered) of selected attribute indexes
		/// </returns>
		/// <exception cref="Exception">if the search can't be completed
		/// </exception>
		public abstract int[] search(ASEvaluation ASEvaluator, Instances data);
		
		/// <summary> Creates a new instance of a search class given it's class name and
		/// (optional) arguments to pass to it's setOptions method. If the
		/// search method implements OptionHandler and the options parameter is
		/// non-null, the search method will have it's options set.
		/// 
		/// </summary>
		/// <param name="searchName">the fully qualified class name of the search class
		/// </param>
		/// <param name="options">an array of options suitable for passing to setOptions. May
		/// be null.
		/// </param>
		/// <returns> the newly created search object, ready for use.
		/// </returns>
		/// <exception cref="Exception">if the search class name is invalid, or the options
		/// supplied are not acceptable to the search class.
		/// </exception>
		public static ASSearch forName(System.String searchName, System.String[] options)
		{
			return (ASSearch) Utils.forName(typeof(ASSearch), searchName, options);
		}
	}
}