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
*    RankedOutputSearch.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	
	/// <summary> Interface for search methods capable of producing a
	/// ranked list of attributes.
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.9 $
	/// </version>
	public interface RankedOutputSearch
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the threshold by which attributes can be discarded. Discarding
		/// of attributes is done by the AttributeSelection module using the
		/// threshold returned by this method.
		/// </summary>
		/// <returns> a threshold by which to discard attributes
		/// </returns>
		/// <summary> Sets a threshold by which attributes can be discarded from the
		/// ranking. This threshold is used by the AttributeSelection module
		/// which does the actual discarding of attributes---the implementer
		/// of this method needs only to provide a variable in which to store the
		/// supplied threshold. -Double.MAX_VALUE is reserved to mean no threshold,
		/// ie, retain all attributes.
		/// </summary>
		/// <param name="threshold">the threshold.
		/// </param>
		double Threshold
		{
			get;
			
			set;
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the user specified number of attributes to be retained.</summary>
		/// <returns> the number of attributes to retain
		/// </returns>
		/// <summary> Specify the number of attributes to select from the ranked list. < 0
		/// indicates that all attributes are to be retained. NumToSelect has
		/// precedence over threshold, ie. if there is a non -1 value for NumToSelect
		/// then this will take precedence over any threshold value.
		/// </summary>
		/// <param name="numToSelect">the number of attributes to retain
		/// </param>
		int NumToSelect
		{
			get;
			
			set;
			
		}
		/// <summary> Gets the calculated number of attributes to retain. This is the
		/// actual number of attributes to retain. This is the same as
		/// getNumToSelect if the user specifies a number which is not less
		/// than zero. Otherwise it should be the number of attributes in the
		/// (potentially transformed) data.
		/// </summary>
		int CalculatedNumToSelect
		{
			get;
			
		}
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets whether the user has opted to see a ranked list of
		/// attributes rather than the normal result of the search
		/// </summary>
		/// <returns> true if a ranked list has been requested.
		/// </returns>
		/// <summary> Sets whether or not ranking is to be performed.
		/// When a search method is capable of producing a ranked list
		/// of attributes, the user has the choice of seeing the results of a
		/// normal search or seeing a ranked list.
		/// </summary>
		/// <param name="doRanking">true if ranked list is to be produced
		/// </param>
		bool GenerateRanking
		{
			get;
			
			set;
			
		}
		
		
		// ===============
		// Public methods.
		// ===============
		
		/// <summary> Returns a X by 2 list of attribute indexes and corresponding
		/// evaluations from best (highest) to worst.
		/// </summary>
		/// <returns> the ranked list of attribute indexes in an array of ints
		/// </returns>
		/// <exception cref="Exception">if the ranking can't be produced
		/// </exception>
		double[][] rankedAttributes();
	}
}