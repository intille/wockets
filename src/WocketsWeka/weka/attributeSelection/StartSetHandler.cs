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
*    StartSetHandler.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Interface for search methods capable of doing something sensible
	/// given a starting set of attributes.
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
	public interface StartSetHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Returns a list of attributes (and or attribute ranges) as a String</summary>
		/// <returns> a list of attributes (and or attribute ranges)
		/// </returns>
		/// <summary> Sets a starting set of attributes for the search. It is the
		/// search method's responsibility to report this start set (if any)
		/// in its toString() method.
		/// </summary>
		/// <param name="startSet">a string containing a list of attributes (and or ranges),
		/// eg. 1,2,6,10-15.
		/// </param>
		/// <exception cref="Exception">if start set can't be set.
		/// </exception>
		System.String StartSet
		{
			get;
			
			set;
			
		}
	}
}