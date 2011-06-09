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
*    OptionHandler.java
*    Copyright (C) 1999 Eibe Frank,Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface to something that understands options.
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <author>  Len Trigg (trigg@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.7 $
	/// </version>
	public interface OptionHandler
	{
		//UPGRADE_NOTE: Respective javadoc comments were merged.  It should be changed in order to comply with .NET documentation conventions. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1199'"
		/// <summary> Gets the current option settings for the OptionHandler.
		/// 
		/// </summary>
		/// <returns> the list of current option settings as an array of strings
		/// </returns>
		/// <summary> Sets the OptionHandler's options using the given list. All options
		/// will be set (or reset) during this call (i.e. incremental setting
		/// of options is not possible).
		/// 
		/// </summary>
		/// <param name="options">the list of options as an array of strings
		/// </param>
		/// <exception cref="Exception">if an option is not supported
		/// </exception>
		System.String[] Options
		{
			/*@pure@*/
			//@ ensures \result != null;
			//@ ensures \nonnullelements(\result);
			
			get;
			
			//@ requires options != null;
			//@ requires \nonnullelements(options);
			
			set;
			
		}
		
		/// <summary> Returns an enumeration of all the available options..
		/// 
		/// </summary>
		/// <returns> an enumeration of all available options.
		/// </returns>
		System.Collections.IEnumerator listOptions();
	}
}