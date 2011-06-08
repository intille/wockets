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
*    Tag.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> A <code>Tag</code> simply associates a numeric ID with a String description.
	/// 
	/// </summary>
	/// <author>  <a href="mailto:len@reeltwo.com">Len Trigg</a>
	/// </author>
	/// <version>  $Revision: 1.5.2.1 $
	/// </version>
	public class Tag
	{
		/// <summary> Gets the numeric ID of the Tag.
		/// 
		/// </summary>
		/// <returns> the ID of the Tag.
		/// </returns>
		virtual public int ID
		{
			get
			{
				return m_ID;
			}
			
		}
		/// <summary> Gets the string description of the Tag.
		/// 
		/// </summary>
		/// <returns> the description of the Tag.
		/// </returns>
		virtual public System.String Readable
		{
			get
			{
				return m_Readable;
			}
			
		}
		
		/// <summary>The ID </summary>
		protected internal int m_ID;
		
		/// <summary>The descriptive text </summary>
		protected internal System.String m_Readable;
		
		/// <summary> Creates a new <code>Tag</code> instance.
		/// 
		/// </summary>
		/// <param name="ident">the ID for the new Tag.
		/// </param>
		/// <param name="readable">the description for the new Tag.
		/// </param>
		public Tag(int ident, System.String readable)
		{
			m_ID = ident;
			m_Readable = readable;
		}
	}
}