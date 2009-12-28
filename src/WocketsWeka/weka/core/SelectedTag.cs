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
*    SelectedTag.java
*    Copyright (C) 1999 Len Trigg
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Represents a selected value from a finite set of values, where each
	/// value is a Tag (i.e. has some string associated with it). Primarily
	/// used in schemes to select between alternative behaviours,
	/// associating names with the alternative behaviours.
	/// 
	/// </summary>
	/// <author>  <a href="mailto:len@reeltwo.com">Len Trigg</a> 
	/// </author>
	/// <version>  $Revision: 1.6.2.1 $
	/// </version>
	public class SelectedTag
	{
		/// <summary> Gets the set of all valid Tags.
		/// 
		/// </summary>
		/// <returns> an array containing the valid Tags.
		/// </returns>
		virtual public Tag[] Tags
		{
			get
			{
				return m_Tags;
			}
			
		}
		
		/// <summary>The index of the selected tag </summary>
		protected internal int m_Selected;
		
		/// <summary>The set of tags to choose from </summary>
		protected internal Tag[] m_Tags;
		
		/// <summary> Creates a new <code>SelectedTag</code> instance.
		/// 
		/// </summary>
		/// <param name="tagID">the id of the selected tag.
		/// </param>
		/// <param name="tags">an array containing the possible valid Tags.
		/// </param>
		/// <exception cref="IllegalArgumentException">if the selected tag isn't in the array
		/// of valid values.
		/// </exception>
		public SelectedTag(int tagID, Tag[] tags)
		{
			for (int i = 0; i < tags.Length; i++)
			{
				if (tags[i].ID == tagID)
				{
					m_Selected = i;
					m_Tags = tags;
					return ;
				}
			}
			throw new System.ArgumentException("Selected tag is not valid");
		}
		
		/// <summary>Returns true if this SelectedTag equals another object </summary>
		public  override bool Equals(System.Object o)
		{
			if ((o == null) || !(o.GetType().Equals(this.GetType())))
			{
				return false;
			}
			SelectedTag s = (SelectedTag) o;
			if ((s.Tags == m_Tags) && (s.getSelectedTag() == m_Tags[m_Selected]))
			{
				return true;
			}
			else
			{
				return false;
			}
		}
		
		
		/// <summary> Gets the selected Tag.
		/// 
		/// </summary>
		/// <returns> the selected Tag.
		/// </returns>
		public virtual Tag getSelectedTag()
		{
			return m_Tags[m_Selected];
		}
		//UPGRADE_NOTE: The following method implementation was automatically added to preserve functionality. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1306'"
		public override int GetHashCode()
		{
			return base.GetHashCode();
		}
	}
}