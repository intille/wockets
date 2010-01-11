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
*    AttributeTransformer.java
*    Copyright (C) 2000 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The package 'weka.core' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using weka.core;
namespace weka.attributeSelection
{
	
	/// <summary> Abstract attribute transformer. Transforms the dataset.
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.6 $
	/// </version>
	public interface AttributeTransformer
	{
		// ===============
		// Public methods.
		// ===============
		
		/// <summary> Returns just the header for the transformed data (ie. an empty
		/// set of instances. This is so that AttributeSelection can
		/// determine the structure of the transformed data without actually
		/// having to get all the transformed data through getTransformedData().
		/// </summary>
		/// <returns> the header of the transformed data.
		/// </returns>
		/// <exception cref="Exception">if the header of the transformed data can't
		/// be determined.
		/// </exception>
		Instances transformedHeader();
		
		/// <summary> Returns the transformed data</summary>
		/// <returns> A set of instances representing the transformed data
		/// </returns>
		/// <exception cref="Exception">if the attribute could not be evaluated
		/// </exception>
		Instances transformedData();
		
		/// <summary> Transforms an instance in the format of the original data to the
		/// transformed space
		/// </summary>
		/// <returns> a transformed instance
		/// </returns>
		/// <exception cref="Exception">if the instance could not be transformed
		/// </exception>
		Instance convertInstance(Instance instance);
	}
}