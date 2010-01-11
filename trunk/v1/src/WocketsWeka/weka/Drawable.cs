/*
*    Drawable.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface to something that can be drawn as a graph.
	/// 
	/// </summary>
	/// <author>  Ashraf M. Kibriya(amk14@cs.waikato.ac.nz), Eibe Frank(eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.8 $
	/// </version>
	public struct Drawable_Fields{
		public readonly static int NOT_DRAWABLE = 0;
		public readonly static int TREE = 1;
		public readonly static int BayesNet = 2;
	}
	public interface Drawable
	{
		//UPGRADE_NOTE: Members of interface 'Drawable' were extracted into structure 'Drawable_Fields'. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1045'"
		
		/// <summary> Returns the type of graph representing
		/// the object.
		/// 
		/// </summary>
		/// <returns> the type of graph representing the object
		/// </returns>
		int graphType();
		
		/// <summary> Returns a string that describes a graph representing
		/// the object. The string should be in XMLBIF ver.
		/// 0.3 format if the graph is a BayesNet, otherwise
		/// it should be in dotty format.
		/// 
		/// </summary>
		/// <returns> the graph described by a string
		/// </returns>
		/// <exception cref="Exception">if the graph can't be computed
		/// </exception>
		System.String graph();
	}
}