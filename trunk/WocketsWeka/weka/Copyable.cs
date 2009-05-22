/*
*    Copyable.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Interface implemented by classes that can produce "shallow" copies
	/// of their objects. (As opposed to clone(), which is supposed to
	/// produce a "deep" copy.)
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	public interface Copyable
	{
		/// <summary> This method produces a shallow copy of an object.
		/// It does the same as the clone() method in Object, which also produces
		/// a shallow copy.
		/// </summary>
		System.Object copy();
	}
}