/*
*    Option.java
*    Copyright (C) 1999 Eibe Frank
*
*/
using System;
namespace weka.core
{
	
	/// <summary> Class to store information about an option. <p>
	/// 
	/// Typical usage: <p>
	/// 
	/// <code>Option myOption = new Option("Uses extended mode.", "E", 0, "-E")); </code><p>
	/// 
	/// </summary>
	/// <author>  Eibe Frank (eibe@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.5 $
	/// </version>
	public class Option
	{
		
		/// <summary>What does this option do? </summary>
		private System.String m_Description;
		
		/// <summary>The synopsis. </summary>
		private System.String m_Synopsis;
		
		/// <summary>What's the option's name? </summary>
		private System.String m_Name;
		
		/// <summary>How many arguments does it take? </summary>
		private int m_NumArguments;
		
		/// <summary> Creates new option with the given parameters.
		/// 
		/// </summary>
		/// <param name="description">the option's description
		/// </param>
		/// <param name="name">the option's name
		/// </param>
		/// <param name="numArguments">the number of arguments
		/// </param>
		public Option(System.String description, System.String name, int numArguments, System.String synopsis)
		{
			
			m_Description = description;
			m_Name = name;
			m_NumArguments = numArguments;
			m_Synopsis = synopsis;
		}
		
		/// <summary> Returns the option's description.
		/// 
		/// </summary>
		/// <returns> the option's description
		/// </returns>
		public virtual System.String description()
		{
			
			return m_Description;
		}
		
		/// <summary> Returns the option's name.
		/// 
		/// </summary>
		/// <returns> the option's name
		/// </returns>
		public virtual System.String name()
		{
			
			return m_Name;
		}
		
		/// <summary> Returns the option's number of arguments.
		/// 
		/// </summary>
		/// <returns> the option's number of arguments
		/// </returns>
		public virtual int numArguments()
		{
			
			return m_NumArguments;
		}
		
		/// <summary> Returns the option's synopsis.
		/// 
		/// </summary>
		/// <returns> the option's synopsis
		/// </returns>
		public virtual System.String synopsis()
		{
			
			return m_Synopsis;
		}
	}
}