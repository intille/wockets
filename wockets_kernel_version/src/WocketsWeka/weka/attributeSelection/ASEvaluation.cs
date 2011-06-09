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
*    ASEvaluation.java
*    Copyright (C) 1999 Mark Hall
*
*/
using System;
//UPGRADE_TODO: The type 'weka.core.Instance' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Instance = weka.core.Instance;
//UPGRADE_TODO: The type 'weka.core.Instances' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Instances = weka.core.Instances;
//UPGRADE_TODO: The type 'weka.core.SerializedObject' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
//using SerializedObject = weka.core.SerializedObject;
//UPGRADE_TODO: The type 'weka.core.Utils' could not be found. If it was not included in the conversion, there may be compiler issues. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1262'"
using Utils = weka.core.Utils;
namespace weka.attributeSelection 
{
	
	/// <summary> Abstract attribute selection evaluation class
	/// 
	/// </summary>
	/// <author>  Mark Hall (mhall@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.9 $
	/// </version>
	
	[Serializable]
	public abstract class ASEvaluation
	{
		
		// ===============
		// Public methods.
		// ===============
		
		/// <summary> Generates a attribute evaluator. Has to initialize all fields of the 
		/// evaluator that are not being set via options.
		/// 
		/// </summary>
		/// <param name="data">set of instances serving as training data 
		/// </param>
		/// <exception cref="Exception">if the evaluator has not been 
		/// generated successfully
		/// </exception>
		public abstract void  buildEvaluator(Instances data);
		
		/// <summary> Provides a chance for a attribute evaluator to do any special
		/// post processing of the selected attribute set.
		/// 
		/// </summary>
		/// <param name="attributeSet">the set of attributes found by the search
		/// </param>
		/// <returns> a possibly ranked list of postprocessed attributes
		/// </returns>
		/// <exception cref="Exception">if postprocessing fails for some reason
		/// </exception>
		public virtual int[] postProcess(int[] attributeSet)
		{
			return attributeSet;
		}
		
		/// <summary> Creates a new instance of an attribute/subset evaluator 
		/// given it's class name and
		/// (optional) arguments to pass to it's setOptions method. If the
		/// evaluator implements OptionHandler and the options parameter is
		/// non-null, the evaluator will have it's options set.
		/// 
		/// </summary>
		/// <param name="evaluatorName">the fully qualified class name of the evaluator
		/// </param>
		/// <param name="options">an array of options suitable for passing to setOptions. May
		/// be null.
		/// </param>
		/// <returns> the newly created evaluator, ready for use.
		/// </returns>
		/// <exception cref="Exception">if the evaluator name is invalid, or the options
		/// supplied are not acceptable to the evaluator
		/// </exception>
		public static ASEvaluation forName(System.String evaluatorName, System.String[] options)
		{
			return (ASEvaluation) Utils.forName(typeof(ASEvaluation), evaluatorName, options);
		}
		
		/// <summary> Creates copies of the current evaluator. Note that this method
		/// now uses Serialization to perform a deep copy, so the evaluator
		/// object must be fully Serializable. Any currently built model will
		/// now be copied as well.
		/// 
		/// </summary>
		/// <param name="model">an example evaluator to copy
		/// </param>
		/// <param name="num">the number of evaluator copies to create.
		/// </param>
		/// <returns> an array of evaluators.
		/// </returns>
		/// <exception cref="Exception">if an error occurs 
		/// </exception>
	/*	public static ASEvaluation[] makeCopies(ASEvaluation model, int num)
		{
			
			if (model == null)
			{
				throw new System.Exception("No model evaluator set");
			}
			ASEvaluation[] evaluators = new ASEvaluation[num];
			SerializedObject so = new SerializedObject(model);
			for (int i = 0; i < evaluators.Length; i++)
			{
				evaluators[i] = (ASEvaluation) so.getObject();
			}
			return evaluators;
		}*/
	}
}