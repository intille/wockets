/*
*    ProtectedProperties.java
*    Copyright (C) 2001 Richard Kirkby
*
*/
using System;
#if !PocketPC
using System.Runtime.Serialization.Formatters.Binary;
using System.Runtime.Serialization;
#endif
namespace weka.core
{
	
	/// <summary> Simple class that extends the Properties class so that the properties are
	/// unable to be modified.
	/// 
	/// </summary>
	/// <author>  Richard Kirkby (rkirkby@cs.waikato.ac.nz)
	/// </author>
	/// <version>  $Revision: 1.2 $
	/// </version>
	//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
#if PocketPC
    public class ProtectedProperties : System.Collections.Specialized.NameValueCollection
#else
    [Serializable()]   
	public class ProtectedProperties:System.Collections.Specialized.NameValueCollection,ISerializable
#endif
	{
		
		// the properties need to be open during construction of the object
		private bool closed = false;
		
		/// <summary> Creates a set of protected properties from a set of normal ones.
		/// 
		/// </summary>
		/// <param name="props">the properties to be stored and protected.
		/// </param>
		//UPGRADE_ISSUE: Class hierarchy differences between 'java.util.Properties' and 'System.Collections.Specialized.NameValueCollection' may cause compilation errors. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1186'"
		public ProtectedProperties(System.Collections.Specialized.NameValueCollection props)
		{
			
			System.Collections.IEnumerator propEnum = props.Keys.GetEnumerator();
			//UPGRADE_TODO: Method 'java.util.Enumeration.hasMoreElements' was converted to 'System.Collections.IEnumerator.MoveNext' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationhasMoreElements'"
			while (propEnum.MoveNext())
			{
				//UPGRADE_TODO: Method 'java.util.Enumeration.nextElement' was converted to 'System.Collections.IEnumerator.Current' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilEnumerationnextElement'"
				System.String propName = (System.String) propEnum.Current;
				System.String propValue = props.Get(propName);
				//UPGRADE_TODO: Method 'java.util.Properties.setProperty' was converted to 'System.Collections.Specialized.NameValueCollection.Item' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilPropertiessetProperty_javalangString_javalangString'"
				base[propName] = propValue;
			}
			closed = true; // no modifications allowed from now on
		}
		
		/// <summary> Overrides a method to prevent the properties from being modified.
		/// 
		/// </summary>
		/// <returns> never returns without throwing an exception.
		/// </returns>
		/// <exception cref="UnsupportedOperationException">always.
		/// </exception>
		//UPGRADE_NOTE: The equivalent of method 'java.util.Properties.setProperty' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
		public System.Object setProperty(System.String key, System.String value_Renamed)
		{
			
			if (closed)
				throw new System.NotSupportedException("ProtectedProperties cannot be modified!");
			else
			{
				System.Object tempObject;
				//UPGRADE_TODO: Method 'java.util.Properties.setProperty' was converted to 'System.Collections.Specialized.NameValueCollection.Item' which has a different behavior. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1073_javautilPropertiessetProperty_javalangString_javalangString'"
				tempObject = base[key];
				base[key] = value_Renamed;
				return tempObject;
			}
		}
		
		/// <summary> Overrides a method to prevent the properties from being modified.
		/// 
		/// </summary>
		/// <returns> never returns without throwing an exception.
		/// </returns>
		/// <exception cref="UnsupportedOperationException">always.
		/// </exception>
		//UPGRADE_NOTE: The equivalent of method 'java.util.Properties.load' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
		public void  load(System.IO.Stream inStream)
		{
			
			throw new System.NotSupportedException("ProtectedProperties cannot be modified!");
		}
		
		/// <summary> Overrides a method to prevent the properties from being modified.
		/// 
		/// </summary>
		/// <returns> never returns without throwing an exception.
		/// </returns>
		/// <exception cref="UnsupportedOperationException">always.
		/// </exception>
		public override void  Clear()
		{
			
			throw new System.NotSupportedException("ProtectedProperties cannot be modified!");
		}
		
		/// <summary> Overrides a method to prevent the properties from being modified.
		/// 
		/// </summary>
		/// <returns> never returns without throwing an exception.
		/// </returns>
		/// <exception cref="UnsupportedOperationException">always.
		/// </exception>
		//UPGRADE_NOTE: The equivalent of method 'java.util.Hashtable.put' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
		public System.Object put(System.Object key, System.Object value_Renamed)
		{
			
			if (closed)
				throw new System.NotSupportedException("ProtectedProperties cannot be modified!");
			else
			{
				System.Object tempObject;
				tempObject = base[(System.String) key];
				base[(System.String) key] = (System.String) value_Renamed;
				return tempObject;
			}
		}
		
		/// <summary> Overrides a method to prevent the properties from being modified.
		/// 
		/// </summary>
		/// <returns> never returns without throwing an exception.
		/// </returns>
		/// <exception cref="UnsupportedOperationException">always.
		/// </exception>
		//UPGRADE_NOTE: The equivalent of method 'java.util.Hashtable.putAll' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
		public void  putAll(System.Collections.IDictionary t)
		{
			
			throw new System.NotSupportedException("ProtectedProperties cannot be modified!");
		}
		
		/// <summary> Overrides a method to prevent the properties from being modified.
		/// 
		/// </summary>
		/// <returns> never returns without throwing an exception.
		/// </returns>
		/// <exception cref="UnsupportedOperationException">always.
		/// </exception>
		//UPGRADE_NOTE: The equivalent of method 'java.util.Hashtable.remove' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
		public System.Object remove(System.Object key)
		{
			
			throw new System.NotSupportedException("ProtectedProperties cannot be modified!");
		}

#if !PocketPC
        //public ProtectedProperties someObject;
           //Deserialization constructor.
        public ProtectedProperties(SerializationInfo info, StreamingContext context)
        {
          closed = (bool)info.GetValue("closed", typeof(bool));
          //Allows MyClass2 to deserialize itself
          //someObject = new ProtectedProperties(info, context);
       }

        //Serialization function.
        public override void GetObjectData(SerializationInfo info, StreamingContext context)
        {
            info.AddValue("closed", closed);
            //Allows MyClass2 to serialize itself
           // someObject.GetObjectData(info, context);
        }

#endif


	}
}