using System;
using System.Collections.Generic;
using System.Text;

namespace weka.core
{
    //UPGRADE_NOTE: Field 'EnclosingInstance' was added to class 'FastVectorEnumeration' to access its enclosing instance. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1019'"
    /// <summary> Class for enumerating the vector's elements.</summary>
    public class FastVectorEnumeration : System.Collections.IEnumerator
    {

        private System.Object tempAuxObj;

        public virtual bool MoveNext()
        {
            bool result = hasMoreElements();
            if (result)
            {
                tempAuxObj = nextElement();
            }
            return result;
        }
        public virtual void Reset()
        {
            if (m_SpecialXmlElement == 0)
            {
                m_Counter = 1;
            }
            else
            {
                m_Counter = 0;
            }
            tempAuxObj = null;
        }
        public virtual System.Object Current
        {
            get
            {
                return tempAuxObj;
            }

        }

        /// <summary>The counter. </summary>
        private int m_Counter;
        // These JML commands say how m_Counter implements Enumeration
        //@ in moreXmlElements;
        //@ private represents moreXmlElements = m_Counter < m_Vector.size();
        //@ private invariant 0 <= m_Counter && m_Counter <= m_Vector.size();

        /// <summary>The vector. </summary>
        private FastVector m_Vector;

        /// <summary>Special element. Skipped during enumeration. </summary>
        private int m_SpecialXmlElement;
        //@ private invariant -1 <= m_SpecialXmlElement;
        //@ private invariant m_SpecialXmlElement < m_Vector.size();
        //@ private invariant m_SpecialXmlElement>=0 ==> m_Counter!=m_SpecialXmlElement;

        /// <summary> Constructs an enumeration.
        /// 
        /// </summary>
        /// <param name="vector">the vector which is to be enumerated
        /// </param>
        public FastVectorEnumeration(FastVector vector)
        {

            m_Counter = 0;
            m_Vector = vector;
            m_SpecialXmlElement = -1;
        }

        /// <summary> Constructs an enumeration with a special element.
        /// The special element is skipped during the enumeration.
        /// 
        /// </summary>
        /// <param name="vector">the vector which is to be enumerated
        /// </param>
        /// <param name="special">the index of the special element
        /// </param>
        //@ requires 0 <= special && special < vector.size();
        public FastVectorEnumeration(FastVector vector, int special)
        {

            m_Vector = vector;
            m_SpecialXmlElement = special;
            if (special == 0)
            {
                m_Counter = 1;
            }
            else
            {
                m_Counter = 0;
            }
        }


        /// <summary> Tests if there are any more elements to enumerate.
        /// 
        /// </summary>
        /// <returns> true if there are some elements left
        /// </returns>
        //UPGRADE_NOTE: The equivalent of method 'java.util.Enumeration.hasMoreElements' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
        public virtual bool hasMoreElements()
        {

            if (m_Counter < m_Vector.size())
            {
                return true;
            }
            return false;
        }

        /// <summary> Returns the next element.
        /// 
        /// </summary>
        /// <returns> the next element to be enumerated
        /// </returns>
        //@ also requires hasMoreElements();
        //UPGRADE_NOTE: The equivalent of method 'java.util.Enumeration.nextElement' is not an override method. "ms-help://MS.VSCC.v80/dv_commoner/local/redirect.htm?index='!DefaultContextWindowIndex'&keyword='jlca1143'"
        public virtual System.Object nextElement()
        {

            System.Object result = m_Vector.elementAt(m_Counter);

            m_Counter++;
            if (m_Counter == m_SpecialXmlElement)
            {
                m_Counter++;
            }
            return result;
        }
    }
}
