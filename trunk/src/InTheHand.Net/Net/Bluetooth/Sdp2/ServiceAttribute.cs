using System;

namespace InTheHand.Net.Bluetooth
{

    /// <summary>
    /// Holds an attribute from an SDP service record.
    /// </summary>
    /// -
    /// <remarks>
    /// Access its SDP Data Element through the 
    /// <see cref="P:InTheHand.Net.Bluetooth.ServiceElement.Value"/> property and read the 
    /// data value through the methods and properties on the returned 
    /// <see cref="T:InTheHand.Net.Bluetooth.ServiceElement"/>.
    /// </remarks>
#if CODE_ANALYSIS
    [System.Diagnostics.CodeAnalysis.SuppressMessage("Microsoft.Naming", "CA1711:IdentifiersShouldNotHaveIncorrectSuffix")]
#endif
    public class ServiceAttribute
    {
        //--------------------------------------------------------------
        ServiceAttributeId m_id;
        ServiceElement m_element;

        //--------------------------------------------------------------

        /// <summary>
        /// Initializes a new instance of the <see cref="T:InTheHand.Net.Bluetooth.ServiceAttribute"/> class.
        /// </summary>
        public ServiceAttribute(ServiceAttributeId id, ServiceElement value)
        {
            m_id = id;
            m_element = value;
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="T:InTheHand.Net.Bluetooth.ServiceAttribute"/> class.
        /// </summary>
        [CLSCompliant(false)] // instead use .ctor(ServiceAttributeId,AttributeValue).
        public ServiceAttribute(UInt16 id, ServiceElement value)
            : this(unchecked((ServiceAttributeId)(Int16)id), value)
        { }

        //--------------------------------------------------------------

        /// <summary>
        /// Get the Attribute Id for this attribute.
        /// </summary>
        public ServiceAttributeId Id
        {
            [System.Diagnostics.DebuggerStepThrough]
            get { return m_id; }
        }

        /// <summary>
        /// Get the value of this attributes as a <see cref="T:InTheHand.Net.Bluetooth.ServiceElement"/>
        /// </summary>
        public ServiceElement Value
        {
            [System.Diagnostics.DebuggerStepThrough]
            get { return m_element; }
        }

    }//class

}