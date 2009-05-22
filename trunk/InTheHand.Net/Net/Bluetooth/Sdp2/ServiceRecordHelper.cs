using System;
#if ! V1
using System.Collections.Generic;
using IList_ServiceElement = System.Collections.Generic.IList<InTheHand.Net.Bluetooth.ServiceElement>;
using List_ServiceElement = System.Collections.Generic.List<InTheHand.Net.Bluetooth.ServiceElement>;
using IEnumerator_ServiceElement = System.Collections.Generic.IEnumerator<InTheHand.Net.Bluetooth.ServiceElement>;
#else
using System.Collections;
using IList_ServiceElement = System.Collections.IList;
using List_ServiceElement = System.Collections.ArrayList;
using IEnumerator_ServiceElement = System.Collections.IEnumerator;
#endif
using System.Text;
using System.Diagnostics;
using InTheHand.Net.Bluetooth.AttributeIds;

namespace InTheHand.Net.Bluetooth
{
    
    /// <summary>
    /// Some useful methods for working with a SDP <see cref="T:InTheHand.Net.Bluetooth.ServiceRecord"/>
    /// including creating and accessing the <see cref="F:InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList"/>
    /// for an RFCOMM service.
    /// </summary>
    public 
#if ! V1
        static 
#endif
        class ServiceRecordHelper
    {
#if V1
        private ServiceRecordHelper() { }
#endif

        //--------------------------------------------------------------

        /// <summary>
        /// Reads the RFCOMM Channel Number element from the service record.
        /// </summary>
        /// <returns>The <see cref="T:InTheHand.Net.Bluetooth.ServiceElement"/>
        /// holding the Channel Number.
        /// or <see langword="null"/> if at the <see cref="F:InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList"/>
        /// attribute is missing or contains invalid elements.
        /// </returns>
        public static ServiceElement GetRfcommChannelElement(ServiceRecord record)
        {
            if (!record.Contains(UniversalAttributeId.ProtocolDescriptorList)) {
                goto NotFound;
            }
            ServiceAttribute attr = record.GetAttributeById(UniversalAttributeId.ProtocolDescriptorList);
            ServiceElement e0 = attr.Value;
            if (e0.ElementType == ElementType.ElementAlternative) {
#if ! WinCE
                Trace.WriteLine("Don't support ElementAlternative ProtocolDescriptorList values.");
#endif
                goto NotFound;
            } else if (e0.ElementType != ElementType.ElementSequence) {
#if ! WinCE
                Trace.WriteLine("Bad ProtocolDescriptorList base element.");
#endif
                goto NotFound;
            }
            IList_ServiceElement protoStack = e0.GetValueAsElementList();
            IEnumerator_ServiceElement etor = protoStack.GetEnumerator();
            ServiceElement layer;
            IList_ServiceElement layerContent;
            if (!etor.MoveNext()) {
#if ! WinCE
                Trace.WriteLine("Protocol stack truncated before {0}.", "L2CAP");
#endif
                goto NotFound;
            }
            layer = (ServiceElement)etor.Current; //cast here are for non-Generic version.
            layerContent = layer.GetValueAsElementList();
            if (((ServiceElement)layerContent[0]).GetValueAsUuid() != BluetoothService.L2CapProtocol) {
#if ! WinCE
                Trace.WriteLine(String.Format(System.Globalization.CultureInfo.InvariantCulture,
                    "Bad protocol stack, layer {0} is not {1}.", 1, "L2CAP"));
#endif
                goto NotFound;
            }
            //
            if (!etor.MoveNext()) {
#if ! WinCE
                Trace.WriteLine("Protocol stack truncated before {0}.", "RFCOMM");
#endif
                goto NotFound;
            }
            layer = (ServiceElement)etor.Current;
            layerContent = layer.GetValueAsElementList();
            if (((ServiceElement)layerContent[0]).GetValueAsUuid() != BluetoothService.RFCommProtocol) {
#if ! WinCE
                Trace.WriteLine(String.Format(System.Globalization.CultureInfo.InvariantCulture,
                    "Bad protocol stack, layer {0} is not {1}.", 2, "RFCOMM"));
#endif
                goto NotFound;
            }
            //
            if (layerContent.Count < 2) {
#if ! WinCE
                Trace.WriteLine(String.Format(System.Globalization.CultureInfo.InvariantCulture,
                    "Bad protocol stack, layer {0} hasn't a second element.", 2));
#endif
                goto NotFound;
            }
            ServiceElement channelElement = (ServiceElement)layerContent[1];
            if (channelElement.ElementType != ElementType.UInt8) {
#if ! WinCE
                Trace.WriteLine(String.Format(System.Globalization.CultureInfo.InvariantCulture,
                    "Bad protocol stack, layer {0} is not UInt8.", 2));
#endif
                goto NotFound;
            }
            // Success
            return channelElement;
        NotFound:
            return null;
        }

        /// <summary>
        /// Reads the RFCOMM Channel Number value from the service record,
        /// or returns -1 if the element is not present.
        /// </summary>
        /// <returns>The Channel Number as an unsigned byte cast to an Int32, 
        /// or -1 if at the <see cref="F:InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList"/>
        /// attribute is missing or contains invalid elements.
        /// </returns>
        public static Int32 GetRfcommChannelNumber(ServiceRecord record)
        {
            ServiceElement channelElement = GetRfcommChannelElement(record);
            if (channelElement == null) {
                return -1;
            }
            System.Diagnostics.Debug.Assert(channelElement.ElementType == ElementType.UInt8);
            byte value = (byte)channelElement.Value;
            return value;
        }

        /// <summary>
        /// Sets the RFCOMM Channel Number value in the service record.
        /// </summary>
        /// -
        /// <exception cref="T:System.InvalidOperation">The
        /// <see cref="F:InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList"/>
        /// attribute is missing or contains invalid elements.
        /// </exception>
        public static void SetRfcommChannelNumber(ServiceRecord record, Byte channelNumber)
        {
            ServiceElement channelElement = GetRfcommChannelElement(record);
            if (channelElement == null) {
                throw new InvalidOperationException("ProtocolDescriptorList element does not exist or is not in the RFCOMM format.");
            }
            System.Diagnostics.Debug.Assert(channelElement.ElementType == ElementType.UInt8);
            channelElement.SetValue(channelNumber);
        }

        //--------------------------------------------------------------

        /// <summary>
        /// Creates the data element for the 
        /// <see cref="F:InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList"/>
        /// attribute in an RFCOMM service
        /// </summary>
        /// -
        /// <remarks>Thus is the following structure:
        /// <code>
        /// ElementSequence
        ///    ElementSequence
        ///       Uuid16 = L2CAP
        ///    ElementSequence
        ///       Uuid16 = RFCOMM
        ///       UInt8  = 0      -- The RFCOMM Channel Number.
        /// </code>
        /// </remarks>
        public static ServiceElement CreateRfcommProtocolDescriptorList()
        {
            return CreateRfcommProtocolDescriptorListWithUpperLayers();
        }

        /// <summary>
        /// Creates the data element for the 
        /// <see cref="F:InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList"/>
        /// attribute in an GOEP (i.e. OBEX) service
        /// </summary>
        /// -
        /// <remarks>Thus is the following structure:
        /// <code>
        /// ElementSequence
        ///    ElementSequence
        ///       Uuid16 = L2CAP
        ///    ElementSequence
        ///       Uuid16 = RFCOMM
        ///       UInt8  = 0      -- The RFCOMM Channel Number.
        ///    ElementSequence
        ///       Uuid16 = GOEP
        /// </code>
        /// </remarks>
        public static ServiceElement CreateGoepProtocolDescriptorList()
        {
            return CreateRfcommProtocolDescriptorListWithUpperLayers(
               CreatePdlLayer((UInt16)ServiceRecordUtilities.HackProtocolId.Obex));
        }

        private static ServiceElement CreateRfcommProtocolDescriptorListWithUpperLayers(params ServiceElement[] upperLayers)
        {
            IList_ServiceElement baseChildren = new List_ServiceElement();
            baseChildren.Add(CreatePdlLayer((UInt16)ServiceRecordUtilities.HackProtocolId.L2Cap));
            baseChildren.Add(CreatePdlLayer((UInt16)ServiceRecordUtilities.HackProtocolId.Rfcomm, 
                new ServiceElement(ElementType.UInt8, (byte)0)));
            foreach (ServiceElement nextLayer in upperLayers) {
                if (nextLayer.ElementType != ElementType.ElementSequence) {
                    throw new ArgumentException("Each layer in a ProtocolDescriptorList must be an ElementSequence.");
                }
                baseChildren.Add(nextLayer);
            }//for
            ServiceElement baseElement = new ServiceElement(ElementType.ElementSequence, baseChildren);
            return baseElement;
        }

        private static ServiceElement CreatePdlLayer(UInt16 uuid, params ServiceElement[] data)
        {
            IList_ServiceElement curSeqChildren;
            ServiceElement curValueElmt, curSeqElmt;
            //
            curSeqChildren = new List_ServiceElement();
            curValueElmt = new ServiceElement(ElementType.Uuid16, uuid);
            curSeqChildren.Add(curValueElmt);
            foreach (ServiceElement element in data) {
                curSeqChildren.Add(element);
            }
            curSeqElmt = new ServiceElement(ElementType.ElementSequence, curSeqChildren);
            return curSeqElmt;
        }

    }//class

}
