// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.ObexListener
// 
// Copyright (c) 2003-2007 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

//#define ADD_SERVICE_NAME_TO_SDP_RECORD


using System;
using System.Net;
using System.Net.Sockets;
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;

namespace InTheHand.Net
{
	/// <summary>
	/// Provides a simple, programmatically controlled OBEX protocol listener.
	/// </summary>
	public class ObexListener
	{
		//changed sdp to use the uuid16 of the obexpush service
		private static readonly byte[] ServiceRecordExpected = new byte[] {
		    0x35,0x25,0x09,0x00,0x01,0x35,0x03,0x19,
		    0x11,0x05,0x09,0x00,0x04,0x35,0x11,0x35,
		    0x03,0x19,0x01,0x00,0x35,0x05,0x19,0x00,
		    0x03,0x08,0x00,0x35,0x03,0x19,0x00,0x08,
		    0x09,0x03,0x03,0x35,0x02,0x08,0xFF};
        private const int ServiceRecordExpectedPortOffset = 26;

		/*0x35,0x33,0x09,0x00,0x01,0x35,0x11,0x1c,
		0x05,0x11,0x00,0x00,0x00,0x00,0x00,0x10,
		0x80,0x00,0x00,0x80,0x5F,0x9B,0x34,0xFB,
		0x09,0x00,0x04,0x35,0x11,0x35,0x03,0x19,
		0x01,0x00,0x35,0x05,0x19,0x00,0x03,0x08,
		0x00,0x35,0x03,0x19,0x00,0x08,0x09,0x03,
		0x03,0x35,0x02,0x08,0xFF};*/

		private ObexTransport transport;
		private IrDAListener iListener;
		private BluetoothListener bListener;
        private TcpListener tListener;

		private bool listening = false;

		/// <summary>
		/// Initializes a new instance of the ObexListener class using the Bluetooth transport.
		/// </summary>
		public ObexListener() : this(ObexTransport.Bluetooth)
		{
		}
		/// <summary>
		/// Initializes a new instance of the ObexListener class specifiying the transport to use.
		/// </summary>
		public ObexListener(ObexTransport transport)
		{
#if WinCE
            PlatformVerification.ThrowException();
#endif
			switch(transport)
			{
				case ObexTransport.Bluetooth:
                    ServiceRecord record = CreateServiceRecord();
                    bListener = new BluetoothListener(BluetoothService.ObexObjectPush, record);
                    bListener.ServiceClass = ServiceClass.ObjectTransfer;
					break;
				case ObexTransport.IrDA:
					iListener = new IrDAListener("OBEX");
					break;
                case ObexTransport.Tcp:
                    tListener = new TcpListener(IPAddress.Any, 650);
                    break;
				default:
					throw new ArgumentException("Invalid transport specified");
			}
			this.transport = transport;
		}

        private static ServiceRecord CreateServiceRecord()
        {
            ServiceElement englishUtf8PrimaryLanguage = CreateEnglishUtf8PrimaryLanguageServiceElement();
            ServiceRecord record = new ServiceRecord(
                new ServiceAttribute(InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ServiceClassIdList,
                    new ServiceElement(ElementType.ElementSequence,
                        new ServiceElement(ElementType.Uuid16, (UInt16)0x1105))),
                new ServiceAttribute(InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProtocolDescriptorList,
                    ServiceRecordHelper.CreateGoepProtocolDescriptorList()),
#if ADD_SERVICE_NAME_TO_SDP_RECORD
                // Could add ServiceName, ProviderName etc here.
                new ServiceAttribute(InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.LanguageBaseAttributeIdList,
                    englishUtf8PrimaryLanguage),
                new ServiceAttribute(ServiceRecord.CreateLanguageBasedAttributeId(
                        InTheHand.Net.Bluetooth.AttributeIds.UniversalAttributeId.ProviderName,
                        LanguageBaseItem.PrimaryLanguageBaseAttributeId),
                    new ServiceElement(ElementType.TextString, "32feet.NET")),
#endif
                //
                new ServiceAttribute(InTheHand.Net.Bluetooth.AttributeIds.ObexAttributeId.SupportedFormatsList,
                    new ServiceElement(ElementType.ElementSequence,
                        new ServiceElement(ElementType.UInt8, (byte)0xFF)))
                );
            return record;
        }

        private static ServiceElement CreateEnglishUtf8PrimaryLanguageServiceElement()
        {
            ServiceElement englishUtf8PrimaryLanguage = LanguageBaseItem.CreateElementSequenceFromList(
                new LanguageBaseItem[] {
                    new LanguageBaseItem("en", LanguageBaseItem.Utf8EncodingId, LanguageBaseItem.PrimaryLanguageBaseAttributeId)
                });
            return englishUtf8PrimaryLanguage;
        }

        // HACK Remove ObexListener.TestRecordAsExpected -- after one general release?
        private void TestRecordAsExpected(byte[] serviceRecord_Expected, BluetoothListener bListener)
        {
#if ! ADD_SERVICE_NAME_TO_SDP_RECORD
            serviceRecord_Expected[ServiceRecordExpectedPortOffset] = (byte)bListener.LocalEndPoint.Port;
            ServiceRecord record = bListener.ServiceRecord;
            byte[] actualRecordBytes = record.ToByteArray();
            ServiceRecord tmpSeeExpectedFormat = ServiceRecord.CreateServiceRecordFromBytes(serviceRecord_Expected);
            Arrays_Equal(serviceRecord_Expected, actualRecordBytes);
#endif
        }

        internal static void Arrays_Equal(byte[] expected, byte[] actual) // as NETCFv1 not Generic <T>
        {
            if (expected.Length != actual.Length) {
                throw new InvalidOperationException("diff lengs!!!");
            }
            for (int i = 0; i < expected.Length; ++i) {
                if (!expected[i].Equals(actual[i])) {
                    throw new InvalidOperationException(String.Format(System.Globalization.CultureInfo.InvariantCulture,
                        "diff at {0}, x: 0x{1:X2}, y: 0x{2:X2} !!!", i, expected[i], actual[i]));
                }
            }
        }

        //--------------------------------------------------------------

		/// <summary>
		/// Gets a value that indicates whether the <see cref="ObexListener"/> has been started.
		/// </summary>
		public bool IsListening
		{
			get
			{
				return listening;
			}
		}

		/// <summary>
		/// Allows this instance to receive incoming requests.
		/// </summary>
		public void Start()
		{
            switch (transport)
            {
                case ObexTransport.Bluetooth:
                    bListener.Start();
                    TestRecordAsExpected(ServiceRecordExpected, bListener);
                    break;
                case ObexTransport.IrDA:
                    iListener.Start();
                    break;
                case ObexTransport.Tcp:
                    tListener.Start();
                    break;
            }
			
			listening = true;
		}

		/// <summary>
		/// Causes this instance to stop receiving incoming requests.
		/// </summary>
		public void Stop()
		{
			listening = false;
            switch (transport)
            {
                case ObexTransport.Bluetooth:
                    bListener.Stop();
                    break;
                case ObexTransport.IrDA:
                    iListener.Stop();
                    break;
                case ObexTransport.Tcp:
                    tListener.Stop();
                    break;
            }
		}

		/// <summary>
		/// Shuts down the ObexListener.
		/// </summary>
		public void Close()
		{
			if(listening)
			{
				this.Stop();
			}
		}

		/// <summary>
		/// Waits for an incoming request and returns when one is received.
		/// </summary>
		/// <returns></returns>
		public ObexListenerContext GetContext()
		{
			if(!listening)
			{
				throw new InvalidOperationException("Listener not started");
			}

			try
			{
				Socket s;

                switch (transport)
                {
                    case ObexTransport.Bluetooth:
                        s = bListener.AcceptSocket();
                        break;
                    case ObexTransport.IrDA:
                        s = iListener.AcceptSocket();
                        break;
                    default:
                        s = tListener.AcceptSocket();
                        break;
                }

				return new ObexListenerContext(s);
			}
			catch
			{
				return null;
			}
		}
	}
}
