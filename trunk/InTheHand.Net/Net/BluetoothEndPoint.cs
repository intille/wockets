// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.BluetoothEndPoint
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Net;
using System.Net.Sockets;
using InTheHand.Net.Bluetooth;
using InTheHand.Net.Sockets;

namespace InTheHand.Net
{
	/// <summary>
	/// Establishes connections to a peer device and provides Bluetooth port information.
	/// </summary>
#if !WinCE
    [Serializable]
#endif
	public class BluetoothEndPoint : EndPoint
	{
		private BluetoothAddress m_id;
		private Guid m_service;
		private int m_port;
#if WinCE
        private const int defaultPort = 0;
#else
        private const int defaultPort = -1;
#endif


        #region Constructor
        private BluetoothEndPoint()
        {
            // For XmlSerialization (etc?) use only!
        }

        /// <summary>
		/// Initializes a new instance of the <see cref="BluetoothEndPoint"/> class with the specified address and service.
		/// </summary>
		/// <param name="address">The Bluetooth address of the device. A six byte array.</param>
		/// <param name="service">The Bluetooth service to use.</param>
		public BluetoothEndPoint(BluetoothAddress address, Guid service) : this(address, service, defaultPort)
		{
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="BluetoothEndPoint"/> class with the specified address, service and port number.
		/// </summary>
		/// <param name="address">The Bluetooth address of the device. A six byte array.</param>
		/// <param name="service">The Bluetooth service to use.</param>
		/// <param name="port">Radio channel to use, -1 for any.</param>
		public BluetoothEndPoint(BluetoothAddress address, Guid service, int port)
		{
			
			m_id = address;
			m_service = service;
			m_port = port;
           
        }
            #endregion

        // As seen below the structures on Win32 and WinCE are the same, except that 
        // Win32 has 1-byte alignment turned on.  Thus on Win32 there are also no 
        // 64-bit differences.
        //
        // * Win32
        //typedef ULONGLONG BTH_ADDR, *PBTH_ADDR;
        //
        //#include <pshpack1.h>
        //struct _SOCKADDR_BTH
        //{
        //    USHORT    addressFamily;  // Always AF_BTH
        //    BTH_ADDR  btAddr;         // Bluetooth device address
        //    GUID      serviceClassId; // [OPTIONAL] system will query SDP for port
        //    ULONG     port;           // RFCOMM channel or L2CAP PSM
        //}
        //
        // * WinCE
        //typedef ULONGLONG bt_addr, *pbt_addr, BT_ADDR, *PBT_ADDR;
        //
        //struct _SOCKADDR_BTH
        //{
        //    USHORT   addressFamily;
        //    bt_addr  btAddr;
        //    GUID     serviceClassId;
        //    ULONG    port;
        //}

        #region Serialize
        /// <summary>
		/// Serializes endpoint information into a <see cref="SocketAddress"/> instance.
		/// </summary>
		/// <returns>A <see cref="SocketAddress"/> instance containing the socket address for the endpoint.</returns>
		public override SocketAddress Serialize()
		{
#if WinCE
            SocketAddress btsa = new SocketAddress(AddressFamily32.Bluetooth, 40);
#else
			SocketAddress btsa = new SocketAddress(AddressFamily32.Bluetooth, 30);
#endif
			//copy address type
			btsa[0] = 32;
			
			//copy device id
			if(m_id != null)
			{
				byte[] deviceidbytes = m_id.ToByteArray();

				for(int idbyte =0; idbyte < 6; idbyte++)
				{
#if WinCE
                    btsa[idbyte + 8] = deviceidbytes[idbyte];
#else
					btsa[idbyte + 2] = deviceidbytes[idbyte];
#endif
				}
			}

			//copy service clsid
            if (m_service != Guid.Empty)
            {
                byte[] servicebytes = m_service.ToByteArray();
                for (int servicebyte = 0; servicebyte < 16; servicebyte++)
                {
#if WinCE
                    btsa[servicebyte + 16] = servicebytes[servicebyte];
#else
                    btsa[servicebyte + 10] = servicebytes[servicebyte];
#endif
                }
            }
			
			//copy port
			byte[] portbytes = BitConverter.GetBytes(m_port);
			for(int portbyte = 0; portbyte < 4; portbyte++)
			{
#if WinCE
                btsa[portbyte + 32] = portbytes[portbyte];
#else
				btsa[portbyte + 26] = portbytes[portbyte];
#endif
			}
			
			return btsa;
        }
        #endregion

        #region Create
        /// <summary>
		/// Creates an endpoint from a socket address.
		/// </summary>
		/// <param name="socketAddress">The <see cref="SocketAddress"/> to use for the endpoint.</param>
		/// <returns>An <see cref="EndPoint"/> instance using the specified socket address.</returns>
		public override EndPoint Create(SocketAddress socketAddress)
		{
			if(socketAddress == null)
			{
				throw new ArgumentNullException("socketAddress");
			}

			//if a Bluetooth SocketAddress
			if(socketAddress[0] == 32)
			{
				int ibyte;

				byte[] addrbytes = new byte[6];
				for(ibyte = 0; ibyte < 6; ibyte++)
				{
#if WinCE
                    addrbytes[ibyte] = socketAddress[8 + ibyte];
#else
					addrbytes[ibyte] = socketAddress[2 + ibyte];
#endif
				}
				
				byte[] servicebytes = new byte[16];
				for(ibyte = 0; ibyte < 16; ibyte++)
				{
#if WinCE
                    servicebytes[ibyte] = socketAddress[16 + ibyte];
#else
					servicebytes[ibyte] = socketAddress[10 + ibyte];
#endif
				}

				byte[] portbytes = new byte[4];
				for(ibyte = 0; ibyte < 4; ibyte++)
				{
#if WinCE
                    portbytes[ibyte] = socketAddress[32 + ibyte];
#else
					portbytes[ibyte] = socketAddress[26 + ibyte];
#endif
				}
				
				return new BluetoothEndPoint(new BluetoothAddress(addrbytes), new Guid(servicebytes), BitConverter.ToInt32(portbytes, 0));
				
			}
			else
			{
				//use generic method
				return base.Create(socketAddress);
			}
        }
        #endregion

        #region Equals
        /// <summary>
		/// Compares two <see cref="BluetoothEndPoint"/> instances for equality.
		/// </summary>
		/// <param name="obj"></param>
		/// <returns></returns>
		public override bool Equals(object obj)
		{
			BluetoothEndPoint bep = obj as BluetoothEndPoint;
			
			if(bep!=null)
			{
				return (this.Address.Equals(bep.Address) && this.Service.Equals(bep.Service));	
			}

			return base.Equals (obj);

        }
        #endregion

        #region Get Hash Code
        /// <summary>
		/// Returns the hash code for this instance.
		/// </summary>
		/// <returns></returns>
		public override int GetHashCode()
		{
			return this.Address.GetHashCode();
        }
        #endregion

        #region To String
        /// <summary>
        /// Returns the string representation of the BluetoothEndPoint.
        /// </summary>
        /// <remarks>
        /// <para>
        /// We try to follow existing examples where possible; JSR-82 and similar
        /// use a URI of the form:</para>
        /// <code>bluetooth://xxxxxxxxxxxx:xx</code>
        /// or:
        /// <code>bluetooth://xxxxxxxxxxxx:xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx</code>
        /// or in some serialport only situations:
        /// <code>btspp://</code>
        /// <para>So we follow that pattern here, but of course without the URI prefix.
        /// If the form with the URI is required then the prefix can simply be appended.</para>
        /// <para>
        /// If the port is non default then we use that, otherwise just the full guid.
        /// </para>
        /// <para>Some examples are:</para>
        /// To the ObexObjectPush service:
        /// <code>"04E2030405F6:0000110500001000800000805f9b34fb"</code>
        /// To the SerialPort service:
        /// <code>"04E2030405F6:0000110100001000800000805f9b34fb"</code>
        /// With an Empty service GUID:
        /// <code>"04E2030405F6:00000000000000000000000000000000"</code>
        /// With port 9:
        /// <code>"04E2030405F6:9"</code>
        /// </remarks>
        /// <returns>The string representation of the BluetoothEndPoint.</returns>
        public override string ToString()
        {
            //if port is set then use that in uri else use full service guid
            if (this.m_port != defaultPort)
            {
                return Address.ToString() + ":" + Port.ToString();
            }
            else
            {
                return Address.ToString() + ":" + Service.ToString("N");
            }
        }
        #endregion

        #region Address Family
        /// <summary>
		/// Gets the address family of the Bluetooth address. 
		/// </summary>
		public override AddressFamily AddressFamily
		{
			get
			{
				return (AddressFamily)32;
			}
        }
        #endregion

        #region Address
        /// <summary>
		/// Gets or sets the Bluetooth address of the endpoint.
		/// </summary>
		public BluetoothAddress Address
		{
			get
			{
				return m_id;
			}
			set
			{
				m_id = value;
			}
        }
        #endregion

        #region Service
        /// <summary>
		/// Gets or sets the Bluetooth service to use for the connection.
		/// </summary>
		public Guid Service
		{
			get
			{
				return m_service;
			}
			set
			{
				m_service = value;
			}
        }
        #endregion

        #region Port
        /// <summary>
		/// Gets or sets the service channel number of the endpoint.
		/// </summary>
		public int Port
		{
			get
			{
				return m_port;
			}
			set
			{
				m_port = value;
			}
        }
        #endregion


        #region Consts
        /// <summary>
		/// Specifies the minimum value that can be assigned to the Port property.
		/// </summary>
		public const int MinPort = 1;

		/// <summary>
		/// Specifies the maximum value that can be assigned to the Port property.
		/// </summary>
		public const int MaxPort = 0xffff;
        #endregion

    }
}
