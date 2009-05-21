// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Ports.PORTEMUPortParams
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using InTheHand.Net;
using System.Runtime.InteropServices;

#if WinCE

namespace InTheHand.Net.Ports
{
#if V2
    [StructLayout(LayoutKind.Sequential)]
    internal struct PORTEMUPortParams
    {
        internal int channel;
        [MarshalAs(UnmanagedType.Bool)]
        internal bool flocal;
        internal long device;//10
        internal int imtu;
        internal int iminmtu;
        internal int imaxmtu;
        internal int isendquota;
        internal int irecvquota;
        internal Guid uuidService;//16
        internal RFCOMM_PORT_FLAGS uiportflags;
    }
#else

	// <summary>
	// Used when creating a virtual serial port.
	// </summary>
	internal sealed class PORTEMUPortParams
	{
		/*int channel;
		int flocal;
		BD_ADDR device;10
		int imtu;
		int iminmtu;
		int imaxmtu;
		int isendquota;
		int irecvquota;
		GUID uuidService;16
		unsigned int uiportflags;*/

		private byte[] m_data;
		
		// <summary>
		// 
		// </summary>
        internal PORTEMUPortParams()
		{
			m_data = new byte[56];
		}

		internal byte[] ToByteArray()
		{
			return m_data;
		}

		// <summary>
		// Set to either an explicit server channel, or, for a server application that wants the server channel to be autobound, to RFCOMM_CHANNEL_MULTIPLE.
		// </summary>
        internal int channel
		{
			get
			{
				return BitConverter.ToInt32(m_data, 0);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 0);
			}
		}
		// <summary>
		// Set to TRUE for a server port that accepts connections, or to FALSE for a client port that is used to creating outgoing connections.
		// </summary>
        internal bool flocal
		{
			get
			{
				return Convert.ToBoolean(BitConverter.ToInt32(m_data, 4));
			}
			set
			{
				BitConverter.GetBytes((int)(value ? 1 : 0)).CopyTo(m_data, 4);
			}
		}

		// <summary>
		// The address of a target device on a client port.
		// </summary>
        internal long device
		{
			get
			{
                return BitConverter.ToInt64(m_data, 8);
				/*BluetoothAddress ba = new BluetoothAddress();
				Buffer.BlockCopy(m_data, 8, ba.ToByteArray(), 0, 6);
				return ba;*/
			}
			set
			{
                BitConverter.GetBytes(value).CopyTo(m_data, 8);
				//Buffer.BlockCopy(value.ToByteArray(), 0, m_data, 8, 6);
			}
		}

        internal int imtu
		{
			get
			{
				return BitConverter.ToInt32(m_data, 16);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 16);
			}
		}

        internal int iminmtu
		{
			get
			{
				return BitConverter.ToInt32(m_data, 20);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 20);
			}
		}

        internal int imaxmtu
		{
			get
			{
				return BitConverter.ToInt32(m_data, 24);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 24);
			}
		}

        internal int isendquota
		{
			get
			{
				return BitConverter.ToInt32(m_data, 28);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 28);
			}
		}

        internal int irecvquota
		{
			get
			{
				return BitConverter.ToInt32(m_data, 32);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 32);
			}
		}
		//etc


		// <summary>
		// Specifies the UUID for the target RFCOMM service.
		// If channel == 0 for the client port, an SDP query is performed to determine the target channel id before the connection is made.
		// </summary>
        internal Guid uuidService
		{
			get
			{
				byte[] guidbytes = new byte[16];
				Buffer.BlockCopy(m_data, 36, guidbytes, 0, 16);
				return new Guid(guidbytes);
			}
			set
			{
				Buffer.BlockCopy(value.ToByteArray(), 0, m_data, 36, 16);
			}
		}

		// <summary>
		// Port Flags.
		// </summary>
        internal RFCOMM_PORT_FLAGS uiportflags
		{
			get
			{
                return (RFCOMM_PORT_FLAGS)BitConverter.ToInt32(m_data, 52);
			}
			set
			{
				BitConverter.GetBytes((int)value).CopyTo(m_data, 52);
			}
		}
	}
#endif

	[Flags()]
    internal enum RFCOMM_PORT_FLAGS : int
	{
        REMOTE_DCB = 0x00000001,
        KEEP_DCD = 0x00000002,
        AUTHENTICATE = 0x00000004,
        ENCRYPT = 0x00000008, 
	}
}

#endif