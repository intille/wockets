// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.BTHNS_INQUIRYBLOB
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Runtime.InteropServices;
using InTheHand.Net.Sockets;

namespace InTheHand.Net.Bluetooth
{
//#if V2
    [StructLayout(LayoutKind.Sequential, Size=8)]
    internal struct BTHNS_INQUIRYBLOB
    {
        internal uint LAP;
        internal short length;
        internal short num_responses;
    }
/*#else
	/// <summary>
	/// This structure contains additional parameters for device inquiries.
	/// </summary>
	internal class BTHNS_INQUIRYBLOB : BTHNS_BLOB
	{

		public BTHNS_INQUIRYBLOB(short length, short responses)
		{
			m_data = new byte[8];

			Lap = 0x9e8b33;
			InquiryLength = length;
			Responses = responses;
		}

		/// <summary>
		/// LAP from which the inquiry access code is derived when the inquiry procedure is made.
		/// </summary>
		public uint Lap
		{
			get
			{
				return BitConverter.ToUInt32(m_data,0);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 0);
			}
		}
		/// <summary>
		/// Amount of time allowed to perform the query.
		/// This value is measured in units of 1.28 seconds (time to query=length*1.28 seconds).
		/// The default value is 16.
		/// </summary>
		public short InquiryLength
		{
			get
			{
				return BitConverter.ToInt16(m_data,4);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 4);
			}
		}
		/// <summary>
		/// Maximum number of devices to retrieve information about before stopping the inquiry. The default value is 16.
		/// </summary>
		public short Responses
		{
			get
			{
				return BitConverter.ToInt16(m_data,6);
			}
			set
			{
				BitConverter.GetBytes(value).CopyTo(m_data, 6);
			}
		}


		
	}
#endif*/
}
