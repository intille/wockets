// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.ObexParser
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.IO;
using System.Net;
using System.Net.Sockets;

namespace InTheHand.Net
{
#if V2
    internal static class ObexParser
    {
#else
	internal class ObexParser
	{
		private ObexParser(){}
#endif //!V2

		internal static void ParseHeaders(byte[] packet, ref ushort remoteMaxPacket, Stream bodyStream, WebHeaderCollection headers)
		{
			ObexMethod method = (ObexMethod)packet[0];
			int packetLength = IPAddress.NetworkToHostOrder(BitConverter.ToInt16(packet, 1));
			
            int pos = 3;

			while (pos < packetLength)
			{
				ObexHeader header = (ObexHeader)packet[pos];
				switch (header)
				{
					case ObexHeader.None:
						return;
					case (ObexHeader)0x10:
						remoteMaxPacket = unchecked((ushort)IPAddress.NetworkToHostOrder(BitConverter.ToInt16(packet, pos + 2)));
						pos += 4;
						break;

					case ObexHeader.ConnectionID:
					case ObexHeader.Count:
					case ObexHeader.Length:
					case ObexHeader.CreatorID:
					case ObexHeader.Time4Byte:
						int intValue = IPAddress.NetworkToHostOrder(BitConverter.ToInt32(packet, pos + 1));
						headers.Add(header.ToString().ToUpper(),intValue.ToString());
						pos += 5;
						break;

					case ObexHeader.Who:
						short whoSize = IPAddress.NetworkToHostOrder(BitConverter.ToInt16(packet, pos + 1));
						byte[] whoBytes = new byte[16];
						Buffer.BlockCopy(packet,pos+3,whoBytes,0,whoSize-3);
						Guid service = new Guid(whoBytes);
						headers.Add(header.ToString().ToUpper(), service.ToString());
						pos += whoSize;
						break;

					case ObexHeader.Body:
					case ObexHeader.EndOfBody:
						short bodySize = IPAddress.NetworkToHostOrder(BitConverter.ToInt16(packet, pos + 1));
						bodyStream.Write(packet, pos +3, bodySize-3);
						pos += bodySize;
						break;

					default:
						int headerSize = IPAddress.NetworkToHostOrder(BitConverter.ToInt16(packet, pos+1));

						if (headerSize > 3)
						{
							string headerString = System.Text.Encoding.BigEndianUnicode.GetString(packet,pos + 3,headerSize-5);
							if(headerString!=null)
							{
								int nullindex = headerString.IndexOf('\0');
								if(nullindex > -1)
								{
									headerString = headerString.Substring(0,nullindex);
								}

								if(headerString!=string.Empty)
								{
									headers.Add(header.ToString().ToUpper(), headerString);
								}
							}
						}

						pos += headerSize;
						break;
				}
				

			}
		}
		
	}
}
