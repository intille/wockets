// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.ObexListenerContext
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.IO;
using System.Net;
using System.Net.Sockets;
using InTheHand.Net;
using InTheHand.Net.Sockets;
using InTheHand.Net.Bluetooth;

namespace InTheHand.Net
{
	/// <summary>
	/// Provides access to the request and response objects used by the <see cref="ObexListener"/> class.
	/// </summary>
	public class ObexListenerContext
	{
		byte[] buffer;
			
		private Socket socket;
		private ObexListenerRequest request;
		private WebHeaderCollection headers = new WebHeaderCollection();
		private MemoryStream bodyStream = new MemoryStream();
		private EndPoint localEndPoint;
		private EndPoint remoteEndPoint;
		ushort remoteMaxPacket = 0;

		internal ObexListenerContext(Socket s)
		{
			buffer = new byte[0x2000];
			this.socket = s;

			this.localEndPoint = s.LocalEndPoint;
			this.remoteEndPoint = s.RemoteEndPoint;

			bool moretoreceive = true;			

			while(moretoreceive)
			{
                //receive the request and store the data for the request object
				int received = 0;

				try
				{
					received = s.Receive(buffer,3,SocketFlags.None);
				}
				catch(SocketException se)
				{
					Console.Write(se.Message);
				}

				if(received == 3)
				{
					ObexMethod method = (ObexMethod)buffer[0];
					//get length (excluding the 3 byte header)
					short len = (short)(IPAddress.NetworkToHostOrder(BitConverter.ToInt16(buffer, 1)) - 3);
					if(len > 0)
					{
                        int iPos = 0;

                        while (iPos < len)
                        {

                            int receivedBytes = s.Receive(this.buffer, iPos+3, s.Available, SocketFlags.None);

                            iPos += receivedBytes;
                        }
					}

					byte[] responsePacket; // Don't init, then the compiler will check that it's set below.

					switch(method)
					{
						case ObexMethod.Get:
                            //gracefully decline
							ObexParser.ParseHeaders(buffer, ref remoteMaxPacket,  bodyStream, headers);
							responsePacket = new byte[3] {(byte)ObexStatusCode.MethodNotAllowed, 0x00, 0x03};
							break;
						case ObexMethod.Connect:
							ObexParser.ParseHeaders(buffer, ref remoteMaxPacket, bodyStream, headers);
							responsePacket = new byte[7] { 0xA0, 0x00, 0x07, 0x10, 0x00, 0x20, 0x00 };
							break;
						case ObexMethod.Put:
							ObexParser.ParseHeaders(buffer, ref remoteMaxPacket,  bodyStream, headers);
							responsePacket = new byte[3] {(byte)(ObexStatusCode.Continue | ObexStatusCode.Final), 0x00, 0x03};
							break;
						case ObexMethod.PutFinal:
							ObexParser.ParseHeaders(buffer, ref remoteMaxPacket,  bodyStream, headers);
                            responsePacket = new byte[3] { (byte)(ObexStatusCode.OK | ObexStatusCode.Final), 0x00, 0x03 };
							break;
						case ObexMethod.Disconnect:
							ObexParser.ParseHeaders(buffer, ref remoteMaxPacket,  bodyStream, headers);
							responsePacket = new byte[3] {(byte)(ObexStatusCode.OK | ObexStatusCode.Final), 0x00, 0x03};
							moretoreceive = false;
							break;
						default:
							Console.WriteLine(method.ToString() + " " + received.ToString());
                            responsePacket = new byte[3] { (byte)ObexStatusCode.NotImplemented, 0x00, 0x03 };
                            break;
					}

					try
					{
                        System.Diagnostics.Debug.Assert(responsePacket != null, "Must always respond to the peer.");
						if(responsePacket!=null)
						{
							s.Send(responsePacket);
						}

					}
					catch(Exception se)
					{
                        // TODO ObexListenerContext swallows any exceptions on responding, and continues!
						Console.WriteLine(se.Message);
					}
				}
				else
				{
					moretoreceive = false;
				}
			}

			s.Close();
			s = null;

			request = new ObexListenerRequest(bodyStream.ToArray(), headers, localEndPoint, remoteEndPoint);
		
		}

		/// <summary>
		/// Gets the <see cref="ObexListenerRequest"/> that represents a client's request for a resource
		/// </summary>
		public ObexListenerRequest Request
		{
			get
			{
				return request;
			}
		}

		/*
		 * For a future version
		/// <summary>
		/// Gets the <see cref="ObexListenerResponse"/> object that will be sent to the client in response to the client's request.
		/// </summary>
		public ObexListenerResponse Response
		{
			get
			{
				return new ObexListenerResponse();
			}
		}*/
	}
}
