// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.ObexWebRequest
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
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
	/// Provides an OBEX implementation of the <see cref="WebRequest"/> class.
	/// </summary>
    /// -
    /// <remarks>
    /// <para>If you want to transfer an file or other object using the standard 
    /// service as used by Windows' Wireless Link / Bluetooth File Transfer Wizard, 
    /// Palm's Beam, Nokia's Send via Infrared, then use the OBEX protocol.  
    /// </para>
    /// <para>Only the PUT operation is supported, GET is not, nor is changing folders 
    /// or getting a folder listing.  There are some issue with handling file names 
    /// that include non-English characters, and in the previous version connections 
    /// to some device types failed.
    /// </para>
    /// </remarks>
    /// -
    /// <example>
    /// Use code like the following to send a file.
    /// <code>
    /// ' The host part of the URI is the device address, e.g. IrDAAddress.ToString(),
    /// ' and the file part is the OBEX object name.
    /// Dim uri As New Uri("obex://112233445566/HelloWorld.txt")
    /// Dim req As New ObexWebRequest(uri)
    /// req.ReadFile("Hello World.txt")
    /// Dim rsp As ObexWebResponse = CType(req.GetResponse(),ObexWebResponse)
    /// Console.WriteLine("Response Code: {0} (0x{0:X})", rsp.StatusCode)
    /// </code>
    /// Or, to send locally generated content use something like the following.
    /// <code>
    /// ' The host part of the URI is the device address, e.g. IrDAAddress.ToString(),
    /// ' and the file part is the OBEX object name.
    /// Dim uri As New Uri("obex://112233445566/HelloWorld2.txt")
    /// Dim req As New ObexWebRequest(uri)
    /// Using content As Stream = req.GetRequestStream()
    ///    ' Using a StreamWriter to write text to the stream...
    ///    Using wtr As New StreamWriter(content)
    ///       wtr.WriteLine("Hello World GetRequestStream")
    ///       wtr.WriteLine("Hello World GetRequestStream 2")
    ///       wtr.Flush()
    ///       ' Set the Length header value
    ///       req.ContentLength = content.Length
    ///    End Using
    ///    ' In this case closing the StreamWriter also closed the Stream, but ...
    /// End Using
    /// Dim rsp As ObexWebResponse = CType(req.GetResponse(),ObexWebResponse) 
    /// Console.WriteLine("Response Code: {0} (0x{0:X})", rsp.StatusCode)
    /// </code>
    /// See also the ObexPushApplication and ObexPushVB sample programs.
    /// </example>
	public class ObexWebRequest : WebRequest
	{
		private System.IO.MemoryStream requestStream = new System.IO.MemoryStream();
		

		private bool connected = false;
		private Socket s;
        private Stream ns;
        private Stream m_alreadyConnectedObexStream;

		
		private ushort remoteMaxPacket = 0x400;
        private int connectionId = 0; //HACK connectionId made readonly to stop compile-time warning.

		#region Constructor
		static ObexWebRequest()
		{
            PlatformVerification.ThrowException();

			//register the obex schemes with the WebRequest base method
			ObexWebRequestCreate owrc = new ObexWebRequestCreate();
			WebRequest.RegisterPrefix("obex",owrc);
			WebRequest.RegisterPrefix("obex-push",owrc);
			WebRequest.RegisterPrefix("obex-ftp",owrc);
			WebRequest.RegisterPrefix("obex-sync",owrc);
		}

        /// <overloads>
        /// Create a new Obex request with the specified <see cref="Uri"/>.
        /// </overloads>
        /// -
        /// <summary>
		/// Create a new Obex request with the specified <see cref="Uri"/>.
		/// </summary>
		/// <param name="requestUri"></param>
		/// <remarks>Uri must use one of the following schemes - obex, obex-push, obex-ftp, obex-sync.
		/// The host name must be the device address in short hex, or dotted hex notation - not the default representation using the colon separator</remarks>
		public ObexWebRequest(Uri requestUri)
		{
            if (requestUri == null) {
                throw new ArgumentNullException("requestUri");
            }
			if(!requestUri.Scheme.StartsWith("obex"))
			{
				throw new UriFormatException("Scheme type not supported by ObexWebRequest");
			}
			uri = requestUri;
		}

        /// <summary>
        /// [Advanced usage]
        /// Create a new Obex request with the specified <see cref="T:System.Uri"/> 
        /// and the open <see cref="T:System.IO.Stream"/> connection to an OBEX server.
        /// </summary>
        /// -
        /// <param name="requestUri">[Advanced usage]
        /// A url of the form 
        /// &#x201C;<i>scheme</i><c>:///</c><i>filename</i>&#x201D;, 
        /// &#x201C;e.g. <c>obex:///foo.txt</c>&#x201D;.
        /// That is the host part must be blank, 
        /// and the scheme and filename parts set as for the other constructor 
        /// <see cref="M:InTheHand.Net.ObexWebRequest.#ctor(System.Uri)"/>
        /// </param>
        /// <param name="stream">An instance of <see cref="T:System.IO.Stream"/>
        /// already connected to an OBEX server.
        /// </param>
        public ObexWebRequest(Uri requestUri, Stream stream)
            : this(requestUri)
        {
            if (requestUri == null) {
                throw new ArgumentNullException("requestUri");
            }
            if (requestUri.Host.Length != 0) {
                throw new ArgumentException("Uri must have no host part when passing in the connection stream.");
            }
            if (stream == null) {
                throw new ArgumentNullException("stream");
            }
            if (!(stream.CanRead && stream.CanWrite)) {
                throw new ArgumentException("Stream must be open for reading and writing.");
            }
            m_alreadyConnectedObexStream = stream;
        }
        #endregion

		#region Headers
        private WebHeaderCollection headers = new WebHeaderCollection();
		/// <summary>
        /// Specifies a collection of the name/value pairs that make up the OBEX headers.
		/// </summary>
		public override WebHeaderCollection Headers
		{
			get
			{
				return headers;
			}
			set
			{
				headers = value;
			}
		}
		#endregion

		#region Method
        private ObexMethod method = ObexMethod.Put;
		/// <summary>
		/// Gets or sets the method for the request.
		/// </summary>
		/// <remarks>For Object Exchange the method code is mapped to the equivalent HTTP style method.
		/// For example "PUT", "GET" etc. In this version only "PUT" is supported and is the default value.</remarks>
		public override string Method
		{
			get
			{
				switch(method)
				{
					case ObexMethod.Put:
						return "PUT";
					case ObexMethod.Get:
						return "GET";
					default:
						return "";
				}
			}
			set
			{
				switch(value.ToUpper())
				{
					case "PUT":
						method = ObexMethod.Put;
						break;
					case "GET":
						method = ObexMethod.Get;
						break;
					default:
						throw new InvalidOperationException("Method not supported");
				}
			}
		}
		#endregion

		#region Connect
		private ObexStatusCode Connect()
		{
			if (!connected)
			{
                if(ns == null)
				{
                    try
                    {
                        if (uri.Host.Length == 0) {
                            System.Diagnostics.Debug.Assert(m_alreadyConnectedObexStream != null);
                            System.Diagnostics.Debug.Assert(m_alreadyConnectedObexStream.CanRead
                                && m_alreadyConnectedObexStream.CanWrite);
                            ns = m_alreadyConnectedObexStream;
                        } else {
                            BluetoothAddress ba;
                            IrDAAddress ia;
                            if(BluetoothAddress.TryParse(uri.Host,out ba))
                            {
                                s = new Socket(AddressFamily32.Bluetooth, SocketType.Stream, BluetoothProtocolType.RFComm);
                                Guid serviceGuid;

                                switch (uri.Scheme)
                                {
                                    case "obex-ftp":
                                        serviceGuid = BluetoothService.ObexFileTransfer;
                                        break;
                                    //potential for other obex based profiles to be added
                                    case "obex-sync":
                                        serviceGuid = BluetoothService.IrMCSyncCommand;
                                        break;
                                    default:
                                        serviceGuid = BluetoothService.ObexObjectPush;
                                        break;
                                }


                                BluetoothEndPoint bep = new BluetoothEndPoint(ba, serviceGuid);
                                s.Connect(bep);
                            }
                            else if (IrDAAddress.TryParse(uri.Host, out ia))
                            {
                                //irda
                                s = new Socket(AddressFamily.Irda, SocketType.Stream, ProtocolType.IP);

                                IrDAEndPoint iep = new IrDAEndPoint(ia, "OBEX");

                                s.Connect(iep);
                            }
                            else
                            {
                                //assume a tcp host
                                s = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);

                                IPAddress ipa;
                                try
                                {
                                    ipa = IPAddress.Parse(uri.Host);
                                }
                                catch
                                {
                                    // Compile-time: warning CS0618: 'System.Net.Dns.Resolve(string)' 
                                    //    is obsolete: 'Resolve is obsoleted for this type, 
                                    //    please use GetHostEntry instead. http://go.microsoft.com/fwlink/?linkid=14202'
                                    // However GetHostEntry isn't supported on NETCFv1,
                                    // so just keep it and disable the warning on
                                    // the other platforms.
#if V1
/*
#endif
#pragma warning disable 618
#if V1
*/
#endif
                                    ipa = System.Net.Dns.Resolve(uri.Host).AddressList[0];
#if V1
/*
#endif
#pragma warning restore 618
#if V1
*/
#endif
                                }

                                IPEndPoint ipep = new IPEndPoint(ipa, 650);

                                s.Connect(ipep);
                            }
                     
                            ns = new NetworkStream(s, true);

#if V2 && WinXP
                            ns.ReadTimeout = timeout;
                            ns.WriteTimeout = timeout;
#endif
                        }

                        //do obex negotiation
                        byte[] connectPacket;
                        if (uri.Scheme == "obex-ftp")
                        {
                            connectPacket = new byte[] { 0x80, 0x00, 26, 0x10, 0x00, 0x20, 0x00, 0x46, 0x00, 19, 0xF9, 0xEC, 0x7B, 0xC4, 0x95, 0x3C, 0x11, 0xD2, 0x98, 0x4E, 0x52, 0x54, 0x00, 0xDC, 0x9E, 0x09 };
                        }
                        else
                        {
                            connectPacket = new byte[7] { 0x80, 0x00, 0x07, 0x10, 0x00, 0x20, 0x00 };
                        }
                        ns.Write(connectPacket, 0, connectPacket.Length);

                        byte[] receivePacket = new byte[3];

                        int bytesReceived = ns.Read(receivePacket, 0, 3);
                        
                        //failure
                        if (bytesReceived == 0)
                        {
                            throw new Exception("Connection Lost");
                        }

                        while (bytesReceived < 3)
                        {
                            bytesReceived += ns.Read(receivePacket, bytesReceived, 3 - bytesReceived);
                        }
                        if (receivePacket[0] == (byte)(ObexStatusCode.OK | ObexStatusCode.Final))
                        {
                            //get length
                            short len = (short)(IPAddress.NetworkToHostOrder(BitConverter.ToInt16(receivePacket, 1)) - 3);

                            byte[] receivePacket2 = new byte[3+len];
                            Buffer.BlockCopy(receivePacket, 0, receivePacket2, 0, 3);
                            int nextReceived = ns.Read(receivePacket2, 3, len);
                            if(nextReceived == 0)
                            {
                                throw new Exception("Connection Lost");
                            }
                            bytesReceived += nextReceived;
                            while (bytesReceived < len+3)
                            {
                                bytesReceived += ns.Read(receivePacket2, 3+bytesReceived, len - bytesReceived);
                            }
                            ObexParser.ParseHeaders(receivePacket2, ref remoteMaxPacket, null, headers);

                            if (headers["CONNECTIONID"] != null)
                            {
                                connectionId = int.Parse(headers["CONNECTIONID"]);
                            }
                            //ParseHeaders(receivePacket2, headers, null);
                        }
                        
                        return (ObexStatusCode)receivePacket[0];

                    }
					finally
					{
						if (s != null && !s.Connected)
						{
							s = null;
						}
					}
				}
			}
			return (ObexStatusCode)0;
		}
		#endregion

		#region Content Type
		/// <summary>
		/// Gets or sets the value of the Type OBEX header.
		/// </summary>
		public override string ContentType
		{
			get
			{
				return headers["TYPE"];
			}
			set
			{
				headers["TYPE"] = value;
			}
		}

		#endregion

		#region Content Length
		/// <summary>
		/// Gets or sets the Length OBEX header.
		/// </summary>
		/// <remarks>This property is mandatory, if not set no data will be sent.
		/// If you use the <see cref="ReadFile"/> helper method this value is automatically populated with the size of the file that was read.</remarks>
		public override long ContentLength
		{
			get
			{
				string len = headers["LENGTH"];
				if(len == null || len == string.Empty)
				{
					return 0;
				}
				return long.Parse(len);
			}
			set
			{
				headers["LENGTH"] = value.ToString();
			}
		}
		#endregion

		#region Proxy
		/// <summary>
		/// Not Supported - do not use, this will throw an exception.
		/// </summary>
		public override IWebProxy Proxy
		{
			get
			{
				throw new NotSupportedException();
			}
			set
			{
				throw new NotSupportedException();
			}
		}
		#endregion

        #region Timeout
        private int timeout = 50000;
        /// <summary>
        /// Gets or sets the time-out value for the <see cref="GetResponse"/> method.
        /// </summary>
        /// <value>The number of milliseconds to wait before the request times out.
        /// The default is 50,000 milliseconds (50 seconds).
        /// A value of -1 or 0 represents no time-out.</value>
        public override int Timeout
        {
            get
            {
                return timeout;
            }
            set
            {
                if (value < -1)
                {
                    throw new ArgumentOutOfRangeException("value");
                }
                
                if (value == -1)
                {
                    timeout = 0;
                }
                else
                {
                    timeout = value;
                }
            }
        }
        #endregion

        #region Uri
        private Uri uri;
		/// <summary>
		/// Gets the original Uniform Resource Identifier (URI) of the request. 
		/// </summary>
		/// <remarks>For an ObexPush request the URI will use the "obex://" prefix, followed by the numerical device id in hex format.
		/// The path section of the URI represents the remote filename of the pushed object. Subfolders are not supported. Some devices may only support specific object types e.g. V-Card.</remarks>
		public override Uri RequestUri
		{
			get
			{
				return uri;
			}
		}
		#endregion

		#region DoPut
		private ObexStatusCode DoPut()
		{
			ObexStatusCode status = 0;

			byte[] buffer = new byte[remoteMaxPacket];

            string filename = uri.PathAndQuery;
            if (!uri.UserEscaped) {
#if !(WinCE && V1)
                // This is a NOP if there's no %xx encodings present.
                filename = Uri.UnescapeDataString(filename);
#else
				// HACK ObexWebRequest -- No Unescape method on NETCFv1!!
#endif
            }
            filename = filename.TrimStart(new char[] { '/' });
			int filenameLength = (filename.Length + 1) * 2;

			int packetLength = 6 + filenameLength;

			buffer[0] = (byte)ObexMethod.Put;
			
			
			buffer[3] = (byte)ObexHeader.Name;
			BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)(filenameLength+3))).CopyTo(buffer, 4);
			System.Text.Encoding.BigEndianUnicode.GetBytes(filename).CopyTo(buffer, 6);

			string contentType = headers["TYPE"];
			if(contentType!=null && contentType!="")
			{
                int contentTypeLength = (contentType.Length + 1);// *2;
				buffer[packetLength] = (byte)ObexHeader.Type;
				BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)(contentTypeLength+3))).CopyTo(buffer, packetLength+1);
				System.Text.Encoding.ASCII.GetBytes(contentType).CopyTo(buffer, packetLength+3);
				packetLength += (3+contentTypeLength);
			}
			if(this.ContentLength!=0)
			{
				buffer[packetLength] = (byte)ObexHeader.Length;
				BitConverter.GetBytes(IPAddress.HostToNetworkOrder(Convert.ToInt32(this.ContentLength))).CopyTo(buffer, packetLength+1);
				packetLength += 5;
			}

			//write the final packet size
			BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)packetLength)).CopyTo(buffer, 1);

			//send packet with name header
            ns.Write(buffer, 0, packetLength);

			if (CheckResponse(ref status))
			{

				int totalBytes = 0;
				
				int thisRequest = 0;
				
				byte[] requestBuffer = requestStream.GetBuffer();

				//we really want the content length, but if not available send the whole buffer
				if(this.ContentLength > 0)
				{
					totalBytes = (int)this.ContentLength;
				}
				else
				{
					totalBytes = requestBuffer.Length;
				}

				MemoryStream readBuffer = new MemoryStream(requestBuffer);

				while (totalBytes > 0)
				{
					if(totalBytes <= (remoteMaxPacket - 6))
					{
						thisRequest = totalBytes;

						totalBytes = 0;
						buffer[0] = (byte)ObexMethod.PutFinal;
						buffer[3] = (byte)ObexHeader.EndOfBody;

					}
					else
					{
						thisRequest = remoteMaxPacket - 6;
						//decrement byte count
						totalBytes -= thisRequest;
						buffer[0] = (byte)ObexMethod.Put;
						buffer[3] = (byte)ObexHeader.Body;
					}

					int readBytes = readBuffer.Read(buffer, 6, thisRequest);
					
					BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)(readBytes+3))).CopyTo(buffer, 4);
			
					BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)(readBytes + 6))).CopyTo(buffer, 1);
					
                    ns.Write(buffer, 0, readBytes + 6);

					if (!CheckResponse(ref status))
					{
						return status;
					}
				}
			}

			return status;

		}
		#endregion

		#region DoGet
		private ObexStatusCode DoGet(MemoryStream ms, WebHeaderCollection headers)
		{
            ObexStatusCode sc;

			byte[] buffer = new byte[remoteMaxPacket];

			buffer[0] = ((byte)ObexMethod.Get) | 0x80;
			int bufferlen = 3;

			//build the packet based on the available headers

			//connectionid (must be first header)
			if(connectionId != 0)
			{
                buffer[bufferlen] = (byte)ObexHeader.ConnectionID;
				BitConverter.GetBytes(IPAddress.HostToNetworkOrder(connectionId)).CopyTo(buffer, bufferlen+1);
				
				bufferlen += 5;
			}

            //name
			string filename = uri.PathAndQuery.TrimStart(new char[]{'/'});
			if(filename.Length>0)
			{
				int filenameLength = filename.Length * 2;
				buffer[bufferlen] = (byte)ObexHeader.Name;
				int filenameheaderlen = IPAddress.HostToNetworkOrder((short)(filenameLength + 3));
				BitConverter.GetBytes(filenameheaderlen).CopyTo(buffer, bufferlen+1);
				System.Text.Encoding.BigEndianUnicode.GetBytes(filename).CopyTo(buffer, bufferlen+3);

				bufferlen += filenameLength+3;
			}

			//content type
			string type = this.headers["TYPE"];
			if (type != null)
			{
				buffer[bufferlen] = (byte)ObexHeader.Type;
				int typeheaderlen = IPAddress.HostToNetworkOrder((short)((type.Length + 1) + 3));
				BitConverter.GetBytes(typeheaderlen).CopyTo(buffer, bufferlen+1);
				System.Text.Encoding.ASCII.GetBytes(type).CopyTo(buffer, bufferlen+3);

				bufferlen += type.Length+4;
			}
			
			//write total packet size
			BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)bufferlen)).CopyTo(buffer, 1);
			
			//send packet with name header
			ns.Write(buffer, 0, bufferlen);

            //response
            
            do
            {
                int bytesread = ns.Read(buffer, 0, 3);
                //get code
                sc = (ObexStatusCode)buffer[0];
                //get length
                short len = (short)IPAddress.NetworkToHostOrder(BitConverter.ToInt16(buffer, 1));
                //read all of packet
                while (bytesread < len)
                {
                    bytesread += ns.Read(buffer, bytesread, len - bytesread);
                }
                ObexParser.ParseHeaders(buffer, ref remoteMaxPacket, ms, headers);

                if ((sc & ObexStatusCode.Final) != ObexStatusCode.Final)
                {
                    //send continue response
                    buffer[0] = (byte)ObexStatusCode.Continue;
                    BitConverter.GetBytes(IPAddress.HostToNetworkOrder((short)3)).CopyTo(buffer, 1);
                    //send packet
                    ns.Write(buffer, 0, 3);
                }
            }
            while (((byte)sc & (byte)ObexStatusCode.Final) != (byte)ObexStatusCode.Final);

            return sc;
		}
		#endregion

		#region Check Response
		private bool CheckResponse(ref ObexStatusCode status)
		{
			byte[] receiveBuffer = new byte[3];
            ns.Read(receiveBuffer, 0, receiveBuffer.Length);

			status = (ObexStatusCode)receiveBuffer[0];

			switch(status)
			{
                case ObexStatusCode.Final | ObexStatusCode.OK:
                case ObexStatusCode.OK:
				case ObexStatusCode.Final | ObexStatusCode.Continue:
				case ObexStatusCode.Continue:
					//get length
					short len = (short)(IPAddress.NetworkToHostOrder(BitConverter.ToInt16(receiveBuffer, 1)) - 3);

					if (len > 0)
					{
						byte[] receivePacket2 = new byte[len];
                        ns.Read(receivePacket2, 0, len);

						remoteMaxPacket = unchecked((ushort)IPAddress.NetworkToHostOrder(BitConverter.ToInt16(receivePacket2, 2)));
					}

					return true;
				default:
					return false;
			}
			
			//handle errors please!
		}
		#endregion

		#region Disconnect
		private void Disconnect()
		{
            if (ns != null)
            {
                ObexStatusCode status = 0;

                short disconnectPacketSize = 3;
                byte[] disconnectPacket = new byte[8];
                disconnectPacket[0] = (byte)ObexMethod.Disconnect;

                //add connectionid header
                if (connectionId != 0)
                {
                    disconnectPacket[3] = (byte)ObexHeader.ConnectionID;
                    BitConverter.GetBytes(IPAddress.HostToNetworkOrder(connectionId)).CopyTo(disconnectPacket, 4);
                    disconnectPacketSize += 5;
                }

                //set packet size
                BitConverter.GetBytes(IPAddress.HostToNetworkOrder(disconnectPacketSize)).CopyTo(disconnectPacket, 1);

                ns.Write(disconnectPacket, 0, disconnectPacketSize);

                CheckResponse(ref status);

                ns.Close();
            }
		}
		#endregion

		#region Get Request Stream
		/// <summary>
		/// Gets a <see cref="System.IO.Stream"/> object to use to write request data.
		/// </summary>
		/// <returns></returns>
		public override System.IO.Stream GetRequestStream()
		{
			return requestStream;
		}
		#endregion

		#region Read File
		/// <summary>
		/// Reads the contents of the specified file to the request stream.
		/// </summary>
		/// <param name="fileName">The filename (including the path) from which to read.</param>
		/// <remarks>Provides an easy equivalent to manually writing the file contents to the request stream.</remarks>
		public void ReadFile(string fileName)
		{
			FileStream fs = File.OpenRead(fileName);
			long len = 0;
			//read in 1k chunks
			byte[] buffer = new byte[1024];
			int readBytes;
			do
			{
				readBytes = fs.Read(buffer, 0, buffer.Length);
				len += readBytes;
				requestStream.Write(buffer, 0, readBytes);
			}while (readBytes > 0);

			fs.Close();
			requestStream.Close();

			//write content length
			this.ContentLength = len;
		}
		#endregion

		#region Get Response
		/// <summary>
		/// Returns the OBEX server response.
		/// </summary>
        /// -
        /// <returns>An <see cref="T:InTheHand.Net.ObexWebResponse"/>.</returns>
        /// -
        /// <exception cref="System.Net.WebException">
        /// An error occurred, with the error that occured being stored in the 
        /// <see cref="P:System.Exception.InnerException"/> property.  If the error 
        /// occurred in the connect phase then the <see cref="P:System.Net.WebException.Status"/>
        /// property will have value <see cref="F:System.Net.WebExceptionStatus.ConnectFailure"/>,
        /// and in the operation phase on the desktop CLR it will have value
        /// <see cref="F:System.Net.WebExceptionStatus.UnknownError"/>
        /// </exception>
        public override WebResponse GetResponse()
        {
            ObexStatusCode status;
            MemoryStream ms = new MemoryStream();
            WebHeaderCollection responseHeaders = new WebHeaderCollection();
            //try connecting if not already
            try
            {
                status = Connect();
            }
            catch (SocketException se)
            {
                throw new WebException("Connect failed.", se, WebExceptionStatus.ConnectFailure, null);
            }

            try
            {
                switch (this.method)
                {
                    case ObexMethod.Put:
                    case ObexMethod.PutFinal:
                        status = DoPut();
                        break;
                    case ObexMethod.Get:
                        status = DoGet(ms, responseHeaders);
                        ms.Seek(0, SeekOrigin.Begin);
                        break;
                    default:
                        throw new WebException("Unsupported Method.", new InvalidOperationException(), WebExceptionStatus.ProtocolError, null);
                }
            }
            catch (Exception ex)
            {
                
                    throw new WebException("Operation failed.", ex
#if ! WinCE
                        // UnknownError member not supported on CE unfortunately.
                        , WebExceptionStatus.UnknownError, null
#endif
);

            }
            finally
            {
                Disconnect();
            }

            return new ObexWebResponse(ms, responseHeaders, status);
        }
		#endregion
		
	}//class
}


