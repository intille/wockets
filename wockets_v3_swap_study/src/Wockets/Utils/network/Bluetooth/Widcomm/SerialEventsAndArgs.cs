//==========================================================================================
//
//		namespace OpenNETCF.IO.Ports.SerialEventsAndArgs
//		Copyright (c) 2005, OpenNETCF.org
//
//		This library is free software; you can redistribute it and/or modify it under 
//		the terms of the OpenNETCF.org Shared Source License.
//
//		This library is distributed in the hope that it will be useful, but 
//		WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
//		FITNESS FOR A PARTICULAR PURPOSE. See the OpenNETCF.org Shared Source License 
//		for more details.
//
//		You should have received a copy of the OpenNETCF.org Shared Source License 
//		along with this library; if not, email licensing@opennetcf.org to request a copy.
//
//		If you wish to contact the OpenNETCF Advisory Board to discuss licensing, please 
//		email licensing@opennetcf.org.
//
//		For general enquiries, email enquiries@opennetcf.org or visit our website at:
//		http://www.opennetcf.org
//
//==========================================================================================

using System;

namespace OpenNETCF.IO.Ports {
	#region Delegates
	/// <summary>
	/// Represents the method that will handle the OpenNETCF.IO.Ports.SerialPort.PinChangedEvent event of a OpenNETCF.IO.Ports.SerialPort object.
	/// </summary>
	public delegate void SerialPinChangedEventHandler(object sender, SerialPinChangedEventArgs e);

	public delegate void SerialErrorReceivedEventHandler(object sender, SerialErrorReceivedEventArgs e);

	public delegate void SerialDataReceivedEventHandler(object sender, SerialDataReceivedEventArgs e);
	#endregion

	#region EventArgs
	/// <summary>
	/// Specifies the arguments sent to the <see cref="SerialPort.PinChanged"/> event.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public class SerialPinChangedEventArgs : EventArgs {
		private SerialPinChange mPinChanged;

		internal SerialPinChangedEventArgs(SerialPinChange eventCode){
			mPinChanged = eventCode;
		}

		/// <summary>
		/// Gets or sets the event type.
		/// <return>A value from the <see cref="SerialPinChange"/> enumeration.</return>
		/// </summary>
		public SerialPinChange EventType { 
			get{
				return mPinChanged;
			} 
		}

	}
 
	/// <summary>
	/// Specifies the arguments sent to the <see cref="SerialPort.ErrorReceived"/> event.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public class SerialErrorReceivedEventArgs : EventArgs 
	{
		private SerialError mErrorType;

		internal SerialErrorReceivedEventArgs(SerialError eventCode){
			mErrorType = eventCode;
		}

		/// <summary>
		/// Gets or sets the event type.
		/// </summary>
		public SerialError EventType {
			get{
				return mErrorType;
			} 
		}
	}
 
	/// <summary>
	/// Specifies the arguments sent to the <see cref="SerialPort.DataReceived"/> event
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public class SerialDataReceivedEventArgs : EventArgs 
	{
		internal SerialData mReceiveType;

		internal SerialDataReceivedEventArgs(SerialData eventCode){
			mReceiveType = eventCode;
		}

		/// <summary>
		/// Gets or sets the event type.
		/// </summary>
		public SerialData EventType {
			get{
				return mReceiveType;
			} 
		}

	}
	#endregion
}
