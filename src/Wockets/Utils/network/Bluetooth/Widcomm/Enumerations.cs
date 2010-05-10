//==========================================================================================
//
//		namespace OpenNETCF.IO.Ports.Enumerations
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
	/// <summary>
	/// Specifies the number of stop bits used on the <see cref="SerialPort"/> object.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public enum StopBits {
		/// <summary>
		/// One stop bit is used
		/// </summary>
		One = 1,

		/// <summary>
		/// Three stop bits are used.
		/// </summary>
		OnePointFive = 3,

		/// <summary>
		/// Two stop bits are used.
		/// </summary>
		Two = 2
	}
 
	/// <summary>
	/// Specifies the control protocol used in establishing a serial port communication for a <see cref="SerialPort"/> object.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public enum Handshake {
		/// <summary>
		/// No control is used for the handshake.
		/// </summary>
		None = 0,

		/// <summary>
		/// Request-to-Send (RTS) hardware flow control is used. RTS is used to signal that data is available for transmission.
		/// </summary>
		RequestToSend = 2,

		/// <summary>
		/// Both the Request-to-Send (RTS) hardware control and the XON/XOFF software controls are used.
		/// </summary>
		RequestToSendXOnXOff = 3,

		/// <summary>
		/// The XON/XOFF software control protocol is used. XOFF is a software control sent to stop the transmission of data and the XON control is sent to resume the transmission. These controls are used instead of Request to Send (RTS) and Clear to Send (CTS) hardware controls.
		/// </summary>
		XOnXOff = 1
	}
 
	/// <summary>
	/// Specifies the parity bit for a <see cref="SerialPort"/> object.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public enum Parity {
		/// <summary>
		/// Sets the parity bit so that the count of bits set is an even number.
		/// </summary>
		Even = 2,

		/// <summary>
		/// Leaves the parity bit set to 1.
		/// </summary>
		Mark = 3,

		/// <summary>
		/// No parity check occurs.
		/// </summary>
		None = 0,

		/// <summary>
		/// Sets the parity bit so that the count of bits set is an odd number.
		/// </summary>
		Odd = 1,

		/// <summary>
		/// Leaves the parity bit set to 0.
		/// </summary>
		Space = 4
	}
 
	/// <summary>
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	public enum SerialData {
		Chars = 1,
		Eof = 2
	}
 
	/// <summary>
	/// Specifies errors that occur on the <see cref="SerialPort"/> object.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	/// <remarks>This enumeration is used with the <see cref="SerialPort.ErrorEvent"/> event.</remarks>
	public enum SerialError {
		/// <summary>
		/// The hardware detected a framing error.
		/// </summary>
		Frame = 8,
		/// <summary>
		/// A character-buffer overrun has occurred.
		/// The next character is lost.
		/// </summary>
		Overrun = 2,
		/// <summary>
		/// An input buffer overflow has occurred.
		/// There is either no room in the input buffer, or a character was received after the end-of-file (EOF) character.
		/// </summary>
		RXOver = 1,
		/// <summary>
		/// The hardware detected a parity error.
		/// </summary>
		RXParity = 4,
		/// <summary>
		/// The application tried to transmit a character, but the output buffer was full.
		/// </summary>
		TXFull = 0x100
	}
 
	/// <summary>
	/// Specifies the type of change that occurred on the <see cref="SerialPort"/> object.
	/// <para><b>New in v1.3</b></para>
	/// </summary>
	/// <remarks>This enumeration is used with the <see cref="SerialPort.PinChangedEvent"/> event.</remarks>
	public enum SerialPinChange {
		/// <summary>
		/// A break was detected on input.
		/// </summary>
		Break = 0x40,
		/// <summary>
		/// The Receive Line Signal Detect (RLSD) signal changed state.
		/// </summary>
		CDChanged = 0x20,
		/// <summary>
		/// The Clear to Send (CTS) signal changed state.
		/// </summary>
		CtsChanged = 8,
		/// <summary>
		/// The Data Set Ready (DSR) signal changed state.
		/// </summary>
		DsrChanged = 0x10,
		/// <summary>
		/// A ring indicator was detected.
		/// </summary>
		Ring = 0x100
	}
}
