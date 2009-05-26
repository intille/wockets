// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.RadioMode
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

namespace InTheHand.Net.Bluetooth
{
	/// <summary>
	/// Determine all the possible modes of operation of the Bluetooth radio.
	/// </summary>
	public enum RadioMode
	{
		/// <summary>
		/// Bluetooth is disabled on the device.
		/// </summary>
		PowerOff,
		/// <summary>
		/// Bluetooth is connectable but your device cannot be discovered by other devices.
		/// </summary>
		Connectable,
		/// <summary>
		/// Bluetooth is activated and fully discoverable.
		/// </summary>
		Discoverable,
	}
}
