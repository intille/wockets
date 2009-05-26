// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.HardwareStatus
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;

namespace InTheHand.Net.Bluetooth
{
	/// <summary>
	/// Specifies the current status of the Bluetooth hardware.
	/// </summary>
	public enum HardwareStatus : int
	{
		/// <summary>
		/// Status cannot be determined.
		/// </summary>
		Unknown			= 0,
		/// <summary>
		/// Bluetooth radio not present.
		/// </summary>
		NotPresent		= 1,
		/// <summary>
		/// Bluetooth radio is in the process of starting up.
		/// </summary>
		Initializing	= 2,
		/// <summary>
		/// Bluetooth radio is active.
		/// </summary>
		Running			= 3,
		/// <summary>
		/// Bluetooth radio is in the process of shutting down.
		/// </summary>
		Shutdown		= 4,
		/// <summary>
		/// Bluetooth radio is in an error state.
		/// </summary>
		Error			= 5,
	}
}
