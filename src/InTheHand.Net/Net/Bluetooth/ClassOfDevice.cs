// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.ClassOfDevice
// 
// Copyright (c) 2003-2006 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using InTheHand.Net.Bluetooth;

namespace InTheHand.Net.Bluetooth
{
    /// <summary>
    /// Describes the device and service capabilities of a device.
    /// </summary>
    /// -
    /// <remarks>
    /// <para>Is returned by the properties
    /// <see cref="P:InTheHand.Net.Sockets.BluetoothDeviceInfo.ClassOfDevice">BluetoothDeviceInfo.ClassOfDevice</see>
    /// and
    /// <see cref="P:InTheHand.Net.Bluetooth.BluetoothRadio.ClassOfDevice">BluetoothRadio.ClassOfDevice</see>.
    /// </para>
    /// </remarks>
    public class ClassOfDevice
    {
        private uint cod;

        internal ClassOfDevice(uint cod)
        {
            this.cod = cod;
        }

        /*
        /// <summary>
        /// 
        /// </summary>
        /// <param name="device"></param>
        public ClassOfDevice(DeviceClass device)
        {
            this.cod = (uint)device;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="device"></param>
        /// <param name="service"></param>
        public ClassOfDevice(DeviceClass device, ServiceClass service)
        {
            this.cod = (uint)device | ((uint)service << 13);
        }*/

        //experimental
        /*internal ClassOfDevice(Sockets.IrDAHints hints)
        {
            switch (hints)
            {
                
                case InTheHand.Net.Sockets.IrDAHints.FileServer:
                    cod | ((uint)ServiceClass.Information << 13);
                
                case InTheHand.Net.Sockets.IrDAHints.Obex:
                    cod | ((uint)ServiceClass.ObjectTransfer << 13);

                case InTheHand.Net.Sockets.IrDAHints.PdaAndPalmtop:
                    cod | DeviceClass.PdaComputer;
                    break;
                case InTheHand.Net.Sockets.IrDAHints.Computer:
                    cod | DeviceClass.Computer;
                    break;
                case InTheHand.Net.Sockets.IrDAHints.Printer:
                    cod | DeviceClass.ImagingPrinter;
                    break;
                case InTheHand.Net.Sockets.IrDAHints.Fax:
                case InTheHand.Net.Sockets.IrDAHints.Modem:
                case InTheHand.Net.Sockets.IrDAHints.Telephony:
                    cod | DeviceClass.Phone;
                    break;
                case InTheHand.Net.Sockets.IrDAHints.LanAccess:
                    cod | DeviceClass.AccessPointAvailable;
                    break;
            }
        }*/

        /// <summary>
        /// Returns the device type.
        /// </summary>
        public DeviceClass Device
        {
            get
            {
                return (DeviceClass)(cod & 0x001ffc);
            }
        }

        /// <summary>
        /// Returns the major device type.
        /// </summary>
        public DeviceClass MajorDevice
        {
            get
            {
                return (DeviceClass)(cod & 0x001f00);
            }
        }

        /// <summary>
        /// Returns supported service types.
        /// </summary>
        public ServiceClass Service
        {
            get
            {
                return (ServiceClass)(cod >> 13);
            }
        }

        /// <summary>
        /// Gets the numerical value.
        /// </summary>
        /// <seealso cref="P:InTheHand.Net.Bluetooth.ClassOfDevice.ValueAsInt32"/>
        [CLSCompliant(false)]//use ValueAsInt32
        public uint Value
        {
            get { return cod; }
        }

        /// <summary>
        /// Gets the numerical value, suitable for CLS Compliance.
        /// </summary>
        /// <seealso cref="P:InTheHand.Net.Bluetooth.ClassOfDevice.Value"/>
        public int ValueAsInt32
        {
            get { return unchecked((int)cod); }
        }

        /*
        /// <summary>
        /// 
        /// </summary>
        public byte FormatType
        {
            get
            {
                return (byte)(cod & 0x03);
            }
        }*/

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        public override int GetHashCode()
        {
            return Convert.ToInt32(cod);
        }

        /// <summary>
        /// Returns the numerical value represented in a hexadecimal.
        /// </summary>
        public override string ToString()
        {
            return cod.ToString("X");
        }
    }
}
