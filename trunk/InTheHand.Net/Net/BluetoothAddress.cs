// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.BluetoothAddress
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;

namespace InTheHand.Net
{
	/// <summary>
	/// Represents a Bluetooth device address.
	/// </summary>
#if !WinCE
    [Serializable]
#endif
	public sealed class BluetoothAddress : IComparable, IFormattable
#if !WinCE
        , System.Xml.Serialization.IXmlSerializable //could be supported on NETCFv2
        , System.Runtime.Serialization.ISerializable
#endif
	{
        [NonSerialized] // Custom serialized in text format, to avoid any endian or length issues etc.
		private byte[] data;

        #region Constructor
        internal BluetoothAddress()
		{
			data = new byte[8];
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="BluetoothAddress"/> class with the specified address.
		/// </summary>
		/// <param name="address"><see cref="Int64"/> representation of the address.</param>
		public BluetoothAddress(long address) : this()
		{
			//copy value to array
			BitConverter.GetBytes(address).CopyTo(data,0);
		}

		/// <summary>
		/// Initializes a new instance of the <see cref="BluetoothAddress"/> class with the specified address.
		/// </summary>
        /// -
        /// <remarks>
        /// <para>Note: The address should be supplied in little-endian order on the
        /// current Windows platform (which is little-endian).
        /// For forward compatibility it would be safer to use the 
        /// <see cref="M:InTheHand.Net.BluetoothAddress.Parse(System.String)"/> method, 
        /// which will be correct for all platforms.
        /// </para>
        /// </remarks>
        /// -
		/// <param name="address">Address as 6 byte array.</param>
        /// <exception cref="ArgumentNullException">address passed was <see langword="null"/>.</exception>
        /// <exception cref="ArgumentException">address passed was not a 6 byte array.</exception>
		public BluetoothAddress(byte[] address) : this()
		{
            if (address == null) {
                throw new ArgumentNullException("address");
            }
			if(address.Length == 6 || address.Length == 8)
			{
				Buffer.BlockCopy(address, 0, data, 0, 6);
			}
			else
			{
				throw new ArgumentException("address");
			}
        }
        #endregion

        #region Parse
        /// <summary>
        /// Converts the string representation of an address to it's <see cref="BluetoothAddress"/> equivalent.
        /// A return value indicates whether the operation succeeded.
        /// </summary>
        /// <param name="s">A string containing an address to convert.</param>
        /// <param name="result">When this method returns, contains the <see cref="BluetoothAddress"/> equivalent to the address contained in s, if the conversion succeeded, or null (Nothing in Visual Basic) if the conversion failed.
        /// The conversion fails if the s parameter is null or is not of the correct format.</param>
        /// <returns>true if s is a valid Bluetooth address; otherwise, false.</returns>
        public static bool TryParse(string s, out BluetoothAddress result)
        {

            try
            {
                result = Parse(s);
                return true;
            }
            catch
            {
                result = null;
                return false;
            }
        }

        /// <summary>
		/// Converts the string representation of a Bluetooth address to a new <see cref="BluetoothAddress"/> instance.
		/// </summary>
        /// <param name="bluetoothString">A string containing an address to convert.</param>
		/// <returns>New <see cref="BluetoothAddress"/> instance.</returns>
		/// <remarks>Address must be specified in hex format optionally separated by the colon or period character e.g. 000000000000, 00:00:00:00:00:00 or 00.00.00.00.00.00.</remarks>
        /// <exception cref="ArgumentNullException">bluetoothString is null.</exception>
        /// <exception cref="FormatException">bluetoothString is not a valid Bluetooth address.</exception>
        public static BluetoothAddress Parse(string bluetoothString)
		{
            if (bluetoothString == null)
			{
                throw new ArgumentNullException("bluetoothString");
			}

			BluetoothAddress ba;

            if (bluetoothString.IndexOf(":") > -1)
			{
				//assume address in standard hex format 00:00:00:00:00:00

                //check length
                if (bluetoothString.Length != 17)
                {
                    throw new FormatException("bluetoothString is not a valid Bluetooth address.");
                }

				ba = new BluetoothAddress();
				byte[] babytes = ba.ToByteArray();
				//split on colons
                string[] sbytes = bluetoothString.Split(':');
				for(int ibyte = 0; ibyte < 6; ibyte++)
				{
					//parse hex byte in reverse order
					babytes[ibyte] = byte.Parse(sbytes[5 - ibyte],System.Globalization.NumberStyles.HexNumber);
				}
			}
            else if (bluetoothString.IndexOf(".") > -1)
			{
				//assume address in uri hex format 00.00.00.00.00.00
                //check length
                if (bluetoothString.Length != 17)
                {
                    throw new FormatException("bluetoothString is not a valid Bluetooth address.");
                }

				ba = new BluetoothAddress();
				byte[] babytes = ba.ToByteArray();
				//split on periods
                string[] sbytes = bluetoothString.Split('.');
				for(int ibyte = 0; ibyte < 6; ibyte++)
				{
					//parse hex byte in reverse order
					babytes[ibyte] = byte.Parse(sbytes[5 - ibyte],System.Globalization.NumberStyles.HexNumber);
				}
			}
			else
			{
				//assume specified as long integer
                if ((bluetoothString.Length < 12) | (bluetoothString.Length > 16))
                {
                    throw new FormatException("bluetoothString is not a valid Bluetooth address.");
                }

                ba = new BluetoothAddress(long.Parse(bluetoothString, System.Globalization.NumberStyles.HexNumber));
			}

			return ba;
        }
        #endregion

        #region SAP
        /// <summary>
        /// Significant address part.
        /// </summary>
        [CLSCompliant(false)]
        public uint Sap
        {
            get
            {
                return BitConverter.ToUInt32(data, 0);
            }
        }
        #endregion
        #region LAP
        #endregion
        #region UAP
        #endregion
        #region NAP
        /// <summary>
        /// Non-significant address part.
        /// </summary>
        [CLSCompliant(false)]
        public ushort Nap
        {
            get
            {
                return BitConverter.ToUInt16(data, 4);
            }
        }
        #endregion

        #region To Byte Array
        /// <summary>
		/// Returns the internal byte array.
		/// </summary>
		/// <returns></returns>
		public byte[] ToByteArray()
		{
			return data;
        }
        #endregion

        #region ToInt64
        /// <summary>
		/// Returns the Bluetooth address as a long integer.
		/// </summary>
		/// <returns></returns>
		public long ToInt64()
		{
			return BitConverter.ToInt64(data, 0);
        }
        #endregion

        #region Equals
        /// <summary>
		/// Compares two <see cref="BluetoothAddress"/> instances for equality.
		/// </summary>
		/// <param name="obj"></param>
		/// <returns></returns>
		public override bool Equals(object obj)
		{
			BluetoothAddress bta = obj as BluetoothAddress;
			
			if(bta!=null)
			{
				return (this==bta);	
			}

			return base.Equals (obj);
        }
        #endregion

        #region Get Hash Code
        /// <summary>
		/// Returns the hash code for this instance.
		/// </summary>
		/// <returns></returns>
		public override int GetHashCode()
		{
			return this.ToInt64().GetHashCode();
        }
        #endregion

        #region Operators
        /// <summary>
		/// Returns an indication whether the values of two specified <see cref="BluetoothAddress"/> objects are equal.<para><b>New in v1.5</b></para>
		/// </summary>
		/// <param name="x"></param>
		/// <param name="y"></param>
		/// <returns></returns>
		public static bool operator ==(BluetoothAddress x, BluetoothAddress y) 
		{
			if(((object)x == null) && ((object)y == null))
			{
				return true;
			}

			if(((object)x != null) && ((object)y != null))
			{
				if(x.ToInt64()==y.ToInt64())
				{
					return true;
				}
			}

			return false;
        }
        

        /// <summary>
		/// Returns an indication whether the values of two specified <see cref="BluetoothAddress"/> objects are not equal.
		/// </summary>
		/// <param name="x"></param>
		/// <param name="y"></param>
		/// <returns></returns>
		public static bool operator !=(BluetoothAddress x, BluetoothAddress y) 
		{
			return !(x == y);
        }
        #endregion

        #region To String
        /// <summary>
		/// Converts the address to its equivalent string representation.
		/// </summary>
		/// <returns>The string representation of this instance.</returns>
		/// <remarks>The default return format is without a separator character 
        /// - use the <see cref="M:InTheHand.Net.BluetoothAddress.ToString(string)"/>
        /// overload for more formatting options.</remarks>
		public override string ToString()
		{
			return this.ToString("N");
		}

		/// <summary>
		/// Returns a <see cref="String"/> representation of the value of this <see cref="BluetoothAddress"/> instance, according to the provided format specifier.
		/// </summary>
		/// <param name="format">A single format specifier that indicates how to format the value of this address.
        /// The format parameter can be "N", "C", or "P".
        /// If format is null or the empty string (""), "D" is used.</param>
		/// <returns>A <see cref="String"/> representation of the value of this <see cref="BluetoothAddress"/>.</returns>
		/// <remarks><list type="table">
		/// <listheader><term>Specifier</term><term>Format of Return Value </term></listheader>
		/// <item><term>N</term><term>12 digits: <para>XXXXXXXXXXXX</para></term></item>
		/// <item><term>C</term><term>12 digits separated by colons: <para>XX:XX:XX:XX:XX:XX</para></term></item>
		/// <item><term>P</term><term>12 digits separated by periods: <para>XX.XX.XX.XX.XX.XX</para></term></item>
		/// </list></remarks>
		public string ToString(string format)
		{
			string separator;

			if(format==null | format==string.Empty)
			{
				separator = string.Empty;
			}
			else
			{

				switch(format.ToUpper())
				{
                    case "8":
					case "N":
						separator = string.Empty;
						break;
					case "C":
						separator = ":";
						break;
					case "P":
						separator = ".";
						break;
					default:
						throw new FormatException("Invalid format specified - must be either \"N\", \"C\", \"P\", \"\" or null.");
				}
			}

			System.Text.StringBuilder result = new System.Text.StringBuilder(18);

            if (format == "8")
            {
                result.Append(data[7].ToString("X2") + separator);
                result.Append(data[6].ToString("X2") + separator);
            }

			result.Append(data[5].ToString("X2") + separator);
			result.Append(data[4].ToString("X2") + separator);
			result.Append(data[3].ToString("X2") + separator);
			result.Append(data[2].ToString("X2") + separator);
			result.Append(data[1].ToString("X2") + separator);
			result.Append(data[0].ToString("X2"));

			return result.ToString();
        }
        #endregion

        #region Static
        /// <summary>
		/// Provides a null Bluetooth address.
		/// </summary>
		public static readonly BluetoothAddress None = new BluetoothAddress();

		/// <summary>
		/// 
		/// </summary>
		internal const int IacFirst = 0x9E8B00;

		/// <summary>
		/// 
		/// </summary>
		internal const int IacLast = 0x9E8B3f;

		/// <summary>
        /// Limited Inquiry Access Code.
		/// </summary>
		public const int Liac = 0x9E8B00;

		/// <summary>
        /// General Inquire Access Code.
        /// The default inquiry code which is used to discover all devices in range.
		/// </summary>
		public const int Giac = 0x9E8B33;

        #endregion

        #region IComparable Members

        int IComparable.CompareTo(object obj)
        {
            BluetoothAddress bta = obj as BluetoothAddress;

            if (bta != null)
            {
                return this.ToInt64().CompareTo(bta.ToInt64());
            }

            return -1;
        }

        #endregion

        #region IFormattable Members
        /// <summary>
        /// Returns a <see cref="String"/> representation of the value of this 
        /// <see cref="BluetoothAddress"/> instance, according to the provided format specifier.
        /// </summary>
        /// -
        /// <param name="format">A single format specifier that indicates how to format the value of this Address.
        /// The format parameter can be "N", "C", or "P".
        /// If format is null or the empty string (""), "D" is used.
        /// </param>
        /// <param name="formatProvider">Ignored.
        /// </param>
        /// -
        /// <returns>A <see cref="String"/> representation of the value of this
        /// <see cref="BluetoothAddress"/>.
        /// </returns>
        /// -
        /// <remarks>See <see cref="M:InTheHand.Net.BluetoothAddress.ToString(System.String)"/>
        /// for the possible format strings and their output.
        /// </remarks>
        public string ToString(string format, IFormatProvider formatProvider)
        {
            //for now just wrap existing ToString method
            return ToString(format);
        }

        #endregion

        #region IXmlSerializable Members
#if !WinCE
        System.Xml.Schema.XmlSchema System.Xml.Serialization.IXmlSerializable.GetSchema()
        {
            return null;
        }

        void System.Xml.Serialization.IXmlSerializable.ReadXml(System.Xml.XmlReader reader)
        {
            String text = reader.ReadElementContentAsString();
            BluetoothAddress tmpAddr = BluetoothAddress.Parse(text);
            this.data = tmpAddr.data;
        }

        void System.Xml.Serialization.IXmlSerializable.WriteXml(System.Xml.XmlWriter writer)
        {
            // Serialize the address -- in text format, to avoid any endian or length 
            // issues etc.
            writer.WriteString(this.ToString("N"));
        }
#endif
        #endregion

        #region ISerializable Members
#if !WinCE
        [System.Security.Permissions.SecurityPermission(System.Security.Permissions.SecurityAction.LinkDemand,
            SerializationFormatter = true)]
        private BluetoothAddress(System.Runtime.Serialization.SerializationInfo info, System.Runtime.Serialization.StreamingContext context)
        {
            String text = info.GetString("dataString");
            BluetoothAddress tmpAddr = BluetoothAddress.Parse(text);
            this.data = tmpAddr.data;
        }

        [System.Security.Permissions.SecurityPermission(System.Security.Permissions.SecurityAction.LinkDemand,
            SerializationFormatter = true)]
        void System.Runtime.Serialization.ISerializable.GetObjectData(System.Runtime.Serialization.SerializationInfo info, System.Runtime.Serialization.StreamingContext context)
        {
            // Serialize the address -- in text format, to avoid any endian or length 
            // issues etc.
            info.AddValue("dataString", this.ToString("N"));
        }
#endif
        #endregion
    }
}
