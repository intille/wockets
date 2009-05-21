// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Sockets.BluetoothDeviceInfo
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Net;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using InTheHand.Net.Bluetooth;
using Microsoft.Win32;
#if WinCE
#if V1
using InTheHand.Runtime.InteropServices;
#else
using Marshal32 = System.Runtime.InteropServices.Marshal;
#endif
#endif

namespace InTheHand.Net.Sockets
{
	/// <summary>
	/// Provides information about an available device obtained by the client during device discovery.
	/// </summary>
	public class BluetoothDeviceInfo : IComparable
	{
		private BLUETOOTH_DEVICE_INFO deviceInfo;

#if WinXP
        private bool valid = false;
#endif

        #region Constructor
        /// <overloads>
        /// Initializes an instance of the <see cref="T:BluetoothDeviceInfo"/> class.
        /// </overloads>
        /// -
        /// <summary>
        /// Initializes an instance of the <see cref="T:BluetoothDeviceInfo"/> class with the given native structure.
        /// </summary>
        public BluetoothDeviceInfo(IntPtr pDevice)
		{
            deviceInfo = new BLUETOOTH_DEVICE_INFO(0);
            Marshal.PtrToStructure(pDevice, deviceInfo);
#if WinXP
            valid = true;
#endif
		}

        internal BluetoothDeviceInfo(BLUETOOTH_DEVICE_INFO device)
        {
            deviceInfo = device;
#if WinXP
            valid = true;
#endif
        }

        /// <summary>
        /// Initializes an instance of the <see cref="T:BluetoothDeviceInfo"/> class 
        /// for the device with the given address.
        /// </summary>
		public BluetoothDeviceInfo(BluetoothAddress address)
		{
            if (address == null) {
                throw new ArgumentNullException("address");
            }
            this.deviceInfo = new BLUETOOTH_DEVICE_INFO(address.ToInt64());
#if WinXP
            GetDeviceInfo();
            valid = true;
#endif
		}
		
#if WinCE
        //use to populate devices from discovery
        internal BluetoothDeviceInfo(BluetoothAddress address, uint classOfDevice) : this(address)
        {
            this.deviceInfo.ulClassofDevice = classOfDevice;
        }
        //used when retrieving bonded devices from the registry
		internal BluetoothDeviceInfo(BluetoothAddress address, string name, uint classOfDevice, bool authenticated) : this(address, classOfDevice)
		{
			this.deviceInfo.szName = name;
            //only for CE
            this.deviceInfo.fAuthenticated = authenticated;
            this.deviceInfo.fRemembered = authenticated;
        }
#endif
        #endregion

        #region Get Device Info
#if WinXP
        private void GetDeviceInfo()
        {
            if (!valid)
            {

                int ret = NativeMethods.BluetoothGetDeviceInfo(IntPtr.Zero, ref deviceInfo);
                if (ret != 0) {
                    System.Diagnostics.Trace.WriteLine("BluetoothGetDeviceInfo returned: 0x" + ret.ToString("X"));
                }            

                valid = true;
            }
        }
#endif
        #endregion

        #region Refresh
        /// <summary>
        /// Forces the system to refresh the device information.
        /// </summary>
        /// -
        /// <remarks>
        /// See <see cref="P:InTheHand.Net.Sockets.BluetoothDeviceInfo.DeviceName"/>
        /// for one reason why this method is necessary.
        /// </remarks>
        public void Refresh()
        {
#if WinXP
            valid = false;
#endif
            deviceInfo.ulClassofDevice = 0;
            deviceInfo.szName = "";           
        }
        #endregion

        #region Update
        /// <summary>
        /// Updates the device name used to display the device, affects the local computer cache.
        /// </summary>
        /// <remarks>On Windows CE this only affects devices which are already paired.</remarks>
        public void Update()
        {
#if WinCE
            RegistryKey devkey = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\Device\\" + this.DeviceAddress.ToString(),true);

            //if local record is present
            if (devkey != null)
            {
                //write the new name
                devkey.SetValue("name", this.deviceInfo.szName);
                devkey.Flush();
                devkey.Close();
            }
#else
            int result = NativeMethods.BluetoothUpdateDeviceRecord(ref this.deviceInfo);
#endif
        }
        #endregion

        #region Address
        /// <summary>
		/// Gets the device identifier.
		/// </summary>
        public BluetoothAddress DeviceAddress
		{
			get
			{
				return new BluetoothAddress(deviceInfo.Address);
			}
		}
        #endregion

        #region Name
        /// <summary>
		/// Gets a name of a device.
		/// </summary>
        /// -
        /// <remarks>
        /// <para>Note, that due the way in which Bluetooth device discovery works,
        /// the existence and address of a device is known first, but a separate
        /// query has to be carried out to find whether the device also has a name.
        /// This means that if a device is discovered afresh then this property might
        /// return only a text version of the device&#x2019;s address and not its
        /// name, one can also see this in the Windows&#x2019; Bluetooth device dialogs
        /// where the device appears first with its address and the name is later
        /// updated.  To see the name, wait for some time and access this property again
        /// having called <see cref="M:InTheHand.Net.Sockets.BluetoothDeviceInfo.Refresh"/>
        /// in the meantime.
        /// </para>
        /// </remarks>
		public string DeviceName
		{
			get
			{
#if WinCE

#if V1
                if((deviceInfo.szName == null) || (deviceInfo.szName == string.Empty))
#else
                if (string.IsNullOrEmpty(deviceInfo.szName))
#endif
				{
                    int bufferLen = 256;
					byte[] buffer = new byte[bufferLen*2];
					int len;
					int result = NativeMethods.BthRemoteNameQuery(this.DeviceAddress.ToByteArray(), bufferLen, out len, buffer);

					if((result!=0) | (len==0))
					{
						return this.DeviceAddress.ToString("C");
					}
					//length excluding trailing null and converted to bytes
					deviceInfo.szName = System.Text.Encoding.Unicode.GetString(buffer, 0, (len-1)*2);
				}
				return deviceInfo.szName;
#else
				GetDeviceInfo();

                    if (string.IsNullOrEmpty(deviceInfo.szName))
                    {
                        return this.DeviceAddress.ToString("C");
                    }

                return deviceInfo.szName;
#endif
			}
            set
            {
                deviceInfo.szName = value;
            }
        }
        #endregion

        #region Class of Device
        /// <summary>
        /// Returns the Class of Device of the remote device.
        /// </summary>
        /// -
        /// <remarks>
        /// <para>
        /// Some CE 4.2 devices such as original PPC2003 devices don't have the native 
        /// API on which this property depends &#x2014; it was added as part of a hotfix. 
        /// The property will always return zero in such a case.  On WM/CE we also 
        /// attempt to get the CoD value as part of the discovery process; this is 
        /// of course only works for devices in-range.
        /// </para>
        /// </remarks>
        public ClassOfDevice ClassOfDevice
        {
            get
            {
#if WinCE
                if (deviceInfo.ulClassofDevice == 0)
                {
                    //open a baseband connection
                    if (Connect())
                    {
                        try
                        {
                            //get the remote cod
                            int hresult = NativeMethods.BthGetRemoteCOD(this.DeviceAddress.ToByteArray(), out deviceInfo.ulClassofDevice);
                        }
                        catch (MissingMethodException)
                        {
                            //some CE 4.2 devices such as original PPC2003 devices don't have this API - it was added as part of a hotfix, so catch a possible missingmethodexception
                        }
                        finally
                        {
                            Disconnect();
                        }
                    }
                }
#else
                GetDeviceInfo();
#endif

                return new ClassOfDevice(deviceInfo.ulClassofDevice);
            }
        }
        #endregion

        #region Rssi
#if WinCE
        /// <summary>
        /// Returns the signal strength for the Bluetooth connection with the peer device.
        /// <para><b>Requires Windows Mobile 5.0 or Windows Embedded CE 6.0</b></para>
        /// </summary>
        /// -
        /// <value>Valid values for this property are -128 to 128.  It returns
        /// <see cref="F:System.Int32.MinValue">Int32.MinValue</see> on failure.
        /// </value>
        /// -
        /// <remarks>
        /// <para>This method requires an open connection to the peer device.
        /// If there is no active connection, then it will attempt to create one.
        /// </para>
        /// <note type="caution">Requires Windows Mobile 5.0 or Windows Embedded CE 6.0</note>
        /// <para>As well as the &#x2018;no connection&#x2019; issue, the native method
        /// on which the property depends is only present in later OS versions, so it 
        /// will fail on earlier devices.
        /// </para>
        /// </remarks>
        public int Rssi
        {
            get
            {
                sbyte rssi = 0;

                //only if baseband connection is possible
                try
                {
                    int result;

                    //get the rssi
                    result = NativeMethods.BthReadRSSI(this.DeviceAddress.ToByteArray(), out rssi);

                    //execution failed
                    const int ErrorNotFound = 0x00000490; // = 1168
                    if (result == ErrorNotFound)
                    {
                        //try again with baseband connection
                        Connect();
                        result = NativeMethods.BthReadRSSI(this.DeviceAddress.ToByteArray(), out rssi);
                    }
                    if (result != 0)
                    {
                        return int.MinValue;
                        //throw new NotSupportedException(string.Format("Failed retrieving Rssi with error {0}", result.ToString("X8")), new System.ComponentModel.Win32Exception(result));
                    }
                }
                catch (MissingMethodException)
                {
                    return int.MinValue;
                    //throw new PlatformNotSupportedException("Rssi property requires Windows Mobile 5.0 or Windows Embedded CE 6.0", mme);
                }
                finally
                {
                    Disconnect();
                }
                return rssi;
            }
        }
#endif
        #endregion

        #region Installed Services
        /// <summary>
		/// Returns a list of services which are already installed for use on the calling machine.
		/// </summary>
		/// <remarks>
        /// <para>This property returns the services already configured for use. 
        /// Those are the ones that are checked in the &#x201C;Services&#x201D; tab
        /// of the device&#x2019;s property sheet in the Bluetooth Control panel.
        /// I presume the behaviour is similar on CE.
        /// </para>
        /// <para>Will only return available services for paired devices.
        /// </para>
        /// <para>It of course will also only returns standard system services which Windows understands.
        /// (On desktop Windows this method calls the OS function <c>BluetoothEnumerateInstalledServices</c>).
        /// </para>
        /// <para>To see all the services that a device advertises use the 
        /// <see cref="M:InTheHand.Net.Sockets.BluetoothDeviceInfo.GetServiceRecords(System.Guid)"/>
        /// method.
        /// </para>
        /// </remarks>
        public Guid[] InstalledServices
        {
            get
            {
#if WinCE
                
                if (this.Authenticated)
                {
                    try
                    {
                        System.Collections.ArrayList foundServices = new System.Collections.ArrayList();

                        using(RegistryKey deviceKey = Registry.LocalMachine.OpenSubKey(NativeMethods.ceRegistryRoot + "Device\\" + this.DeviceAddress.ToString() + "\\Services")) {
                            if (deviceKey == null)
                            {
                                // Handle the 'no such key' case here, rather than
                                // just letting a NRE occur at the next line.
                                return new Guid[0];
                            }
                            foreach (string serviceid in deviceKey.GetSubKeyNames())
                            {
                                foundServices.Add(new Guid(serviceid));
                            }

                        }//using

                        return (Guid[])foundServices.ToArray(typeof(Guid));
                    }
                    catch (Exception ex)
                    {
                        System.Diagnostics.Debug.Fail("Exception in get_InstalledServices: " + ex);
                        return new Guid[0];
                    }
                }
                return new Guid[0];
            
#else
            
                GetDeviceInfo();

                int nservices = 0;
                //get the count

                int result = NativeMethods.BluetoothEnumerateInstalledServices(IntPtr.Zero, ref deviceInfo, ref nservices, null);

                byte[] services = new byte[nservices*16];

                result = NativeMethods.BluetoothEnumerateInstalledServices(IntPtr.Zero, ref deviceInfo, ref nservices, services);


                if (result < 0)
                {
                    return new Guid[0];
                }
                Guid[] foundservices = new Guid[nservices];
                for (int iservice = 0; iservice < nservices; iservice++)
                {
                    byte[] buffer = new byte[16];
                    Buffer.BlockCopy(services, iservice * 16, buffer, 0, 16);
                    foundservices[iservice] = new Guid(buffer);
                }
                return foundservices;
#endif
            }
        }
        #endregion

        #region Set Service State
        /// <summary>
        /// Enables or disables services for a Bluetooth device.
        /// </summary>
        /// <param name="service">The service GUID on the remote device.</param>
        /// <param name="state">Service state - TRUE to enable the service, FALSE to disable it.</param>
        /// <remarks>
        /// When called on Windows CE, the device will require a soft-reset to enabled the settings.
        /// 
        ///<note>
        /// <para>The system maintains a mapping of service guids to supported drivers for
        /// Bluetooth-enabled devices. Enabling a service installs the corresponding
        /// device driver. Disabling a service removes the corresponding device driver.
        /// If a non-supported service is enabled, a driver will not be installed.
        /// </para>
        /// </note>
        /// <para>This overload is silent on error; the other overload raises an exception
        /// if required
        /// (<see cref="M:InTheHand.Net.Sockets.BluetoothDeviceInfo.SetServiceState(System.Guid,System.Boolean,System.Boolean)"/>).
        /// </para>
        /// </remarks>
        /// -
        /// <exception cref="PlatformNotSupportedException">
        /// Thrown if this method is called on Windows CE platforms.</exception>
        public void SetServiceState(Guid service, bool state)
        {
            SetServiceState(service, state, false);
        }

        /// <summary>
        /// Enables or disables services for a Bluetooth device.
        /// </summary>
        /// <param name="service">The service GUID on the remote device.</param>
        /// <param name="state">Service state - TRUE to enable the service, FALSE to disable it.</param>
        /// <param name="throwOnError">Whether the method should raise an exception
        /// when 
        /// </param>
        /// <remarks>
        /// When called on Windows CE, the device will require a soft-reset to enabled the settings.
        ///<note>
        /// <para>The system maintains a mapping of service guids to supported drivers for
        /// Bluetooth-enabled devices. Enabling a service installs the corresponding
        /// device driver. Disabling a service removes the corresponding device driver.
        /// If a non-supported service is enabled, a driver will not be installed.
        /// </para>
        /// </note>
        /// </remarks>
        /// -
        /// <exception cref="T:System.ComponentModel.Win32Exception">The call failed.
        /// </exception>
        public void SetServiceState(Guid service, bool state, bool throwOnError)
        {
#if WinCE
            if (service == BluetoothService.SerialPort)
            {
                if (state)
                {
                    //write registry settings for WM5 Serial Port support

                    //get available ports
                    Microsoft.Win32.RegistryKey rkPorts = Microsoft.Win32.Registry.LocalMachine.OpenSubKey("SOFTWARE\\Microsoft\\Bluetooth\\Serial\\Ports", true);
                    string[] supportedPorts = (string[])rkPorts.GetValue("SupportedPorts");
                    System.Collections.ArrayList alPorts = new System.Collections.ArrayList(supportedPorts);

                    //check availability
                    foreach (string deviceid in rkPorts.GetSubKeyNames())
                    {
                        Microsoft.Win32.RegistryKey rkDevice = rkPorts.OpenSubKey(deviceid);
                        //remove port from arraylist if unavailable
                        string port = rkDevice.GetValue("Port").ToString();
                        int nullPos = port.IndexOf('\0');
                        if (nullPos > -1)
                        {
                            port = port.Substring(0, nullPos);
                        }
                        if (alPorts.Contains(port))
                        {
                            alPorts.Remove(port);
                        }
                        rkDevice.Close();
                    }

                    if (alPorts.Count == 0)
                    {
                        throw new InvalidOperationException("No ports available");
                    }
                    //write port details to registry
                    Microsoft.Win32.RegistryKey rkNewPort = rkPorts.CreateSubKey(this.DeviceAddress.ToString("8"));
                    rkNewPort.SetValue("KeepDCB", 0);
                    rkNewPort.SetValue("RemoteDCB", 0);
                    rkNewPort.SetValue("Encryption", 0);
                    rkNewPort.SetValue("Authentication", 0);
                    rkNewPort.SetValue("Port", alPorts[0]);
                    rkNewPort.SetValue("Server", 0);
                    rkNewPort.Close();

                    rkPorts.Close();

                    //try open port now
                    try
                    {
                        InTheHand.Net.Ports.BluetoothSerialPort.CreateClient(alPorts[0].ToString(), new BluetoothEndPoint(this.DeviceAddress, BluetoothService.SerialPort));
                    }
                    catch
                    {
                    }
                }
                else
                {
                    //find and remove registry entries
                    Microsoft.Win32.RegistryKey rkPorts = Microsoft.Win32.Registry.LocalMachine.OpenSubKey("SOFTWARE\\Microsoft\\Bluetooth\\Serial\\Ports", true);
                    foreach (string deviceAddress in rkPorts.GetSubKeyNames())
                    {
                        if (deviceAddress == this.DeviceAddress.ToString("8"))
                        {
                            rkPorts.DeleteSubKeyTree(deviceAddress);
                            break;
                        }
                    }
                    rkPorts.Close();
                }

            }
            else if (service == BluetoothService.AudioSink)
            {
                //set the enabled flag (will be reflected in UI)
                Microsoft.Win32.RegistryKey rkDeviceServices = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\Device\\" + DeviceAddress.ToString("N") + "\\Services\\0000110b-0000-1000-8000-00805f9b34fb", true);
                if (rkDeviceServices != null)
                {
                    rkDeviceServices.SetValue("Enabled", state ? 1 : 0);
                    rkDeviceServices.Close();
                }
                //set/remove as one of the 4 audio devices
                Microsoft.Win32.RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\A2DP\\Devices");
                if (rk != null)
                {
                    string[] keyNames = rk.GetSubKeyNames();
                    foreach (string keyName in keyNames)
                    {
                        RegistryKey rk2 = rk.OpenSubKey(keyName, true);
                        byte[] addressBytes = (byte[])rk2.GetValue("Address");
                        BluetoothAddress ba = new BluetoothAddress(addressBytes);
                        if (ba == this.DeviceAddress)
                        {
                            //already in there
                            if (!state)
                            {
                                //need to delete - reset to all zeros;
                                rk2.SetValue("Address", BluetoothAddress.None.ToByteArray());
                                rk2.Close();
                                break;
                            }
                        }
                        if (ba == BluetoothAddress.None)
                        {
                            if (state)
                            {
                                //need to add
                                rk2.SetValue("Address", DeviceAddress.ToByteArray());
                                rk2.Close();
                                break;
                            }
                        }
                        rk2.Close();
                    }
                    rk.Close();
                }
            }
            else if ((service == BluetoothService.Handsfree) | (service == BluetoothService.Headset))
            {
                //set the enabled flag (will be reflected in UI)
                Microsoft.Win32.RegistryKey rkDeviceServices = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\Device\\" + DeviceAddress.ToString("N") + "\\Services\\" + service.ToString("D"), true);
                if (rkDeviceServices != null)
                {
                    rkDeviceServices.SetValue("Enabled", state ? 1 : 0);
                    rkDeviceServices.Close();
                }

                //set/remove the audio gateway device
                Microsoft.Win32.RegistryKey rk = Registry.LocalMachine.OpenSubKey("Software\\Microsoft\\Bluetooth\\AudioGateway\\Devices", true);
                if (rk != null)
                {
                    bool written = false;
                    string[] keyNames = rk.GetSubKeyNames();
                    foreach (string keyName in keyNames)
                    {
                        RegistryKey rk2 = rk.OpenSubKey(keyName, true);
                        byte[] addressBytes = (byte[])rk2.GetValue("Address");
                        BluetoothAddress ba = new BluetoothAddress(addressBytes);
                        if (ba == this.DeviceAddress)
                        {
                            //already in there
                            if (!state)
                            {
                                break;
                            }
                        }
                        if (ba == BluetoothAddress.None)
                        {
                            if (state)
                            {
                                //need to add
                                rk2.SetValue("Address", DeviceAddress.ToByteArray());
                                rk2.SetValue("Service", service.ToByteArray());
                                rk2.Close();
                                written = true;
                                break;
                            }
                        }
                        rk2.Close();
                    }
                    if (state && !written)
                    {
                        RegistryKey rk2 = rk.CreateSubKey("1");
                        rk2.SetValue("Address", DeviceAddress.ToByteArray());
                        rk2.SetValue("Service", service.ToByteArray());
                        rk2.Close();

                    }
                    rk.Close();
                }
            }
            else
            {
                throw new PlatformNotSupportedException("Not supported under Windows CE");
            }
#else
            GetDeviceInfo();
            // MSDN says the posible errors are:
            //   ERROR_INVALID_PARAMETER The dwServiceFlags are invalid. 
            //   ERROR_SERVICE_DOES_NOT_EXIST The GUID specified in pGuidService is not supported. 
            // Numerically:
            //   #define ERROR_FILE_NOT_FOUND             2L
            //   #define ERROR_SERVICE_DOES_NOT_EXIST     1060L
            //   #define ERROR_NOT_FOUND                  1168L
            //
            // Seen:
            // • 0x00000424 = 1060 ----> ERROR_SERVICE_DOES_NOT_EXIST
            // When service not present, or device not present.
            //
            // • 0x80070002        -/\-> ERROR_FILE_NOT_FOUND
            // PANU on Broadcom peer.  "No driver for service"?
            //
            // • 0x00000490 = 1168 ----> ERROR_NOT_FOUND
            // Setting 'False' on a service not set previously registered.
            const int BLUETOOTH_SERVICE_DISABLE = 0x00;
            const int BLUETOOTH_SERVICE_ENABLE = 0x01;
            int hresult = NativeMethods.BluetoothSetServiceState(IntPtr.Zero, ref deviceInfo, ref service,
                state ? BLUETOOTH_SERVICE_ENABLE : BLUETOOTH_SERVICE_DISABLE);
            if (hresult != 0) {
                System.ComponentModel.Win32Exception ex 
                    = new System.ComponentModel.Win32Exception(hresult);
                if (throwOnError) {
                    throw ex;
                }
            }
#endif
        }
        #endregion

        #region Get Service Records
        /// <summary>
        /// Run an SDP query on the device&#x2019;s Service Discovery Database.
        /// </summary>
        /// -
        /// <remarks>
        /// <para>
        /// For instance to see whether the device has an an Serial Port services
        /// search for UUID <see cref="F:InTheHand.Net.Bluetooth.BluetoothService.SerialPort"/>,
        /// or too find all the services that use RFCOMM use 
        /// <see cref="F:InTheHand.Net.Bluetooth.BluetoothService.RFCommProtocol"/>,
        /// or all the services use 
        /// <see cref="F:InTheHand.Net.Bluetooth.BluetoothService.L2CapProtocol"/>.
        /// </para>
        /// <para>
        /// If the device isn&#x2019;t accessible a <see cref="T:System.Net.Sockets.SocketException"/>
        /// with <see cref="P:System.Net.Sockets.SocketException.ErrorCode"/>
        /// 10108 (0x277C) occurs.
        /// </para>
        /// </remarks>
        /// -
        /// <param name="service">The UUID to search for, as a <see cref="T:System.Guid"/>.
        /// </param>
        /// -
        /// <returns>The parsed record as an 
        /// <see cref="T:InTheHand.Net.Bluetooth.ServiceRecord"/>.
        /// </returns>
        /// -
        /// <example>
        /// <code lang="Visual Basic">
        /// Dim bdi As BluetoothDeviceInfo = ...
        /// Dim records As ServiceRecord() = bdi.GetServiceRecords(BluetoothService.RFCommProtocol)
        /// ' Dump each to console
        /// For Each curRecord As ServiceRecord In records
        ///    ServiceRecordUtilities.Dump(Console.Out, curRecord)
        /// Next
        /// </code>
        /// </example>
        /// 
        /// -
        /// <exception cref="T:System.Net.Sockets.SocketException">
        /// The query failed.
        /// </exception>
        public ServiceRecord[] GetServiceRecords(Guid service)
        {
            byte[][] rawRecords = GetServiceRecordsUnparsed(service);
            ServiceRecord[] records = new ServiceRecord[rawRecords.Length];
            ServiceRecordParser parser = new ServiceRecordParser();
            int i = 0;
            foreach (byte[] rawBytes in rawRecords) {
                ServiceRecord record = parser.Parse(rawBytes);
                record.SetSourceBytes(rawBytes);
                records[i] = record;
                ++i;
            }
            return records;
        }

        /// <summary>
        /// Run an SDP query on the device&#x2019;s Service Discovery Database,
        /// returning the raw byte rather than a parsed record.
        /// </summary>
        /// -
        /// <remarks>
        /// If the device isn&#x2019;t accessible a <see cref="T:System.Net.Sockets.SocketException"/>
        /// with <see cref="P:System.Net.Sockets.SocketException.ErrorCode"/>
        /// 10108 (0x277C) occurs.
        /// </remarks>
        /// -
        /// <param name="service">The UUID to search for, as a <see cref="T:System.Guid"/>.
        /// </param>
        /// -
        /// <returns>An array of array of <see cref="T:System.Byte"/>.</returns>
        /// -
        /// <exception cref="T:System.Net.Sockets.SocketException">
        /// The query failed.
        /// </exception>
        public byte[][] GetServiceRecordsUnparsed(Guid service)
        {
            byte[][] result = GetServiceRecordsUnparsedWindowsRaw(service);
#if WinCE
            if (Environment.OSVersion.Platform == PlatformID.WinCE) {
                if (result.Length != 0) {
                    System.Diagnostics.Debug.Assert(result.Length == 1, "Expect one multi-record item on CE.");
                    result = ServiceRecordParser.SplitSearchAttributeResult(result[0]);
                }
            }
#endif
            return result;
        }

        /// <summary>
        /// Returns the raw results from the native call(s); the format is different 
        /// on Win32 versus WinCE.
        /// </summary>
        /// <remarks>
        /// On CE this is thus a single item which is a ElementSequence of records.
        /// On Win32 it is an array with each item being a record.
        /// </remarks>
        public byte[][] GetServiceRecordsUnparsedWindowsRaw(Guid service)
        {
            WqsOffset.AssertCheckLayout();
            BlobOffsets.AssertCheckLayout();
            //temporary workaround - sockets must be initialised
            Socket s = new Socket(AddressFamily32.Bluetooth, SocketType.Stream, BluetoothProtocolType.RFComm);

            //store variable length collection of records
            System.Collections.ArrayList records = new System.Collections.ArrayList();

            byte[] sdp = null;
            
            WSAQUERYSET wqs = new WSAQUERYSET();
            wqs.dwSize = WqsOffset.StructLength_60;
            wqs.dwNameSpace = WqsOffset.NsBth_16;

#if WinCE
            CSADDR_INFO sainfo = new CSADDR_INFO(null, this.DeviceAddress , SocketType.Unknown, ProtocolType.Unknown);
            wqs.dwNumberOfCsAddrs = 1;
            
            IntPtr pSaInfo = Marshal32.AllocHGlobal(24);
            IntPtr pBrb = Marshal32.AllocHGlobal(256);
            IntPtr pService = Marshal32.AllocHGlobal(240);

            Marshal.StructureToPtr(sainfo, pSaInfo, false);
            wqs.lpcsaBuffer = pSaInfo;            

            Marshal.WriteInt32(pBrb, 0, (int)SdpQueryType.SearchAttributeRequest);

            //write the service guid
            Marshal.Copy(service.ToByteArray(), 0, new IntPtr(pBrb.ToInt32() + 8), 16);
            Marshal.WriteInt16(pBrb, 24, (short)SdpSpecificType.Uuid128);
            Marshal.WriteInt16(pBrb, 26, 0);

            //write an empty guid to the next position
            Marshal.Copy(Guid.Empty.ToByteArray(), 0, new IntPtr(pBrb.ToInt32() + 28), 16);
            Marshal.WriteInt16(pBrb, 44, 0x0);
            Marshal.WriteInt16(pBrb, 46, 0);

            //number of attribute ranges
            Marshal.WriteInt32(pBrb, 248, 1);
            //min attribute
            Marshal.WriteInt16(pBrb, 252, 0);
            //max attribute
            Marshal.WriteInt16(pBrb, 254, 0x800);
            
            BLOB b = new BLOB(256, pBrb);

            IntPtr pb = Marshal32.AllocHGlobal(8);

            Marshal.StructureToPtr(b, pb, false);
            wqs.lpBlob = pb;
            
#endif


#if WinXP
            GCHandle hservice = GCHandle.Alloc(service.ToByteArray(),GCHandleType.Pinned);
            wqs.lpServiceClassId = hservice.AddrOfPinnedObject();
            wqs.lpszContext = "(" + this.DeviceAddress.ToString("C") + ")"; // sb.ToString(); // hContext.AddrOfPinnedObject();
#endif
            
            int handle;

            int lookupresult;

            //start looking for Bluetooth services


#if WinCE
            LookupFlags flagsForBegin; // Move above the #if is changed to use for desktop build too.
            flagsForBegin = 0;
            bool isQueryingLocalhost = false;
            try {
                BluetoothRadio theOne = BluetoothRadio.PrimaryRadio; // Only ever one on CE...
                if (theOne != null) {
                    BluetoothAddress localAddr = theOne.LocalAddress;
                    if (localAddr != null) {
                        if (localAddr == this.DeviceAddress) {
                            isQueryingLocalhost = true;
                        }
                    }
                }
            } catch (Exception ex) {
                System.Diagnostics.Debug.Fail("Exception in hack on CE to check if localhost: " + ex);
            }
            if (isQueryingLocalhost) {
                flagsForBegin |= LookupFlags.ResService;
            }
#endif
#if WinCE
            try
            {
                lookupresult = NativeMethods.WSALookupServiceBegin(ref wqs, flagsForBegin, out handle);
#else
                lookupresult = NativeMethods.WSALookupServiceBegin(ref wqs, LookupFlags.FlushCache | LookupFlags.ReturnName | LookupFlags.ReturnBlob, out handle);
#endif
                BluetoothClient.ThrowSocketExceptionForHR(lookupresult);


#if WinXP
                hservice.Free();
#endif

                while (lookupresult == 0)
                {
                    byte[] sdpBuffer = new byte[6000];
                    BitConverter.GetBytes(WqsOffset.StructLength_60).CopyTo(sdpBuffer, WqsOffset.dwSize_0);
                    BitConverter.GetBytes(WqsOffset.NsBth_16).CopyTo(sdpBuffer, WqsOffset.dwNameSpace_20);
                    int size = sdpBuffer.Length;

#if WinCE
                    lookupresult = NativeMethods.WSALookupServiceNext(handle, (LookupFlags)0, ref size, sdpBuffer);
#else
                    lookupresult = NativeMethods.WSALookupServiceNext(handle, LookupFlags.FlushCache | LookupFlags.ReturnBlob, ref size, sdpBuffer);
#endif

                    if (lookupresult == -1)
                    {
                        const int WSA_E_NO_MORE = 10110;
                        BluetoothClient.ThrowSocketExceptionForHrExceptFor(lookupresult, WSA_E_NO_MORE);
                    }
                    else
                    {
                        IntPtr pBlob = InTheHand.Runtime.InteropServices.Marshal32.ReadIntPtr(sdpBuffer, WqsOffset.lpBlob_56);
                        if (pBlob != IntPtr.Zero)
                        {
                            IntPtr pSdpBlob = InTheHand.Runtime.InteropServices.Marshal32.ReadIntPtr(pBlob, BlobOffsets.Offset_pBlobData_4);
                            int cSdpBlob = Marshal.ReadInt32(pBlob);

                            if (cSdpBlob > 2)
                            {
                                sdp = new byte[cSdpBlob];
                                Marshal.Copy(pSdpBlob, sdp, 0, cSdpBlob);
                                records.Add(sdp);
                            }
                        }

                    }

                }
            
#if WinCE
            }
            finally
            {
                sainfo.Dispose();

                Marshal32.FreeHGlobal(pSaInfo);
                Marshal32.FreeHGlobal(pb);
                Marshal32.FreeHGlobal(pBrb);
            }
#endif
            
            //stop looking
            lookupresult = NativeMethods.WSALookupServiceEnd(handle);
            BluetoothClient.ThrowSocketExceptionForHR(lookupresult);
          
            return (byte[][])records.ToArray(typeof(byte[]));
        }
        #endregion

        #region Connected
        /// <summary>
        /// Specifies whether the device is connected.
		/// </summary>
		/// <remarks>Not supported under Windows CE and will always return false.</remarks>
        /// <seealso cref="Remembered"/>
        /// <seealso cref="Authenticated"/>
		public bool Connected
		{
			get
			{
#if WinCE
                return false;
#else
				GetDeviceInfo();

                return deviceInfo.fConnected;
#endif	
			}
        }
        #endregion

        #region Remembered
        /// <summary>
        /// Specifies whether the device is a remembered device. Not all remembered devices are authenticated.
		/// </summary>
        /// -
        /// <remarks>Now supported under Windows CE &#x2014; will return the same as 
        /// <see cref="P:InTheHand.Net.Sockets.BluetoothDeviceInfo.Authenticated"/>.
        /// </remarks>
        /// <seealso cref="Connected"/>
        /// <seealso cref="Authenticated"/>
		public bool Remembered
		{
			get
			{
#if WinCE
                System.Diagnostics.Debug.Assert(deviceInfo.fAuthenticated == deviceInfo.fRemembered, 
                    "CE fAuthenticated == fRemembered");
#else
				GetDeviceInfo();               
#endif
                return deviceInfo.fRemembered;
			}
        }
        #endregion

        #region Authenticated
        /// <summary>
        /// Specifies whether the device is authenticated, paired, or bonded. All authenticated devices are remembered.
		/// </summary>
		/// <remarks>Is now supported on both CE and XP.</remarks>
        /// <seealso cref="Connected"/>
        /// <seealso cref="Remembered"/>
		public bool Authenticated
		{
			get
			{
#if WinXP
                GetDeviceInfo();
#else
                System.Diagnostics.Debug.Assert(deviceInfo.fAuthenticated == deviceInfo.fRemembered,
                    "CE fAuthenticated == fRemembered");
#endif
                return deviceInfo.fAuthenticated;
			}
#if WinCE
#if V2
            internal set
#else
            set
#endif
            {
                //only for CE
                deviceInfo.fAuthenticated = value;
                deviceInfo.fRemembered = value;
            }
#endif
        }
        #endregion


        #region Last Seen
        /// <summary>
		/// Date and Time this device was last seen by the system.
		/// </summary>
        /// -
		/// <remarks><para>Not supported under Windows CE and will return DateTime.MinValue.
        /// </para>
        /// <para>This value is supported on Win32 where it is read from a native 
        /// API; it however has a bug.  The value provided is always simply the current 
        /// time, e.g. after a discovery for every device returned this value has 
        /// the time of the discovery operation.  Tracked by workitem 
        /// <see href="http://www.codeplex.com/32feet/WorkItem/View.aspx?WorkItemId=10280">10280</see>.
        /// </para>
        /// </remarks>
        /// -
        /// <value>
        /// An instance of <see cref="T:System.DateTime"/> containing the time in UTC,
        /// or <c>DateTime</c>.<see cref="F:System.DateTime.MinValue"/>
        /// if there's no value.
        /// </value>
		public DateTime LastSeen
		{
			get
			{
#if WinCE
                return DateTime.MinValue;
#else
				GetDeviceInfo();

                return deviceInfo.LastSeen;				
#endif
			}
        }
        #endregion

        #region Last Used
        /// <summary>
		/// Date and Time this device was last used by the system.
		/// </summary>
        /// -
		/// <remarks>Not supported under Windows CE and will return DateTime.MinValue.</remarks>
        /// -
        /// <value>
        /// An instance of <see cref="T:System.DateTime"/> containing the time in UTC,
        /// or <c>DateTime</c>.<see cref="F:System.DateTime.MinValue"/> 
        /// if there's no value.
        /// </value>
        public DateTime LastUsed
		{
			get
			{
#if WinCE
                return DateTime.MinValue;
#else
				GetDeviceInfo();
                return deviceInfo.LastUsed;
#endif                 
			}
        }
        #endregion


        #region Show Dialog
        /// <summary>
		/// Displays information about the device.
		/// </summary>
		public void ShowDialog()
		{
#if WinCE
			System.Windows.Forms.MessageBox.Show("Name: " + this.DeviceName + "\r\nAddress: " + this.DeviceAddress.ToString("C"), this.DeviceName + " Properties",System.Windows.Forms.MessageBoxButtons.OK,System.Windows.Forms.MessageBoxIcon.None,System.Windows.Forms.MessageBoxDefaultButton.Button1);
#else
            GetDeviceInfo();
            bool success = NativeMethods.BluetoothDisplayDeviceProperties(IntPtr.Zero, ref deviceInfo);
#endif
        }
        #endregion

        #region Equals
        /// <summary>
		/// Compares two <see cref="BluetoothDeviceInfo"/> instances for equality.
		/// </summary>
		/// <param name="obj"></param>
		/// <returns></returns>	
		public override bool Equals(object obj)
		{
			//objects are equal if device address matches
			BluetoothDeviceInfo bdi = obj as BluetoothDeviceInfo;
			
			if(bdi!=null)
			{
				return this.deviceInfo.Address.Equals(bdi.deviceInfo.Address);
			}

			return base.Equals(obj);
        }
        #endregion

        #region Get Hash Code
        /// <summary>
		/// Returns the hash code for this instance. 
		/// </summary>
		/// <returns></returns>
		public override int GetHashCode()
		{
			return this.deviceInfo.Address.GetHashCode();
        }
        #endregion


        #region IComparable Members

        int IComparable.CompareTo(object obj)
        {
            //objects are equal if device address matches
            BluetoothDeviceInfo bdi = obj as BluetoothDeviceInfo;

            if (bdi != null)
            {
                return ((IComparable)this.DeviceAddress).CompareTo(bdi);
            }

            return -1;
        }

        #endregion

#if WinCE
        private ushort basebandHandle = 0;
        //Connect/Disconnect baseband connection required for some properties
        private bool Connect()
        {
            if (basebandHandle == 0)
            {
                int hresult = NativeMethods.BthCreateACLConnection(this.DeviceAddress.ToByteArray(), out basebandHandle);

                if (hresult != 0)
                {
                    //e.g. 0x05b4=1460=ErrorTimeout
                    return false;
                }
            }

            return true;
        }

        private void Disconnect()
        {
            if (basebandHandle != 0)
            {
                int hresult = NativeMethods.BthCloseConnection(basebandHandle);
                basebandHandle = 0;
            }
        }
#endif
    }
}
