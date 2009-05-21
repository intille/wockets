// 32feet.NET - Personal Area Networking for .NET
//
// InTheHand.Net.Bluetooth.BluetoothRadio
// 
// Copyright (c) 2003-2008 In The Hand Ltd, All rights reserved.
// This source code is licensed under the In The Hand Community License - see License.txt

using System;
using System.Collections;
using Microsoft.Win32;

namespace InTheHand.Net.Bluetooth
{
	/// <summary>
	/// Represents a Bluetooth Radio device.
	/// </summary>
	/// <remarks>Allows you to query properties of the radio hardware and set the mode.</remarks>
	public sealed class BluetoothRadio //: IDisposable
	{

		#region IsSupported
		/// <summary>
		/// Gets a value that indicates whether the 32feet.NET library can be used with the current device.
		/// </summary>
		public static bool IsSupported
		{
            get
            {
#if WinCE
                PlatformVerification.ThrowException();
                
                try
                {
                        HardwareStatus status = 0;
                        int result = NativeMethods.BthGetHardwareStatus(ref status);
                        if (result == 0)
                        {
                            if (status != HardwareStatus.NotPresent)
                            {
                                return true;
                            }
                        }
                }
                catch
                {
                }

                return false;
#else
                return  (AllRadios.Length > 0);
#endif
            }
		}
		#endregion
		
#if WinXP
        private BLUETOOTH_RADIO_INFO radio;
        private IntPtr handle;
#else
        //private IntPtr msgQueueHandle;
        //private IntPtr notificationHandle;
#endif
		


		#region Constructor
		internal BluetoothRadio(IntPtr handle)
		{
			
#if WinCE
			//get version/manufacturer
			byte hv;
			ushort hr;
			byte lv;
			ushort ls;
			ushort man;
			byte fea;

			int hresult = NativeMethods.BthReadLocalVersion(out hv, out hr, out lv, out ls, out man, out fea);
			if(hresult==0)
			{
				manufacturer = (Manufacturer)man;
				lmpSubversion = ls;
			}
			else
			{
				manufacturer = Manufacturer.Unknown;
			}

            //setup message queue

            /*NativeMethods.MSGQUEUEOPTIONS mqo = new NativeMethods.MSGQUEUEOPTIONS();
            mqo.dwFlags = 0;
            mqo.cbMaxMessage = 72;
            mqo.bReadAccess = true;
            mqo.dwSize = System.Runtime.InteropServices.Marshal.SizeOf(mqo);
            msgQueueHandle = NativeMethods.CreateMsgQueue("InTheHand.Net.Bluetooth.BluetoothRadio", ref mqo);

            notificationHandle = NativeMethods.RequestBluetoothNotifications(NativeMethods.BTE_CLASS.CONNECTIONS | NativeMethods.BTE_CLASS.DEVICE | NativeMethods.BTE_CLASS.PAIRING | NativeMethods.BTE_CLASS.STACK, msgQueueHandle);

            System.Threading.Thread t = new System.Threading.Thread(new System.Threading.ThreadStart(EventThread));
            t.IsBackground = true;
            t.Start();*/
#else
            radio = new BLUETOOTH_RADIO_INFO();
            radio.dwSize = 520;
            System.Diagnostics.Debug.Assert(System.Runtime.InteropServices.Marshal.SizeOf(radio) == radio.dwSize, "BLUETOOTH_RADIO_INFO SizeOf == dwSize");

			int hresult = NativeMethods.BluetoothGetRadioInfo(handle, ref radio);
            if(hresult!=0)
            {
                throw new System.ComponentModel.Win32Exception(hresult, "Error retrieving Radio information.");
            }

            this.handle = handle;
#endif
            }
		#endregion

		#region Primary Radio
#if WinCE
        private static BluetoothRadio primaryRadio;
#endif
		/// <summary>
		/// Gets the primary <see cref="BluetoothRadio"/>.
		/// </summary>
		/// <remarks>For Windows CE based devices this is the only <see cref="BluetoothRadio"/>, for Windows XP this is the first available <see cref="BluetoothRadio"/> device.
		/// <para>If the device has a third-party stack this property will return null</para></remarks>
		public static BluetoothRadio PrimaryRadio
		{
			get
			{
#if WinCE
                if (primaryRadio == null)
                {
                    if (IsSupported)
                    {
                        primaryRadio = new BluetoothRadio(IntPtr.Zero);
                    }
                }
                return primaryRadio;
#else
					//get a single radio
					IntPtr handle = IntPtr.Zero;
					IntPtr findhandle = IntPtr.Zero;

					BLUETOOTH_FIND_RADIO_PARAMS bfrp;
					bfrp.dwSize = 4;
                    System.Diagnostics.Debug.Assert(System.Runtime.InteropServices.Marshal.SizeOf(bfrp) == bfrp.dwSize, "BLUETOOTH_FIND_RADIO_PARAMS SizeOf == dwSize");

					findhandle = NativeMethods.BluetoothFindFirstRadio(ref bfrp, ref handle);
				
					if(findhandle!=IntPtr.Zero)
					{
						NativeMethods.BluetoothFindRadioClose(findhandle);
					}
					if(handle!=IntPtr.Zero)
					{
						return new BluetoothRadio(handle);
					}
					return null;
#endif		
			}

		}
		#endregion

		#region All Radios
		/// <summary>
		///  Gets an array of all Bluetooth radios on the system.  
		/// </summary>
		/// <remarks>Under Windows CE this will only ever return a single <see cref="BluetoothRadio"/> device.
		/// <para>If the device has a third-party stack this property will return an empty collection</para></remarks>
		public static BluetoothRadio[] AllRadios
		{
            get
            {
#if WinCE
                if (IsSupported)
                {
                    return new BluetoothRadio[] { new BluetoothRadio(IntPtr.Zero) };
                }
                return new BluetoothRadio[0] { };
#else
				IntPtr handle = IntPtr.Zero;
				IntPtr findhandle = IntPtr.Zero;

				BLUETOOTH_FIND_RADIO_PARAMS bfrp;
				bfrp.dwSize = 4;
                System.Diagnostics.Debug.Assert(System.Runtime.InteropServices.Marshal.SizeOf(bfrp) == bfrp.dwSize, "BLUETOOTH_FIND_RADIO_PARAMS SizeOf == dwSize");

				ArrayList radiocollection = new ArrayList();

				findhandle = NativeMethods.BluetoothFindFirstRadio(ref bfrp, ref handle);
				
				if(findhandle!=IntPtr.Zero)
				{		
					radiocollection.Add(handle);

					while(NativeMethods.BluetoothFindNextRadio(findhandle, ref handle))
					{
						radiocollection.Add(handle);
					}

					NativeMethods.BluetoothFindRadioClose(findhandle);
				}
				BluetoothRadio[] results = new BluetoothRadio[radiocollection.Count];
				for(int radioindex = 0; radioindex < results.Length; radioindex++)
				{
					results[radioindex] = new BluetoothRadio((IntPtr)radiocollection[radioindex]);
				}

				return results;
#endif
            }
		}
		#endregion



        #region Handle
        /// <summary>
        /// Gets the handle for this radio.
        /// </summary>
        /// <remarks>Relevant only on Windows XP.</remarks>
        public IntPtr Handle
        {
            get
            {
#if WinCE
                return IntPtr.Zero;
#else
                return this.handle;
#endif
            }
        }
        #endregion

        #region Hardware Status
        /// <summary>
        /// Returns the current status of the Bluetooth radio hardware.
        /// </summary>
        /// <value>A member of the <see cref="HardwareStatus"/> enumeration.</value>
        public HardwareStatus HardwareStatus
        {
            get
            {
#if WinCE
                HardwareStatus status = 0;
                int result = NativeMethods.BthGetHardwareStatus(ref status);

                if (result != 0)
                {
                    throw new System.ComponentModel.Win32Exception(result, "Error retrieving Bluetooth hardware status");
                }
                return status;
#else
				return HardwareStatus.Unknown;
#endif
            }
        }

        #endregion

        #region Mode
        /// <summary>
		/// Gets or Sets the current mode of operation of the Bluetooth radio.
		/// </summary>
		/// <remarks>This setting will be persisted when the device is reset.
		/// An Icon will be displayed in the tray on the Home screen and a ?Windows Mobile device will emit a flashing blue LED when Bluetooth is enabled.</remarks>
		public RadioMode Mode
		{
			get
			{
#if WinCE
				RadioMode val;
				int result = NativeMethods.BthGetMode(out val);
				if(result!=0)
				{
					throw new System.ComponentModel.Win32Exception(result, "Error getting BluetoothRadio mode");
				}
				return val;
#else

					if(NativeMethods.BluetoothIsDiscoverable(handle))
					{
						return RadioMode.Discoverable;
					}
					if(NativeMethods.BluetoothIsConnectable(handle))
					{
						return RadioMode.Connectable;
					}
					return RadioMode.PowerOff;
#endif
			}
			set
			{
#if WinCE
				int result = NativeMethods.BthSetMode(value);
				if(result!=0)
				{
					throw new System.ComponentModel.Win32Exception(result, "Error setting BluetoothRadio mode");
				}
#else
				//else
				//{
					switch(value)
					{
						case RadioMode.Discoverable:
							if(Mode==RadioMode.PowerOff)
							{
								NativeMethods.BluetoothEnableIncomingConnections(handle, true);
							}
							NativeMethods.BluetoothEnableDiscovery(handle, true);
							break;
						case RadioMode.Connectable:
							if(Mode==RadioMode.Discoverable)
							{
								NativeMethods.BluetoothEnableDiscovery(handle, false);
							}
							else
							{
								NativeMethods.BluetoothEnableIncomingConnections(handle, true);
							}
							break;
						case RadioMode.PowerOff:
							if(Mode==RadioMode.Discoverable)
							{
								NativeMethods.BluetoothEnableDiscovery(handle, false);
							}
							NativeMethods.BluetoothEnableIncomingConnections(handle, false);
							break;
					}
				//}
#endif
			}
		}
		#endregion

		#region Local Address
#if WinCE
        private BluetoothAddress localAddress;
#endif
		/// <summary>
		/// Get the address of the local Bluetooth radio device.
		/// </summary>
        /// -
        /// <remarks><para>The property can return a <see langword="null"/> value in
        /// some cases.  For instance on CE when the radio is powered-off the value 
        /// will be <see>null</see>.</para>
        /// </remarks>
        /// -
        /// <value>The address of the local Bluetooth radio device.
        /// </value>
		public BluetoothAddress LocalAddress
		{
			get
			{
#if WinCE
                if (localAddress == null)
                {
                    BluetoothAddress ba = new BluetoothAddress();

                    int hresult = NativeMethods.BthReadLocalAddr(ba.ToByteArray());

                    if (hresult == 0)
                    {
                        localAddress = ba;
                    }
                }
                return localAddress;
#else
				return new BluetoothAddress(radio.address);
#endif
			}
		}
		
		#endregion

		#region Name
		/// <summary>
		/// Returns the friendly name of the local Bluetooth radio.
		/// </summary>
        /// <remarks>Currently read-only on Windows XP. Other devices may cache this device name.</remarks>
		public string Name
		{
			get
			{
#if WinCE
                string radioName = string.Empty;
                //get name from registry
                RegistryKey keyName = Registry.CurrentUser.OpenSubKey("\\Software\\Microsoft\\Bluetooth\\Settings");
                if (keyName != null)
                {
                    radioName = (string)keyName.GetValue("LocalName", string.Empty);
                    keyName.Close();
                }
                return radioName;
#else
				return radio.szName;
#endif
			}
            set
            {
#if WinCE
                RegistryKey keyName = Registry.CurrentUser.CreateSubKey("\\Software\\Microsoft\\Bluetooth\\Settings");
                if (keyName != null)
                {
                    keyName.SetValue("LocalName", value);
                    keyName.Close();
                }
#else
                //need a solution for XP - attached to the radio device
#endif
            }
		}
		#endregion

		#region Class Of Device
        /// <summary>
        /// Returns the Class of Device.
        /// </summary>
        public ClassOfDevice ClassOfDevice
        {
            get
            {
#if WinCE
                uint cod;
                int hresult = NativeMethods.BthReadCOD(out cod);
                if (hresult == 0)
                {
                    return new ClassOfDevice(cod);
                }
                else
                {
                    return new ClassOfDevice((uint)DeviceClass.Uncategorized);
                }          
#else
                return new ClassOfDevice(radio.ulClassofDevice);
#endif
            }
        }

		#endregion

		#region Manufacturer
#if WinCE
        private Manufacturer manufacturer;
#endif
		/// <summary>
		/// Returns the manufacturer of the <see cref="BluetoothRadio"/> device.
		/// </summary>
		public Manufacturer Manufacturer
		{
			get
			{
#if WinCE
                return manufacturer;
#else
				return radio.manufacturer;
#endif
			}
		}
        #endregion

        #region Lmp Subversion
#if WinCE
        private int lmpSubversion;
#endif
        /// <summary>
        /// Subversion of the current LMP in the <see cref="BluetoothRadio"/> device.
        /// </summary>
        public int LmpSubversion
        {
            get
            {
#if WinCE
                return lmpSubversion;
#else
                return radio.lmpSubversion;
#endif
            }
        }
        #endregion

        #region Stack
        /// <summary>
		/// Returns the manufacturer of the Bluetooth software stack running locally.
		/// Currently only Microsoft is supported.
		/// </summary>
		public Manufacturer SoftwareManufacturer
		{
			get
			{
				return Manufacturer.Microsoft;
			}
        }
        #endregion


        //events
#if WinCE
        /*private void EventThread()
        {
            int len = 72;
            IntPtr buffer = System.Runtime.InteropServices.Marshal.AllocHGlobal(len);
            int received = 0;
            int flags = 0;

            try
            {
                while (msgQueueHandle != IntPtr.Zero)
                {
                    bool success = NativeMethods.ReadMsgQueue(msgQueueHandle, buffer, len, out received, -1, out flags);
                    if (success)
                    {
                        NativeMethods.BTEVENT bte = (NativeMethods.BTEVENT)System.Runtime.InteropServices.Marshal.PtrToStructure(buffer, typeof(NativeMethods.BTEVENT));
                        switch (bte.dwEventId)
                        {
                            case NativeMethods.BTE.CONNECTION:
                                if (this.Connection != null)
                                {
                                    this.Connection(this, EventArgs.Empty);
                                }
                                break;
                            case NativeMethods.BTE.DISCONNECTION:
                                if (this.Disconnection != null)
                                {
                                    this.Disconnection(this, EventArgs.Empty);
                                }
                                break;
                            case NativeMethods.BTE.PAGE_TIMEOUT:
                                if (this.PageTimeout != null)
                                {
                                    this.PageTimeout(this, EventArgs.Empty);
                                }
                                break;
                        }
                    }

                }
            }
            finally
            {
                System.Runtime.InteropServices.Marshal.FreeHGlobal(buffer);
            }
        }*/
#endif

        //public event EventHandler Connection;
        //public event EventHandler Disconnection;
        //public event EventHandler PageTimeout;

#if WinXP
        /*private static NativeMethods.BluetoothMessageFilter bmf = new NativeMethods.BluetoothMessageFilter();

        public event EventHandler RadioInRange
        {
            add
            {
#if WinXP
                NativeMethods.DEV_BROADCAST_HANDLE dbh = new NativeMethods.DEV_BROADCAST_HANDLE();
                dbh.dbch_size = System.Runtime.InteropServices.Marshal.SizeOf(dbh);
                dbh.dbch_devicetype = NativeMethods.DBT_DEVTYP_HANDLE;
                dbh.dbch_handle = this.handle;
                dbh.dbch_eventguid = NativeMethods.GUID_BLUETOOTH_RADIO_IN_RANGE;
                System.Windows.Forms.Application.AddMessageFilter(bmf);
                int result = NativeMethods.RegisterDeviceNotification(System.Diagnostics.Process.GetCurrentProcess().MainWindowHandle, ref dbh, 0);
#endif
            }
            remove
            {
            }
        }*/
#endif
       

        #region IDisposable Members
        /*
        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        public void Dispose(bool disposing)
        {
#if WinCE
            if (notificationHandle != IntPtr.Zero)
            {
                NativeMethods.StopBluetoothNotifications(notificationHandle);
                notificationHandle = IntPtr.Zero;
            }
            if (msgQueueHandle != IntPtr.Zero)
            {
                NativeMethods.CloseMsgQueue(msgQueueHandle);
                msgQueueHandle = IntPtr.Zero;
            }
            
#endif
        }

        ~BluetoothRadio()
        {
            Dispose(false);
        }*/
        #endregion
    }
}
