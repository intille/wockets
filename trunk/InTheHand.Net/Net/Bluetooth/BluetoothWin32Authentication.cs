using System;
using System.Runtime.InteropServices;
using InTheHand.Net.Sockets;

namespace InTheHand.Net.Bluetooth
{

    /// <summary>
    /// Provides Bluetooth authentication services on desktop Windows.
    /// </summary>
    /// -
    /// <remarks>
    /// <para>Respond to requests for authentication for Bluetooth devices.
    /// It is used by <see cref="T:InTheHand.Net.Sockets.BluetoothClient"/> to support
    /// its <see cref="P:InTheHand.Net.Sockets.BluetoothClient.Pin"/> property, in
    /// that case an instance is created specifying the device that is being connected
    /// to and the PIN string to use.  It can also be used a mode where a user supplied
    /// callback will be called when any device requires authentication, see the
    /// example below.
    /// </para>
    /// <para>The callback mode can be configured to do a callback after the 
    /// &#x2018;send PIN&#x2019;action, this allows one to see if it was successful 
    /// etc.  An example sequence where the PIN was <strong>incorrect</strong> is as follows.
    /// </para>
    /// <code>
    ///Authenticate one device -- with wrong passcode here the first two times.
    ///Passcode respectively: 'BAD-x', 'BAD-y', '9876'
    ///Making PC discoverable
    ///Hit Return to complete
    ///Authenticating 0017E464CF1E wm_alan1
    ///  Attempt# 0, Last error code 0
    ///  Sending "BAD-x"
    ///Authenticating 0017E464CF1E wm_alan1
    ///  Attempt# 1, Last error code 1244
    ///  Sending "BAD-y"
    ///Authenticating 0017E464CF1E wm_alan1
    ///  Attempt# 2, Last error code 1167
    ///  Sending "9876"
    ///Authenticating 0017E464CF1E wm_alan1
    ///  Attempt# 3, Last error code 1167
    ///etc
    ///</code>
    /// <para>
    /// That is we see the error code of <c>1244=NativeErrorNotAuthenticated</c>
    /// once, and then the peer device disappears (<c>1167=NativeErrorDeviceNotConnected</c>).
    /// I suppose that's a security feature -- its stops an attacker
    /// from trying again and again with different passcodes.
    ///
    /// Anyway the result of that is that is it <strong>not</strong> worth repeating 
    /// the callback after the device disappears.  The code now enforces this.  With 
    /// <see cref="P:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs.CallbackWithResult"/> 
    /// set to <c>true</c>, if the result of the previous attempt was &#x2018;success&#x2019; 
    /// or &#x2018;device not connected&#x2019; then any new PIN set in the callback 
    /// won&#x2019;t be used and thus the callback won&#x2019;t be called again 
    /// for that authentication attempt.
    /// </para>
    /// <para>A successful authentication process can thus be detected by checking if
    /// <code>e.PreviousNativeErrorCode == NativeErrorSuccess &amp;&amp; e.AttemptNumber != 0</code>
    /// </para>
    /// <para>
    /// </para>
    /// <para>The instance will continue receiving authentication requests
    /// until it is disposed or garbage collected, so keep a reference to it
    /// whilst it should be active and call 
    /// <see cref="M:InTheHand.Net.Bluetooth.BluetoothWin32Authentication.Dispose"/>
    /// when you&#x2019;re finished.
    /// </para>
    /// </remarks>
    /// -
    /// <example>
    /// If one wants to respond to PIN requests for one device with a known PIN then
    /// use the simple form which is initialized with an address and PIN.
    /// <code lang="C#">
    /// BluetoothWin32Authentication authenticator
    ///     = new BluetoothWin32Authentication(remoteEP.Address, m_pin);
    /// // when the peer is expected to require pairing, perhaps do some work.
    /// authenticator.Dispose();
    /// </code>
    /// 
    /// If one wants to see the PIN request, perhaps to be able to check the type
    /// of the peer by its address then use the form here which requests callbacks.
    /// <code lang="Visual Basic">
    /// Using pairer As New BluetoothWin32Authentication(AddressOf Win32AuthCallbackHandler)
    ///     Console.WriteLine("Hit Return to stop authenticating")
    ///     Console.ReadLine()
    /// End Using
    /// ...
    /// 
    /// Sub Win32AuthCallbackHandler(ByVal sender As Object, ByVal e As InTheHand.Net.Bluetooth.BluetoothWin32AuthentionEventArgs)
    ///    Dim address As String = e.Device.DeviceAddress.ToString()
    ///    Console.WriteLine("Received an authentication request from address " + address)
    ///    
    ///    ' compare the first 8 hex numbers, this is just a special case because in the
    ///    ' used scenario the model of the devices can be identified by the first 8 hex
    ///    ' numbers, the last 4 numbers being the device specific part.
    ///    If address.Substring(0, 8).Equals("0099880D") OrElse _
    ///            address.Substring(0, 8).Equals("0099880E") Then
    ///        ' send authentication response
    ///        e.Pin = "5276"
    ///    ElseIf (address.Substring(0, 8).Equals("00997788")) Then
    ///        ' send authentication response
    ///        e.Pin = "ásdfghjkl"
    ///    End If
    /// End Sub
    /// </code>
    /// </example>
    //[System.Security.Permissions.SecurityPermission(System.Security.Permissions.SecurityAction.Demand, UnmanagedCode = true)]
    public class BluetoothWin32Authentication : IDisposable
    {
        /// <summary>
        /// Windows&#x2019; ERROR_SUCCESS
        /// </summary>
        /// <remarks><see cref="P:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs.PreviousNativeErrorCode"/>
        /// </remarks>
        public const int NativeErrorSuccess = 0;

        /// <summary>
        /// Windows&#x2019; ERROR_NOT_AUTHENTICATED
        /// </summary>
        /// <remarks><see cref="P:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs.PreviousNativeErrorCode"/>
        /// </remarks>
        public const int NativeErrorNotAuthenticated = 1244; // ERROR_NOT_AUTHENTICATED

        /// <summary>
        /// Windows&#x2019; ERROR_DEVICE_NOT_CONNECTED
        /// </summary>
        /// <remarks><see cref="P:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs.PreviousNativeErrorCode"/>
        /// </remarks>
        public const int NativeErrorDeviceNotConnected = 1167; // ERROR_DEVICE_NOT_CONNECTED

        // This class is XP only, but XmlDocs generation is from CF2 only, so we need
        // to compile on that platform too.  So, leave the skeleton with no innards.
#if WinXP
        //
        readonly IntPtr m_radioHandle = IntPtr.Zero;
        BluetoothAuthenticationRegistrationHandle m_regHandle;
        NativeMethods.BluetoothAuthenticationCallback m_callback; // Stop gc of callback thunk.
        //
        BluetoothAddress m_remoteAddress;
        String m_pin;
        EventHandler<BluetoothWin32AuthenticationEventArgs> m_userCallback;
#endif

        //--------------------------------------------------------------

        /// <overloads>
        /// Initializes a new instance of the <see cref="T:BluetoothWin32Authentication"/> class.
        /// </overloads>
        /// -
        /// <summary>
        /// Initializes a new instance of the <see cref="T:BluetoothWin32Authentication"/> class,
        /// to respond to a specific address with a specific PIN string.
        /// </summary>
        /// -
        /// <remarks>
        /// <para>The instance will continue receiving authentication requests
        /// until it is disposed or garbage collected, so keep a reference to it
        /// whilst it should be active, and call 
        /// <see cref="M:InTheHand.Net.Bluetooth.BluetoothWin32Authentication.Dispose"/>
        /// when you&#x2019;re finished.
        /// </para>
        /// </remarks>
        /// -
        /// <param name="remoteAddress">The address of the device to authenticate,
        /// as a <see cref="T:InTheHand.Net.BluetoothAddress"/>.
        /// </param>
        /// <param name="pin">The PIN string to use for authentication, as a
        /// <see cref="T:System.String"/>.
        /// </param>
        public BluetoothWin32Authentication(BluetoothAddress remoteAddress, String pin)
        {
#if ! WinXP
            throw new PlatformNotSupportedException();
#else
            if (remoteAddress == null) {
                throw new ArgumentNullException("remoteAddress");
            }
            if (remoteAddress.ToInt64() == 0) {
                throw new ArgumentNullException("remoteAddress", "A non-blank address must be specified.");
            }
            if (pin == null) {
                throw new ArgumentNullException("pin");
            }
            m_remoteAddress = remoteAddress;
            m_pin = pin;
            Register(remoteAddress);
#endif
        }

        /// <summary>
        /// Initializes a new instance of the <see cref="T:BluetoothWin32Authentication"/> class,
        /// to call a specified handler when any device requires authentication.
        /// </summary>
        /// -
        /// <remarks>
        /// <para>See the example below.
        /// </para>
        /// <para>The callback mode can be configured to do a callback after the 
        /// &#x2018;send PIN&#x2019;action, this allows one to see if it was successful 
        /// etc.  An example sequence where the PIN was <strong>incorrect</strong> is as follows.
        /// </para>
        /// <code>
        ///Authenticate one device -- with wrong passcode here the first two times.
        ///Passcode respectively: 'BAD-x', 'BAD-y', '9876'
        ///Making PC discoverable
        ///Hit Return to complete
        ///Authenticating 0017E464CF1E wm_alan1
        ///  Attempt# 0, Last error code 0
        ///  Sending "BAD-x"
        ///Authenticating 0017E464CF1E wm_alan1
        ///  Attempt# 1, Last error code 1244
        ///  Sending "BAD-y"
        ///Authenticating 0017E464CF1E wm_alan1
        ///  Attempt# 2, Last error code 1167
        ///  Sending "9876"
        ///Authenticating 0017E464CF1E wm_alan1
        ///  Attempt# 3, Last error code 1167
        ///etc
        ///</code>
        /// <para>
        /// That is we see the error code of <c>1244=NativeErrorNotAuthenticated</c>
        /// once, and then the peer device disappears (<c>1167=NativeErrorDeviceNotConnected</c>).
        /// I suppose that's a security feature -- its stops an attacker
        /// from trying again and again with different passcodes.
        ///
        /// Anyway the result of that is that is it <strong>not</strong> worth repeating 
        /// the callback after the device disappears.  The code now enforces this.  With 
        /// <see cref="P:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs.CallbackWithResult"/> 
        /// set to <c>true</c>, if the result of the previous attempt was &#x2018;success&#x2019; 
        /// or &#x2018;device not connected&#x2019; then any new PIN set in the callback 
        /// won&#x2019;t be used and thus the callback won&#x2019;t be called again 
        /// for that authentication attempt.
        /// </para>
        /// <para>A successful authentication process can thus be detected by setting
        /// <c>CallbackWithResult=true</c> and checking in the callback if
        /// <code>  e.PreviousNativeErrorCode == NativeErrorSuccess &amp;&amp; e.AttemptNumber != 0</code>
        /// </para>
        /// <para>
        /// </para>
        /// <para>The instance will continue receiving authentication requests
        /// until it is disposed or garbage collected, so keep a reference to it
        /// whilst it should be active, and call 
        /// <see cref="M:InTheHand.Net.Bluetooth.BluetoothWin32Authentication.Dispose"/>
        /// when you&#x2019;re finished.
        /// </para>
        /// </remarks>
        /// -
        /// <param name="handler">A reference to a handler function that can respond
        /// to authentication requests.
        /// </param>
        /// -
        /// <example>
        /// <code lang="Visual Basic">
        /// Using pairer As New BluetoothWin32Authentication(AddressOf Win32AuthCallbackHandler)
        ///     Console.WriteLine("Hit Return to stop authenticating")
        ///     Console.ReadLine()
        /// End Using
        /// ...
        /// 
        /// Sub Win32AuthCallbackHandler(ByVal sender As Object, ByVal e As InTheHand.Net.Bluetooth.BluetoothWin32AuthentionEventArgs)
        ///    Dim address As String = e.Device.DeviceAddress.ToString()
        ///    Console.WriteLine("Received an authentication request from address " + address)
        ///    
        ///    ' compare the first 8 hex numbers, this is just a special case because in the
        ///    ' used scenario the model of the devices can be identified by the first 8 hex
        ///    ' numbers, the last 4 numbers being the device specific part.
        ///    If address.Substring(0, 8).Equals("0099880D") OrElse _
        ///            address.Substring(0, 8).Equals("0099880E") Then
        ///        ' send authentication response
        ///        e.Pin = "5276"
        ///    ElseIf (address.Substring(0, 8).Equals("00997788")) Then
        ///        ' send authentication response
        ///        e.Pin = "ásdfghjkl"
        ///    End If
        /// End Sub
        /// </code>
        /// </example>
        public BluetoothWin32Authentication(EventHandler<BluetoothWin32AuthenticationEventArgs> handler)
        {
#if ! WinXP
            throw new PlatformNotSupportedException();
#else
            m_userCallback = handler;
            Register(new BluetoothAddress(0)); // All devices
#endif
        }

#if WinXP
        private void Register(BluetoothAddress remoteAddress)
        {
            System.Diagnostics.Debug.Assert(m_pin == null ^ m_userCallback == null);
            //
            m_callback = new NativeMethods.BluetoothAuthenticationCallback(NativeCallback);
            BLUETOOTH_DEVICE_INFO bdi = new BLUETOOTH_DEVICE_INFO(remoteAddress);
            UInt32 ret = NativeMethods.BluetoothRegisterForAuthentication(
                ref bdi, out m_regHandle, m_callback, IntPtr.Zero);
            int gle = Marshal.GetLastWin32Error();
            System.Diagnostics.Debug.Assert(ret == NativeErrorSuccess,
                "BluetoothRegisterForAuthentication failed, GLE="
                + gle.ToString() + "=0x)" + gle.ToString("X"));
            if (ret != NativeErrorSuccess) {
                throw new System.ComponentModel.Win32Exception(gle);
            }
            m_regHandle.SetObjectToKeepAlive(m_callback);
        }

        //--------------------------------------------------------------
        private bool NativeCallback(IntPtr param, ref BLUETOOTH_DEVICE_INFO bdi)
        {
            System.Diagnostics.Debug.Assert(m_pin == null ^ m_userCallback == null);
            //
            System.Diagnostics.Debug.WriteLine(String.Format(
                    System.Globalization.CultureInfo.InvariantCulture,
                    "AuthenticateResponder callback (for {0}): 0x{1:X} 0x{2:X}",
                    m_remoteAddress, param, bdi.Address));
            //
            String pin;
            Int32 ret = NativeErrorSuccess;
            if (m_pin != null) {
                // Pre-specified case.
                System.Diagnostics.Debug.Assert(bdi.Address == m_remoteAddress.ToInt64(),
                    "Should only get callback for the single device.");
                //TODO if (bdi.Address != m_remoteAddress.ToInt64()) {
                //    return false;
                //}
                pin = m_pin;
                ret = NativeMethods.BluetoothSendAuthenticationResponse(
                    m_radioHandle, ref bdi, pin);
            } else {
                // Callback case.
                System.Diagnostics.Debug.Assert(m_userCallback != null);
                BluetoothWin32AuthenticationEventArgs e = new BluetoothWin32AuthenticationEventArgs(bdi);
                while (true) {
                    // Callback the user code
                    OnAuthentication(e);
                    // Don't proceed if no (null) passcode given, or
                    // if the last attempt was successful, or
                    // the decvice has disppeared.
                    if (e.Pin == null) {
                        break;
                    }
                    if (e.PreviousNativeErrorCode == NativeErrorSuccess && e.AttemptNumber != 0) {
                        break;
                    }
                    if (e.PreviousNativeErrorCode == NativeErrorDeviceNotConnected) {
                        // When I try this (against Win2k+Belkin and iPaq hx2190,
                        // both apparently with Broadcom) I see:
                        //[[
                        //Authenticate one device -- with wrong passcode here the first two times.
                        //Passcode respectively: 'BAD-x', 'BAD-y', '9876'
                        //Making PC discoverable
                        //Hit Return to complete
                        //Authenticating 0017E464CF1E wm_alan1
                        //  Attempt# 0, Last error code 0
                        //Using '0.23672947484847'
                        //Authenticating 0017E464CF1E wm_alan1
                        //  Attempt# 1, Last error code 1244
                        //Using '0.54782851764365'
                        //Authenticating 0017E464CF1E wm_alan1
                        //  Attempt# 2, Last error code 1167
                        //Using '9876'
                        //Authenticating 0017E464CF1E wm_alan1
                        //  Attempt# 3, Last error code 1167
                        //etc
                        //]]
                        // That is we see the error code of 1244=ErrorNotAuthenticated
                        // once, and then the peer device disappears (1167=ErrorDeviceNotConnected).
                        // I suppose that's a security feature -- its stops an attacker
                        // from trying again and again with different passcodes.
                        //
                        // Anyway the result of that is that is it NOT worth repeating
                        // the callback after the device disappears.
                        break;
                    }
                    pin = e.Pin;
                    System.Diagnostics.Debug.WriteLine(String.Format(System.Globalization.CultureInfo.InvariantCulture,
                        "BW32Auth SendAuthRsp pin {0}", pin));
                    ret = NativeMethods.BluetoothSendAuthenticationResponse(
                        m_radioHandle, ref bdi, pin);
                    if (ret != NativeErrorSuccess) {
                        System.Diagnostics.Trace.WriteLine(String.Format(
                            System.Globalization.CultureInfo.InvariantCulture,
                            "    BluetoothSendAuthenticationResponse failed: {0}=0x{0:X}", ret));
                    }
                    // Have to callback the user code after the attempt?
                    BluetoothWin32AuthenticationEventArgs lastEa = e;
                    if (!lastEa.CallbackWithResult) {
                        break;
                    }
                    e = new BluetoothWin32AuthenticationEventArgs(ret, lastEa);
                }
            }
            //
            if (ret != NativeErrorSuccess) {
                System.Diagnostics.Trace.WriteLine(String.Format(
                    System.Globalization.CultureInfo.InvariantCulture,
                    "BluetoothSendAuthenticationResponse failed: {0}=0x{0:X}", ret));
            }
            return true; // "The return value from this function is ignored by the system."
        }

        /// <summary>
        /// Calls the authentication callback handler.
        /// </summary>
        /// -
        /// <param name="e">An instance of <see cref="T:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs"/> 
        /// containingthe details of the authentication callback.
        /// </param>
        protected virtual void OnAuthentication(BluetoothWin32AuthenticationEventArgs e)
        {
            EventHandler<BluetoothWin32AuthenticationEventArgs> callback = m_userCallback;
            if (callback != null) {
                m_userCallback(this, e);
            }
        }
#endif
        //--------------------------------------------------------------

        #region IDisposable Members
        /// <summary>
        /// Release the unmanaged resources used by the <see cref="T:BluetoothWin32Authentication"/>.
        /// </summary>
        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        /// <summary>
        /// Release the unmanaged resources used by the <see cref="T:BluetoothWin32Authentication"/>,
        /// and optionally disposes of the managed resources.
        /// </summary>
        protected virtual void Dispose(bool disposing)
        {
#if WinXP
            if (disposing) {
                if (m_regHandle != null) {
                    m_regHandle.Dispose();
                }
            }
#endif
        }
        #endregion

    }//class

#if WinXP
    // Or should we derive from Microsoft.Win32.SafeHandles.SafeHandleMinusOneIsInvalid?
    internal class BluetoothAuthenticationRegistrationHandle
        : Microsoft.Win32.SafeHandles.SafeHandleZeroOrMinusOneIsInvalid
    {
        object m_objectToKeepAlive;
#if DEBUG
        WeakReference m_weakRef;
#endif

        public BluetoothAuthenticationRegistrationHandle()
            : base(true)
        { }

        protected override bool ReleaseHandle()
        {
            bool success = NativeMethods.BluetoothUnregisterAuthentication(handle);
            int gle = Marshal.GetLastWin32Error();
            System.Diagnostics.Debug.Assert(success,
                "BluetoothUnregisterAuthentication returned false, GLE="
                + gle.ToString() + "=0x)" + gle.ToString("X"));
#if DEBUG
            System.Diagnostics.Debug.Assert((m_weakRef == null) == (m_objectToKeepAlive == null),
                "Only one of the two objects set.");
            if (m_weakRef != null) {
                bool isAlive = m_weakRef.IsAlive;
                System.Diagnostics.Debug.Assert(isAlive, "m_weakRef.IsAlive");
            }
#endif
            return success;
        }

        internal void SetObjectToKeepAlive(object objectToKeepAlive)
        {
            m_objectToKeepAlive = objectToKeepAlive;
#if DEBUG
            m_weakRef = new WeakReference(m_objectToKeepAlive);
#endif
        }

    }//class
#endif


    /// <summary>
    /// Provides data for an authentication event.
    /// </summary>
    /// -
    /// <remarks>
    /// <para>For usage information, see the class documentation at
    /// <see cref="T:InTheHand.Net.Bluetooth.BluetoothWin32Authentication"/> it includes
    /// an example, 
    /// also see the documentation on each of this class&#x2019;s properties.
    /// </para>
    /// </remarks>
    public class BluetoothWin32AuthenticationEventArgs : EventArgs
    {
        BluetoothDeviceInfo m_device;
        string m_pin;
        //
        bool m_callbackWithResult;
        int m_attemptNumber;
        int m_errorCode;

        //--------------------------------------------------------------

        /// <summary>
        /// Initialize an instance of <see cref="T:BluetoothWin32AuthentionEventArgs"/>.
        /// </summary>
        public BluetoothWin32AuthenticationEventArgs()
        { }

        /// <summary>
        /// Initialize an instance of <see cref="T:BluetoothWin32AuthentionEventArgs"/>.
        /// </summary>
        public BluetoothWin32AuthenticationEventArgs(BluetoothDeviceInfo device)
        {
            if (device == null) {
                throw new ArgumentNullException("device");
            }
            m_device = device;
        }

        internal BluetoothWin32AuthenticationEventArgs(BLUETOOTH_DEVICE_INFO device)
        {
            m_device = new BluetoothDeviceInfo(device);
        }

        internal BluetoothWin32AuthenticationEventArgs(int errorCode, BluetoothWin32AuthenticationEventArgs previousEa)
        {
            if (previousEa == null) {
                throw new ArgumentNullException("previousEa");
            }
            m_device = previousEa.Device;
            m_attemptNumber = previousEa.AttemptNumber + 1;
            //
            m_errorCode = errorCode;
        }

        //--------------------------------------------------------------
        /// <summary>
        /// Gets the device requiring an authentication response as a
        /// <see cref="T:InTheHand.Net.Sockets.BluetoothDeviceInfo"/>.
        /// </summary>
        public BluetoothDeviceInfo Device { get { return m_device; } }

        /// <summary>
        /// Gets or sets the PIN string to be used to authenticate the specified device.
        /// </summary>
        /// -
        /// <remarks>On an authentication event, a PIN response is sent if the value 
        /// returned from the handler is not <see langword="null"/>.
        /// </remarks>
        public string Pin
        {
            get { return m_pin; }
            set
            {
                // ????
                //if (CannotSendAnotherResponse_) {
                //    throw new InvalidOperationException();
                //}
                m_pin = value;
            }
        }

        //****

        /// <summary>
        /// Gets or sets whether the callback is called again after the PIN response
        /// is sent.
        /// </summary>
        /// -
        /// <remarks><para>This is useful to see the error code returned by sending
        /// the PIN response. It can thus also be used to see the successful result 
        /// of sending the PIN response.  See the documentation on the 
        /// <see cref="T:InTheHand.Net.Bluetooth.BluetoothWin32Authentication"/> class.
        /// </para>
        /// </remarks>
        [System.Diagnostics.CodeAnalysis.SuppressMessage("Microsoft.Naming", "CA1704:IdentifiersShouldBeSpelledCorrectly", MessageId = "Callback")]
        public bool CallbackWithResult
        {
            get { return m_callbackWithResult; }
            set { m_callbackWithResult = value; }
        }

        /// <summary>
        /// Gets how many attempts at sending a PIN have been tried.
        /// </summary>
        /// <remarks>
        /// When there&#x2019;s a new PIN request, the first time the callback is
        /// called this property will have value zero.  If the PIN is rejected and
        /// <see cref="P:InTheHand.Net.Bluetooth.BluetoothWin32AuthenticationEventArgs.CallbackWithResult"/>
        /// was set, then the callback will be recalled and this property will have
        /// value one, etc.
        /// </remarks>
        public int AttemptNumber { get { return m_attemptNumber; } }

        /// <summary>
        /// The Windows error code returned by the last PIN response attempt.
        /// </summary>
        /// -
        /// <remarks><para>A bad PIN/passcode value appears to result in a error code
        /// with value 1244, which is <see cref="F:InTheHand.Net.Bluetooth.BluetoothWin32Authentication.NativeErrorNotAuthenticated"/>.
        /// </para>
        /// <para>If one tries to respond to that failure with another passcode,
        /// then error 1167 <see cref="F:InTheHand.Net.Bluetooth.BluetoothWin32Authentication.NativeErrorDeviceNotConnected"/>
        /// results.  So it seems that only one attempt is possible.
        /// </para>
        /// </remarks>
        public int PreviousNativeErrorCode { get { return m_errorCode; } }

        /// <summary>
        /// The Windows error code returned by the last PIN response attempt,
        /// as an unsigned value.
        /// </summary>
        /// -
        /// <remarks>See <see cref="P:PreviousNativeErrorCode"/>.
        /// </remarks>
        /// -
        /// <seealso cref="P:PreviousNativeErrorCode"/>
        [CLSCompliant(false)] // -> PreviousErrorCode
        public uint PreviousNativeErrorCodeAsUnsigned
        {
            get { return unchecked((uint)m_errorCode); }
        }

        /// <summary>
        /// Gets whether it is not possible to send another PIN response.
        /// </summary>
        /// <remarks><para>For instance, in testing it appears that after one response
        /// the device becomes non-contactable, any PIN response returning error code
        /// <see cref="F:InTheHand.Net.Bluetooth.BluetoothWin32Authentication.NativeErrorDeviceNotConnected"/>.
        /// </para>
        /// </remarks>
        public bool CannotSendAnotherResponse
        {
            get
            {
                return m_errorCode == BluetoothWin32Authentication.NativeErrorDeviceNotConnected;
            }
        }


        /// <exclude/>
        private const string ErrorMessageSendingAnotherPinIsDisallowed_
            = "It is disallowed to send another PIN response in this case.";

    }//class

}
