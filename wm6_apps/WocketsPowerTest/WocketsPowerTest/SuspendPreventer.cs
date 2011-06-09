using System;
using System.Runtime.InteropServices;//Dllimport
using System.Threading; //Timer
using System.Text; //StringBuilder


namespace Wockets
{
    /// <summary>
    /// In PocketPC devices, applications are "suspended" after some period of time, thereby 
    /// preventing background tasks, such as Sensors, from running; among many side-effects, 
    /// MyExperience cannot prompt the user, unless timed when the user is actively using the device;
    /// To prevent the device from going into a suspend state, this class uses a P/Invoke to call 
    /// SystemIdleTimerReset periodically. Because this call may put the device into a powerstate
    /// where the LCD remains on (and draining battery), this class also includes method calls
    /// to explicitly turn off the LCD _or_ to prevent that power state
    /// </summary>
    public class SuspendPreventer
    {
        private static Timer _timerReset;
        private static int _count = 0;
        private static TimeSpan _resetInterval = new TimeSpan(0, 0, 15); //frequency of reset
        private static bool _doesTurnOffDisplay = true;

        #region PROPERTIES
        /// <summary>
        /// Frequency of calling SystemIdleReset; should be less than timeout period on the device
        /// </summary>
        public static TimeSpan Interval
        {
            get { return _resetInterval; }
            set { _resetInterval = value; }
        }

        /// <summary>
        /// In some models, it may not be necessary to explicitly turn off display, 
        /// and may in fact be too agressive with turning off display; if notice that
        /// display gets turned off after 45 seconds even when user is still interacting
        /// with device, set to false
        /// </summary>
        public static bool DoesTurnOffDisplay
        {
            get { return _doesTurnOffDisplay; }
            set { _doesTurnOffDisplay = value; }
        }

        #endregion


        #region PUBLIC METHODS
        /// <summary>
        /// Start thread that will call "KeepAwake" method
        /// Call at start of application
        /// </summary>
        public static void Start()
        {
            //in some models, this call may allow SystemIdleTimerReset to switch directly to UnattendedMode instead of UserIdle Mode
            //Unattended mode keeps the system running, but has the backlight AND LCD off
            //UserIdle mode only turns the backlight off (keeps the LCD on and draining battery)
            PowerPolicyNotify(PowerMode.UnattendedMode, 1);

            TimerCallback tDelegate = new TimerCallback(timerReset_Tick);
            _timerReset = new Timer(tDelegate, null, 1000, 1000);

        }
        /// <summary>
        /// Stop thread that calls the "KeepAwake" method
        /// Call before exiting application
        /// </summary>
        public static void Stop()
        {
            PowerPolicyNotify(PowerMode.UnattendedMode, 0);

            if (_timerReset != null) _timerReset.Dispose();
        }
        #endregion


        #region PRIVATE METHODS
        static void timerReset_Tick(object stateInfo)
        {
            if (_count >= _resetInterval.TotalSeconds)
            {
                _count = 0;
                KeepAwake();

            }
            else _count++;
        }

        /// <summary>
        /// Makes a call to SystemIdleTimerReset to prevent the device from going into "suspend"
        /// </summary>
        private static void KeepAwake()
        {
            bool wasOn = true;

            //was display/power on? (i.e., is user actively using device?)
            //may always return false in some models (HTC Apache) - need to investigate
            if (_doesTurnOffDisplay) wasOn = IsDisplayOn(); 

            //SystemIdleReset, when used by itself, keeps the system from 
            //going into Suspend mode by keeping the phone in another 
            //power state. Used by itself, however, it may keep the device 
            //in UserIdle mode, which means the backlight is off, but the LCD is on 
            SystemIdleTimerReset();

            //SystemIdelTimerReset may keep the LCD on, draining battery
            //if display was off, before the call, turn off again
            //does not seem necessary for some models (HTC P3600), but is for others (HTC 3300)
            if (_doesTurnOffDisplay)
            {
                if (!wasOn) PowerOffDisplay(); //if display off, turn off again
            }
        }


        /// <summary>
        /// PInvokes GetSystemPowerState; 
        /// </summary>
        /// <returns>true if power state is "ON"; false if in other power state, such as user idle, unattended, backlight off, etc.</returns>
        private static bool IsDisplayOn()
        {
            StringBuilder sb = new StringBuilder();
            PowerState pps = new PowerState();
            GetSystemPowerState(sb.ToString(), (uint)sb.Capacity, out pps);

            return (pps.Equals(PowerState.POWER_STATE_POWERON) || pps.Equals(PowerState.POWER_STATE_ON));

        }

        ~SuspendPreventer()
        {
            Stop();
        }
        #endregion


        #region PINVOKE

        [DllImport("CoreDll.dll")]
        public static extern void PowerPolicyNotify(PowerMode powermode, int flags);

        [DllImport("coredll.dll")]
        extern static void SystemIdleTimerReset();

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int GetSystemPowerState(string psState, UInt32 dwLength, out PowerState flags);


        public enum PowerState
        {
            POWER_STATE_ON = 0x00010000,         // power state in P3600
            POWER_STATE_OFF = 0x00020000,
            POWER_STATE_CRITICAL = 0x00040000,
            POWER_STATE_BOOT = 0x00080000,
            POWER_STATE_IDLE = 0x00100000,         //---> screen off,  touch disabled
            POWER_STATE_SUSPEND = 0x00200000,
            POWER_STATE_UNATTENDED = 0x00400000,
            POWER_STATE_RESET = 0x00800000,
            POWER_STATE_USERIDLE = 0x01000000,     //---> user idle, screen off, but touch enabled
            POWER_STATE_PASSWORD = 0x10000000,     //---> resuming
            POWER_STATE_BACKLIGHTOFF = 0x10010000, //---> bkl-off
            POWER_STATE_POWERON = 0x12010000       // power state in P3300
        }

        public enum PowerMode
        {
            ReevaluateStat = 0x0001,
            PowerChange = 0x0002,
            UnattendedMode = 0x0003,
            SuspendKeyOrPwrButtonPressed = 0x0004,
            SuspendKeyReleased = 0x0005,
            AppButtonPressed = 0x0006
        }

        #endregion

        #region DISPLAY POWER
        /// Adapted from code:
        /// By Peter Foot, OpenNetCF (originally called Video)
        /// http://community.opennetcf.com/forums/t/774.aspx

        // GDI Escapes for ExtEscape()	
        private const uint QUERYESCSUPPORT = 8;
        // The following are unique to CE	
        private const uint GETVFRAMEPHYSICAL = 6144;
        private const uint GETVFRAMELEN = 6145;
        private const uint DBGDRIVERSTAT = 6146;
        private const uint SETPOWERMANAGEMENT = 6147;
        private const uint GETPOWERMANAGEMENT = 6148;

        private const uint VIDEOPOWERON = 1;
        private const uint VIDEOPOWERSTANDBY = 2;
        private const uint VIDEOPOWERSUSPEND = 3;
        private const uint VIDEOPOWEROFF = 4;

        private static void PowerOffDisplay()
        {
            IntPtr hdc = GetDC(IntPtr.Zero);
            uint func = SETPOWERMANAGEMENT;
            uint size = 12;
            byte[] vpm = new byte[size];
            //structure size		
            BitConverter.GetBytes(size).CopyTo(vpm, 0);
            //dpms version		
            BitConverter.GetBytes(0x0001).CopyTo(vpm, 4);
            //power state		
            BitConverter.GetBytes((uint)VIDEOPOWEROFF).CopyTo(vpm, 8);
            ExtEscapeSet(hdc, SETPOWERMANAGEMENT, size, vpm, 0, IntPtr.Zero);
        }

        private static void PowerOnDisplay()
        {
            IntPtr hdc = GetDC(IntPtr.Zero);
            uint size = 12;
            byte[] vpm = new byte[size];
            //structure size		
            BitConverter.GetBytes(size).CopyTo(vpm, 0);
            //dpms version		
            BitConverter.GetBytes(0x0001).CopyTo(vpm, 4);
            //power state		
            BitConverter.GetBytes((uint)VIDEOPOWERON).CopyTo(vpm, 8);
            ExtEscapeSet(hdc, SETPOWERMANAGEMENT, size, vpm, 0, IntPtr.Zero);
        }

        [DllImport("coredll", EntryPoint = "ExtEscape")]
        private static extern int ExtEscapeSet(IntPtr hdc, uint nEscape, uint cbInput, byte[] lpszInData, int cbOutput, IntPtr lpszOutData);

        [DllImport("coredll")]
        private static extern IntPtr GetDC(IntPtr hwnd);
        #endregion


    }


}
