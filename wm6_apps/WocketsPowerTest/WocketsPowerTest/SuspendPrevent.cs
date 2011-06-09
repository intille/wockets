using System;
using System.Text; //StringBuilder
using System.Runtime.InteropServices;//Dllimport
using System.Windows.Forms; //Timer

namespace Wockets
{
    public class SuspendPrevent
    {
        private Timer timerReset = new Timer();
        private byte count = 0;
        private byte secInterval = 45; //45, 5

        private static IntPtr handle_bkl = IntPtr.Zero;
        private static IntPtr handle_blt = IntPtr.Zero;
        private static IntPtr handle_wifi = IntPtr.Zero;

        public SuspendPrevent()
        {
            timerReset.Tick += new EventHandler(timerReset_Tick);
            timerReset.Interval = 5000; //once every 5 seconds = 5000, 1000
        }

        public byte SecondInterval
        {
            get { return secInterval; }
            set { secInterval = value; }
        }

        public void Start()
        {
            PowerPolicyNotify(PowerMode.UnattendedMode, 1);
            timerReset.Enabled = true;
        }
        public void Stop()
        {
            PowerPolicyNotify(PowerMode.UnattendedMode, 0);
            timerReset.Enabled = false;
        }

        void timerReset_Tick(object sender, EventArgs e)
        {
            if (count >= secInterval)
            {
                count = 0;
                KeepAwake();

            }
            else count += 5;
        }

        /// <summary>
        /// Makes a call to SystemIdleTimerReset; if display was on before call, stays on; otherwise, turns off
        /// </summary>
        public static void KeepAwake()
        {
            SystemIdleTimerReset(); //turns on display by default, but not in P3600 phone

            //Turn off display in touch screen phone
            //bool on = IsDisplayOn(); //was display/power on?
            //if (!on) TurnOffDisplay(); //if display off, turn off again

            // Turn off display in phones with not touch screen 
            // turns display off, not touch screen
            //if (!on) SetSystemPowerState(null,PowerState.POWER_STATE_IDLE,0); 


        }

        /// <summary>
        /// Makes a call to GetSystemPower; if system power is on it stays on; otherwise, it goes to idle state 
        /// </summary>
        public void Test_SetDevicePower_ON()
        {
            bool on;
            bool is_power_on;

            // test the devices power
            on = IsDeviceOn("wifi");
            is_power_on = SetDevicePowerState("wifi", "ON");

            on = IsDeviceOn("backlight");
            is_power_on = SetDevicePowerState("backlight", "OFF");

            on = IsDeviceOn("bluetooth");
            is_power_on = SetDevicePowerState("bluetooth", "ON");


        }

        /// <summary>
        /// Makes a call to GetSystemPower; if system power is on it stays on; otherwise, it goes to idle state 
        /// </summary>
        public void Test_SetDevicePower_OFF()
        {
            bool on;
            bool is_power_on;

            // test the devices power
            on = IsDeviceOn("wifi");
            is_power_on = SetDevicePowerState("wifi", "OFF");

            on = IsDeviceOn("backlight");
            is_power_on = SetDevicePowerState("backlight", "ON");

            on = IsDeviceOn("bluetooth");
            is_power_on = SetDevicePowerState("bluetooth", "OFF");


        }

        ~SuspendPrevent()
        {
            Stop();
            timerReset.Dispose();
        }



        #region POWER MANAGEMENT

        #region PINVOKE
        [DllImport("coredll.dll")]
        extern static void SystemIdleTimerReset();

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int GetSystemPowerState(string psState, UInt32 dwLength, out PowerState flags);

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int SetSystemPowerState(string psState, PowerState stateflags, int options);

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int GetDevicePower(string psDevice, PowerStateRequirement dflags, out CEDEVICE_POWER_STATE device_state);

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int SetDevicePower(string psDevice, PowerStateRequirement dflags, CEDEVICE_POWER_STATE device_state);


        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int DevicePowerNotify(string psDevice, CEDEVICE_POWER_STATE device_state, PowerStateRequirement dflags);

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static IntPtr SetPowerRequirement(string psDevice, CEDEVICE_POWER_STATE device_state, PowerStateRequirement dflags, PowerState system_state, int sflags);

        [DllImport("coredll.dll", SetLastError = true)]
        extern private static int ReleasePowerRequirement(IntPtr device_handle);

        [DllImport("BthUtil.dll")]
        public static extern int BthGetMode(out RadioMode dwMode);

        [DllImport("BthUtil.dll")]
        public static extern int BthSetMode(RadioMode dwMode);


        [DllImport("CoreDll.dll")]
        public static extern void PowerPolicyNotify(PowerMode powermode, int flags);

        #endregion




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

        //
        // Power Requirement Flags
        //
        public enum PowerStateRequirement
        {
            POWER_NAME = 0x00000001,         // default
            POWER_FORCE = 0x00001000,
            POWER_DUMPDW = 0x00002000        // Calling CaptureDumpFileOnDevice() before entering this state.
        }


        public enum CEDEVICE_POWER_STATE
        {
            PwrDeviceUnspecified = -1,
            D0 = 0,  // on
            D1,      // low power
            D2,      // standby, system cannot wakeup the system
            D3,      // sleep, device can wakeup the system
            D4,      // off
            PwrDeviceMaximum
        }

        public enum RadioMode
        {
            Off = 0,
            Connectable = 1,
            Discoverable = 2
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

        private static void TurnOffDisplay()
        {
            DisplayPower.PowerOff();
        }



        /// <summary>
        /// PInvokes GetSystemPowerState; SetSystemPowerState 
        /// </summary>
        /// <returns>true if power state is "ON"; otherwise, current system power state is kept on
        /// 
        /// false if in other power state, such as user idle, unattended, backlight off, etc. 
        /// system power state is set to user idle or system idle(screen off)
        /// </returns>
        private static bool IsPowerOn()
        {
            bool is_power_on = true;
            StringBuilder sb = new StringBuilder();
            PowerState pps = new PowerState();


            GetSystemPowerState(sb.ToString(), (uint)sb.Capacity, out pps);


            if (!(pps.Equals(PowerState.POWER_STATE_POWERON) || pps.Equals(PowerState.POWER_STATE_ON)))
            {

                SetSystemPowerState(null, PowerState.POWER_STATE_IDLE, 0); // dispay and touch screen off
                //SetSystemPowerState(null, PowerState.POWER_STATE_USERIDLE, 0); // dispay off, touch screen on

                is_power_on = false;
            }

            return is_power_on;

        }



        /// <summary>
        /// PInvokes GetDevicePower; 
        /// </summary>
        /// <returns>true if device power state is "ON"; 
        /// false if in other power state, such as D1, D2,D3,D4 
        /// </returns>
        private static bool IsDeviceOn(string device_name)
        {
            string device;
            bool res = false;


            CEDEVICE_POWER_STATE dps = new CEDEVICE_POWER_STATE();
            dps = CEDEVICE_POWER_STATE.PwrDeviceUnspecified;

            // set the device driver name and get its current power state
            switch (device_name)
            {
                case "backlight": device = "BKL1:";
                    GetDevicePower(device.ToString(), PowerStateRequirement.POWER_NAME, out dps);
                    res = dps.Equals(CEDEVICE_POWER_STATE.D0);
                    break;

                case "wifi": device = "{98C5250D-C29A-4985-AE5F-AFE5367E5006}\\TNETW12511";
                    GetDevicePower(device.ToString(), PowerStateRequirement.POWER_NAME, out dps);
                    res = dps.Equals(CEDEVICE_POWER_STATE.D0);
                    break;

                case "bluetooth":
                    RadioMode mode;
                    BthGetMode(out mode);
                    res = (mode.Equals(RadioMode.Discoverable) | mode.Equals(RadioMode.Connectable));
                    break;

                default:
                    break;

            }

            return (res);

        }




        /// <summary>
        /// PInvokes GetDevicePower; SetDevicePower;DevicePowerNotify;
        /// </summary>
        /// <returns>true if device power state is "ON"; 
        /// false if in other power state, such as D1, D2,D3,D4 
        /// </returns>
        private static bool SetDevicePowerState(string device_name, string device_power_state)
        {
            string device;
            bool res = false;


            if (device_name == "backlight" | device_name == "wifi")
            {


                CEDEVICE_POWER_STATE dps_get = new CEDEVICE_POWER_STATE();
                CEDEVICE_POWER_STATE dps_set = new CEDEVICE_POWER_STATE();
                dps_get = CEDEVICE_POWER_STATE.PwrDeviceUnspecified;


                // specifies the desired power state
                if (device_power_state.Equals("ON"))
                { dps_set = CEDEVICE_POWER_STATE.D0; }
                else if (device_power_state.Equals("OFF"))
                { dps_set = CEDEVICE_POWER_STATE.D4; }
                else
                { dps_set = CEDEVICE_POWER_STATE.PwrDeviceUnspecified; }

                // specifies the device driver name
                if (device_name == "backlight")
                    device = "BKL1:";
                else if (device_name == "wifi")
                    device = "{98C5250D-C29A-4985-AE5F-AFE5367E5006}\\TNETW12511";
                else
                    device = "none";


                GetDevicePower(device.ToString(), PowerStateRequirement.POWER_NAME, out dps_get);

                // sets a specific power state
                DevicePowerNotify(device.ToString(), dps_set, PowerStateRequirement.POWER_NAME);
                SetDevicePower(device.ToString(), PowerStateRequirement.POWER_NAME, dps_set);

                GetDevicePower(device.ToString(), PowerStateRequirement.POWER_NAME, out dps_get);

                //check if device is on
                if (dps_get.Equals(CEDEVICE_POWER_STATE.D0))
                { res = true; }

            }
            else if (device_name == "bluetooth")
            {
                RadioMode mode;

                if (device_power_state == "ON")
                { BthSetMode(RadioMode.Discoverable); }
                else if (device_power_state == "OFF")
                { BthSetMode(RadioMode.Off); }

                BthGetMode(out mode);

                //check if power state is on
                if (mode.Equals(1) | mode.Equals(2))
                { res = true; }
            }

            return (res);

        }


        #endregion

    }
}