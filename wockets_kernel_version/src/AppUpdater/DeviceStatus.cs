using System;
using System.Text; //StringBuilder
using Microsoft.WindowsMobile.Status;//SystemState Phone status
using System.Runtime.InteropServices; //PInvoke
using System.IO; //File.Exists, Path

namespace AppUpdater
{
    public class DeviceStatus
    {
        public static bool IsUserOnPhoneCall()
        {
            //Code based on Jon Froehlich's method in MyExperience
            return (SystemState.PhoneActiveCallCount > 0 ||
                SystemState.PhoneCallCalling ||
                SystemState.PhoneCallOnHold ||
                SystemState.PhoneCallTalking ||
                SystemState.PhoneIncomingCall);
        }

        public static bool IsDeviceCurrentlyIdle()
        {
            StringBuilder sb = new StringBuilder();
            PowerState pps = new PowerState();
            GetSystemPowerState(sb.ToString(), (uint)sb.Capacity, out pps);

            return (pps.Equals(PowerState.POWER_STATE_IDLE) || pps.Equals(PowerState.POWER_STATE_BACKLIGHTOFF) || pps.Equals(PowerState.POWER_STATE_UNATTENDED) || pps.Equals(PowerState.POWER_STATE_USERIDLE));
        }

        #region RESOLVE PATHS
        #region LOCATION OF FILE
        public static string LocationOfFile(string subpath)
        {
            return LocationOfFile(subpath, new string[0]);
        }
        public static string LocationOfFile(string subpath, string tryDirectory)
        {
            return LocationOfFile(subpath, new string[1] { tryDirectory });
        }
        public static string LocationOfFile(string subpath, string[] tryDirectories)
        {
            string pathResolved = "";

            //SupPath is actually full path
            if (File.Exists(subpath)) pathResolved = subpath;
            else
            {
                subpath = subpath.Trim('\\');

                string pathOption;
                if (tryDirectories != null)
                {
                    int d = 0;
                    while ((d < tryDirectories.Length) && (pathResolved.Length == 0))
                    {
                        pathOption = Path.Combine(tryDirectories[d], subpath);
                        if (File.Exists(pathOption)) pathResolved = pathOption;
                        else d++;
                    }
                }

                if (pathResolved.Length == 0)
                {
                    //File on device in Program Files folder
                    pathOption = Path.Combine("\\Program Files", subpath);
                    if (File.Exists(pathOption)) pathResolved = pathOption;
                    else
                    {
                        //File on device in root folder
                        pathOption = Path.Combine("\\", subpath);
                        if (File.Exists(pathOption)) pathResolved = pathOption;
                        else
                        {
                            //File on storage card in Program Files folder
                            pathOption = Path.Combine("\\Storage Card\\Program Files", subpath);
                            if (File.Exists(pathOption)) pathResolved = pathOption;
                            else
                            {
                                //File on storage card at root level
                                pathOption = Path.Combine("\\Storage Card", subpath);
                                if (File.Exists(pathOption)) pathResolved = pathOption;
                            }
                        }
                    }
                }
            }

            return pathResolved;
        }
        #endregion

        #region LOCATION OF DIRECTORY
        public static string LocationOfDirectory(string subpath)
        {
            return LocationOfDirectory(subpath, new string[0]);
        }
        public static string LocationOfDirectory(string subpath, string tryDirectory)
        {
            return LocationOfDirectory(subpath, new string[1] { tryDirectory });
        }
        public static string LocationOfDirectory(string subpath, string[] tryDirectories)
        {
            string pathResolved = "";

            //SupPath is actually full path
            if (Directory.Exists(subpath)) pathResolved = subpath;
            else
            {
                subpath = subpath.Trim('\\');

                string pathOption;
                if (tryDirectories != null)
                {
                    int d = 0;
                    while ((d < tryDirectories.Length) && (pathResolved.Length == 0))
                    {
                        pathOption = Path.Combine(tryDirectories[d], subpath);
                        if (Directory.Exists(pathOption)) pathResolved = pathOption;
                        else d++;
                    }
                }

                if (pathResolved.Length == 0)
                {
                    //File on device in Program Files folder
                    pathOption = Path.Combine("\\Program Files", subpath);
                    if (Directory.Exists(pathOption)) pathResolved = pathOption;
                    else
                    {
                        //File on device in root folder
                        pathOption = Path.Combine("\\", subpath);
                        if (Directory.Exists(pathOption)) pathResolved = pathOption;
                        else
                        {
                            //File on storage card in Program Files folder
                            pathOption = Path.Combine("\\Storage Card\\Program Files", subpath);
                            if (Directory.Exists(pathOption)) pathResolved = pathOption;
                            else
                            {
                                //File on storage card at root level
                                pathOption = Path.Combine("\\Storage Card", subpath);
                                if (Directory.Exists(pathOption)) pathResolved = pathOption;
                            }
                        }
                    }
                }
            }

            return pathResolved;
        }
        #endregion
        #endregion

        #region PINVOKE
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
            POWER_STATE_BACKLIGHTOFF = 0x10010000, //---> backlight off, screen on
            POWER_STATE_POWERON = 0x12010000       // power state in P3300
        }

        #endregion
    }
}
