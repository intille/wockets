using System;
using System.Collections;
using System.Threading;
using System.Diagnostics;
using Wockets.Utils.IPC;
using Wockets.Data.Types;
using Wockets.Data.Commands;
using Wockets.Kernel.Types;
using Wockets.Utils;
using Microsoft.Win32;
using Wockets.Data.Responses;
using Wockets.Data.Configuration;
using Wockets.Receivers;
using Wockets.Decoders.Accelerometers;
using Wockets.Sensors.Accelerometers;

namespace Wockets.Kernel
{
    public class Core
    {
        public static string REGISTRY_WOCKETS_PATH="Software\\MIT\\Wockets";
        public static string REGISTRY_REGISTERED_APPLICATIONS_PATH = REGISTRY_WOCKETS_PATH + "\\RegisteredApplications";
        public static string REGISTRY_SENSORS_PATH = REGISTRY_WOCKETS_PATH + "\\Sensors";
        public static string REGISTRY_DISCOVERED_SENSORS_PATH = REGISTRY_WOCKETS_PATH + "\\Discovered";
        public static string COMMAND_CHANNEL = Core.REGISTRY_WOCKETS_PATH + "\\Command";
        public static string REGISTRY_KERNEL_PATH = REGISTRY_WOCKETS_PATH + "\\Kernel";
        public static string REGISTRY_LOCK = "WocketsRLock";
        public static string KERNEL_PATH = @"\Program Files\wockets\";
        public static string KERNEL_EXECUTABLE = "Kernel.exe";
        public static string BROADCAST_EVENT_PREFIX = "WOCKET_BROADCAST_";
        private static Semaphore registryLock;
        public static bool _Registered = false;
        public static string _KernelGuid = null;
        public static bool _Connected = false;
        public static string storagePath = "";
        static Core()
        {
            registryLock = new Semaphore(1, 1, REGISTRY_LOCK);
        }

       public static bool _KernelStarted
        {
            get
            {
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(REGISTRY_KERNEL_PATH);
                int status =0;
                if (rk != null)
                {
                    status = (int)rk.GetValue("Status");
                    rk.Close();
                }
                registryLock.Release();
                return (status == 1);
            }
   
        }

       public static string _StoragePath
       {
           get
           {
               if (_Connected)
               {
                   if (storagePath == "")
                   {
                       registryLock.WaitOne();
                       RegistryKey rk = Registry.LocalMachine.OpenSubKey(REGISTRY_KERNEL_PATH);
                       storagePath = (string)rk.GetValue("Storage");       
                       rk.Close();
                       registryLock.Release();
                   }
             
               }
               else               
                   storagePath = "";               
               return storagePath;
           }
       }

       public static void InitializeConfiguration()
       {
           CurrentWockets._Configuration = new Wockets.Data.Configuration.WocketsConfiguration();           
           CurrentWockets._Configuration._ErrorWindowSize = 1000;
           CurrentWockets._Configuration._FeatureWindowOverlap = 0.5;
           CurrentWockets._Configuration._FeatureWindowSize = 1000;
           CurrentWockets._Configuration._FFTInterpolationPower = 7;
           CurrentWockets._Configuration._FFTMaximumFrequencies = 2;
           CurrentWockets._Configuration._MaximumConsecutivePacketLoss = 20;
           CurrentWockets._Configuration._MaximumNonconsecutivePacketLoss = 0.5;
           CurrentWockets._Configuration._SmoothWindowCount = 5;
           CurrentWockets._Configuration._MemoryMode = MemoryConfiguration.SHARED;
           CurrentWockets._Configuration._SoftwareMode = SoftwareConfiguration.DEBUG;

       }

       public static void InitializeController()
       {
           CurrentWockets._Controller = new WocketsController("", "", "");
           CurrentWockets._Controller._Mode = Wockets.MemoryMode.SharedToLocal;
           CurrentWockets._Controller._Receivers = new Wockets.Receivers.ReceiverList();


           RegistryKey rk = null;
           registryLock.WaitOne();
           for (int i = 0; (i < 5); i++)
           {
               try
               {
                   rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                   int status = (int)rk.GetValue("Status");
                   if (status == 1)
                   {
                       string mac = (string)rk.GetValue("MacAddress");
                       RFCOMMReceiver receiver = new RFCOMMReceiver();
                       receiver._ID = 0;
                       receiver._Address = mac;
                       CurrentWockets._Controller._Receivers.Add(receiver);
                       WocketsDecoder decoder = new WocketsDecoder();
                       decoder._ID = 0;
                       CurrentWockets._Controller._Decoders.Add(decoder);
                       Wocket wocket = new Wocket();
                       wocket._ID = 0;
                       wocket._Loaded = true;
                       wocket._Decoder = decoder;
                       wocket._Receiver = receiver;
                       CurrentWockets._Controller._Sensors.Add(wocket);

                   }
                   rk.Close();
               }
               catch
               {
               }
           }
           registryLock.Release();

          
           CurrentWockets._Controller.Initialize();
       }
        public static void Start()
        {
          
            if (!_KernelStarted)
            {
                System.Diagnostics.Process po = new System.Diagnostics.Process();
                ProcessStartInfo startInfo = new ProcessStartInfo();
                //startInfo.
                startInfo.WorkingDirectory = KERNEL_PATH;
                startInfo.FileName = KERNEL_PATH + "\\" + KERNEL_EXECUTABLE;
                startInfo.UseShellExecute = false;
                po.StartInfo = startInfo;
                po.Start();
            }
        }

        public static bool Terminate()
        {

            storagePath = "";
            Core.Send(KernelCommand.TERMINATE, "any");
            Thread.Sleep(2000);

            //If termination failed try killing the process
            if (_KernelStarted)
            {

                try
                {
                    ProcessInfo[] processes = ProcessCE.GetProcesses();
                    if (processes != null)
                    {
                        for (int i = 0; (i < processes.Length); i++)
                        {
                            if (processes[i].FullPath.IndexOf("Kernel.exe") >= 0)
                            {
                                processes[i].Kill();
                                break;
                            }
                        }

                        // registry is corrupt fix it
                        RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
                        rk.SetValue("Status", 0, RegistryValueKind.DWord);
                        rk.Close();      
                    }
                }
                catch
                {
                    if (_KernelStarted)
                        return false;
                }
            }

            return true;
        }
        public static void Send(KernelCommand command,string senderGuid)
        {
            NamedEvents namedEvent = new NamedEvents();
            registryLock.WaitOne();
            RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
            rk.SetValue("Message", command.ToString(), RegistryValueKind.String);
            rk.SetValue("Param", senderGuid.ToString(), RegistryValueKind.String);
            rk.Flush();
            rk.Close();
            registryLock.Release();
            namedEvent.Send(Channels.COMMAND.ToString());
        }

        public static void SetSensors(string channel, ArrayList s)
        {
            if ((_Registered) && (!_Connected))
            {              
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKETS.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                for (int i = 0; (i < 5); i++)
                {
                    rk = Registry.LocalMachine.CreateSubKey(REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                    if (s.Count > i)
                    {
                        rk.SetValue("MacAddress", (string)s[i], RegistryValueKind.String);
                        rk.SetValue("Status", 1, RegistryValueKind.DWord);
                    }
                    else
                        rk.SetValue("Status", 0, RegistryValueKind.DWord);
                    rk.Flush();
                    rk.Close();
                }
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
            }
        }


        public static bool Disconnect(string channel)
        {
            bool success = false;
            if (_Registered)
            {
                storagePath = "";
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();

                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.DISCONNECT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
               
            }
            return success;
        }
        
        public static bool Connect(string channel)
        {
            bool success = false;
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.CONNECT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
            }
            return success;
        }
        public static bool Register()
        {

            NamedEvents namedEvent = new NamedEvents();
            string guid= Guid.NewGuid().ToString();
            bool success = false;
            
            registryLock.WaitOne();
            RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
            rk.SetValue("Message", KernelCommand.REGISTER.ToString(), RegistryValueKind.String);
            rk.SetValue("Param", guid.ToString(), RegistryValueKind.String);
            rk.Flush();
            rk.Close();
            registryLock.Release();

            namedEvent.Send(Channels.COMMAND.ToString());

            int count = 0;
            while (true)
            {
                rk = Registry.LocalMachine.OpenSubKey(REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + guid + "}");
                if (rk != null)
                {
                    success = true;
                    rk.Close();
                    break;
                }
                Thread.Sleep(1000);
                count++;
                if (count == 10)
                    break;
            }
            if (success)
            {
                _Registered = true;
               _KernelGuid = guid;
                return true;
            }
            else
                return false;
        }

        public static bool Unregister(string guid)
        {
            bool success = false;
            if (_Registered)
            {
                NamedEvents namedEvent = new NamedEvents();               
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                rk.SetValue("Message", KernelCommand.UNREGISTER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", guid.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Channels.COMMAND.ToString());
                _Registered = false;
            }
            return success;
        }

        public static bool GET_BATTERY_LEVEL(string channel,string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_BATTERY_LEVEL.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();   
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static void WRITE_BATTERY_LEVEL(BL_RSP bl)
        {
            try
            {                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + bl._SensorID.ToString("0"));
                rk.SetValue("BATTERY_LEVEL", bl._BatteryLevel, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();                
            }
            catch
            {
                registryLock.Release();
            }
        }
        public static Hashtable READ_BATTERY_LEVEL()
        {
            try
            {
                Hashtable blevels = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            int batteryLevel = Convert.ToInt32(rk.GetValue("BATTERY_LEVEL"));
                            string mac = (string)rk.GetValue("MacAddress");
                            blevels.Add(mac, batteryLevel);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (blevels.Count > 0)
                    return blevels;
                else
                    return null;
             
            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }

        public static bool GET_BATTERY_PERCENT(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_BATTERY_PERCENT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static void WRITE_BATTERY_PERCENT(BP_RSP bp)
        {
            try
            {            
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + bp._SensorID.ToString("0"));
                rk.SetValue("BATTERY_PERCENT", bp._Percent, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();
            }
            catch
            {
                registryLock.Release();
            }
        }

        public static Hashtable READ_BATTERY_PERCENT()
        {
            try
            {
                Hashtable bpercents = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            int batterypercent = Convert.ToInt32(rk.GetValue("BATTERY_PERCENT"));
                            string mac = (string)rk.GetValue("MacAddress");
                            bpercents.Add(mac, batterypercent);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (bpercents.Count > 0)
                    return bpercents;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }
        public static bool GET_PDU_COUNT(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_PDU_COUNT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static void WRITE_PDU_COUNT(PC_RSP pc)
        {
            try
            {                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + pc._SensorID.ToString("0"));
                rk.SetValue("PDU_COUNT", pc._Count, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();                
            }
            catch
            {
                registryLock.Release();
            }
        }
        public static Hashtable READ_PDU_COUNT()
        {
            try
            {
                Hashtable pducounts = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            int pducount = Convert.ToInt32(rk.GetValue("PDU_COUNT"));
                            string mac = (string)rk.GetValue("MacAddress");
                            pducounts.Add(mac, pducount);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (pducounts.Count > 0)
                    return pducounts;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }

        public static bool GET_WOCKET_SENSITIVITY(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_SENSITIVITY.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static void WRITE_SENSITIVITY(SENS_RSP sen)
        {
            try
            {                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sen._SensorID.ToString("0"));
                rk.SetValue("SENSITIVITY", sen._Sensitivity, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();

            }
            catch
            {
                registryLock.Release();
            }
        }
        public static Hashtable READ_SENSITIVITY()
        {
            try
            {
                Hashtable sensitivities = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            Sensitivity s = (Sensitivity)Enum.Parse(typeof(Sensitivity), (string)rk.GetValue("SENSITIVITY"), true);
                            string mac = (string)rk.GetValue("MacAddress");
                            sensitivities.Add(mac, s);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (sensitivities.Count > 0)
                    return sensitivities;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }

        public static bool SET_WOCKET_SENSITIVITY(string channel, string mac,Sensitivity sensitivity)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_SENSITIVITY.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString()+":"+sensitivity.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static bool GET_WOCKET_CALIBRATION(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_CALIBRATION.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }


        public static void WRITE_CALIBRATION(CAL_RSP cal)
        {
            try
            {                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + cal._SensorID.ToString("0"));
                rk.SetValue("_X1G", cal._X1G, RegistryValueKind.String);
                rk.SetValue("_XN1G", cal._XN1G, RegistryValueKind.String);
                rk.SetValue("_Y1G", cal._Y1G, RegistryValueKind.String);
                rk.SetValue("_YN1G", cal._YN1G, RegistryValueKind.String);
                rk.SetValue("_Z1G", cal._Z1G, RegistryValueKind.String);
                rk.SetValue("_ZN1G", cal._ZN1G, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();                
            }
            catch
            {
                registryLock.Release();
            }
        }

        public static Hashtable READ_CALIBRATION()
        {
            try
            {
                Hashtable calibrations = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            Calibration calibration = new Calibration();
                            calibration._X1G=(ushort) Convert.ToUInt16(rk.GetValue("_X1G"));
                            calibration._XN1G = (ushort)Convert.ToUInt16(rk.GetValue("_XN1G"));
                            calibration._Y1G = (ushort)Convert.ToUInt16(rk.GetValue("_Y1G"));
                            calibration._YN1G = (ushort)Convert.ToUInt16(rk.GetValue("_YN1G"));
                            calibration._Z1G = (ushort)Convert.ToUInt16(rk.GetValue("_Z1G"));
                            calibration._ZN1G = (ushort)Convert.ToUInt16(rk.GetValue("_ZN1G"));
                            string mac = (string)rk.GetValue("MacAddress");
                            calibrations.Add(mac, calibration);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (calibrations.Count > 0)
                    return calibrations;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }

        public static bool SET_WOCKET_CALIBRATION(string channel, string mac, string calibration)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_BATTERY_PERCENT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString()+":"+calibration.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }


        public static bool GET_WOCKET_SAMPLING_RATE(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_SAMPLING_RATE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }


        public static bool SET_WOCKET_SAMPLING_RATE(string channel, string mac, int sr)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_SAMPLING_RATE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + sr.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static void WRITE_SAMPLING_RATE(SR_RSP sr)
        {
            try
            {    
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sr._SensorID.ToString("0"));
                rk.SetValue("SAMPLING_RATE", sr._SamplingRate, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();
             
            }
            catch
            {
                registryLock.Release();
            }
        }
        public static Hashtable READ_SAMPLING_RATE()
        {
            try
            {
                Hashtable srs = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            int sr = Convert.ToInt32((string)rk.GetValue("SAMPLING_RATE"));
                            string mac = (string)rk.GetValue("MacAddress");
                            srs.Add(mac, sr);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (srs.Count > 0)
                    return srs;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }

        public static void WRITE_ACTIVITY_COUNT(AC_RSP ac)
        {
            try
            {                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + ac._SensorID.ToString("0"));
                rk.SetValue("ACTIVITY_COUNT", ac._Count, RegistryValueKind.String);
                rk.Close();
                registryLock.Release();                
            }
            catch
            {
                registryLock.Release();
            }
        }

        public static Hashtable READ_ACTIVITY_COUNT()
        {
            try
            {
                Hashtable acs = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            int sr = Convert.ToInt32((string)rk.GetValue("ACTIVITY_COUNT"));
                            string mac = (string)rk.GetValue("MacAddress");
                            acs.Add(mac, sr);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (acs.Count > 0)
                    return acs;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }

        public static bool GET_WOCKET_POWERDOWN_TIMEOUT(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_POWERDOWN_TIMEOUT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }


        public static bool SET_WOCKET_POWERDOWN_TIMEOUT(string channel, string mac, int timeout)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_POWERDOWN_TIMEOUT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + timeout.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }




        public static bool GET_TRANSMISSION_MODE(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_TRANSMISSION_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }

        public static void WRITE_TRANSMISSION_MODE(TM_RSP tm)
        {
            try
            {                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + tm._SensorID.ToString("0"));
                rk.SetValue("TRANSMISSION_MODE", tm._TransmissionMode.ToString(), RegistryValueKind.String);
                rk.Close();
                registryLock.Release();                
            }
            catch
            {                
            }
        }

        public static Hashtable READ_TRANSMISSION_MODE()
        {
            try
            {
                Hashtable tms = new Hashtable();
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < 5); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            TransmissionMode tm = (TransmissionMode)Enum.Parse(typeof(TransmissionMode), (string)rk.GetValue("TRANSMISSION_MODE"), true);
                            string mac = (string)rk.GetValue("MacAddress");
                            tms.Add(mac, tm);

                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                if (tms.Count > 0)
                    return tms;
                else
                    return null;

            }
            catch
            {
                registryLock.Release();
            }
            return null;
        }


        public static bool SET_TRANSMISSION_MODE(string channel, string mac, TransmissionMode mode)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_TRANSMISSION_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + mode.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }


        public static bool GET_MEMORY_MODE(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_MEMORY_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }


        public static bool SET_MEMORY_MODE(string channel, string mac, MemoryMode mode)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_MEMORY_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + mode.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
        }
    }
}
