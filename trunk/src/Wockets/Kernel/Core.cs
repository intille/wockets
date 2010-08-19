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
        //public static string _KernelGuid = null;
        public static bool _Connected = false;
        public static string storagePath = "";
        public static string _IcomingChannel = null;
        public static string _OutgoingChannel = null;

        private static Hashtable events = new Hashtable();
        private static Hashtable threads = new Hashtable();
        public static Hashtable _DiscoveredSensors = new Hashtable();
        public static bool _KernalStarted;

        public delegate void KernelResponseHandler(KernelResponse rsp);
        protected static KernelResponseHandler[] delegates = new KernelResponseHandler[20];
        protected static bool[] subscribed = new bool[] { false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false };

        private static void FireEvent(KernelResponse rsp)
        {
            if (subscribed[(int)rsp])
                delegates[(int)rsp](rsp);
        }

        public static void SubscribeEvent(KernelResponse type, KernelResponseHandler handler)
        {
            subscribed[(int)type] = true;
            delegates[(int)type] = handler;
        }

        public static void UnsubscribeEvent(KernelResponse type, KernelResponseHandler handler)
        {
            subscribed[(int)type] = false;
        }

        static Core()
        {
            registryLock = new Semaphore(1, 1, REGISTRY_LOCK);
            _IcomingChannel = Guid.NewGuid().ToString();
            _OutgoingChannel = _IcomingChannel + "-kernel";

            Thread t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.STARTED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.REGISTERED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.UNREGISTERED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.STOPPED);
            t.Start();


            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.DISCOVERED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.CONNECTED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.DISCONNECTED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SENSORS_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.BATTERY_LEVEL_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.BATTERY_PERCENT_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.PC_COUNT_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SENSITIVITY_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.CALIBRATION_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.SAMPLING_RATE_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.TRANSMISSION_MODE_UPDATED);
            t.Start();

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.ACTIVITY_COUNT_UPDATED);
            t.Start();

        }

       /* static ~Core()
        {
            foreach (Thread t in threads.Values)
            {
                try
                {
                    t.Abort();
                }
                catch { }
            }
        }*/
        private static void EventListener()
        {
            int myid = System.Threading.Thread.CurrentThread.ManagedThreadId;
            KernelResponse myevent = (KernelResponse)events[myid];
            string eventName = Core.BROADCAST_EVENT_PREFIX + myevent.ToString();
            NamedEvents namedEvent = new NamedEvents();
            RegistryKey rk = null;
            while (true)
            {
                namedEvent.Receive(eventName);
                switch (myevent)
                {
                    case (KernelResponse)KernelResponse.STARTED:
                        Core._KernalStarted = true;
                        break;
                    case (KernelResponse)KernelResponse.REGISTERED:
                        _Registered = true;                        
                        break;
                    case (KernelResponse)KernelResponse.UNREGISTERED:
                        _Registered = false;
                        break;
                    case (KernelResponse)KernelResponse.STOPPED:
                        Core._KernalStarted = false;
                        break;
                    case (KernelResponse)KernelResponse.DISCOVERED:
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
                        if (rk != null)
                        {
                            string[] sensors = rk.GetSubKeyNames();
                            rk.Close();
                            _DiscoveredSensors.Clear();
                            if (sensors.Length > 0)
                            {
                                for (int i = 0; (i < sensors.Length); i++)
                                {

                                    rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH + "\\" + sensors[i]); ;
                                    _DiscoveredSensors.Add((string)rk.GetValue("Name"), (string)rk.GetValue("MacAddress"));
                                    rk.Close();
                                }
                            }
                        }
                        break;
                    case (KernelResponse)KernelResponse.SENSORS_UPDATED:
                        CurrentWockets._Controller = new WocketsController("", "", "");
                        CurrentWockets._Controller._Mode = Wockets.MemoryMode.SharedToLocal;
                        CurrentWockets._Controller._Receivers = new Wockets.Receivers.ReceiverList();
                        rk = null;
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
                        //CurrentWockets._Controller._Receivers.SortByAddress();
                        registryLock.Release();
                        break;
                    case (KernelResponse)KernelResponse.CONNECTED:
                        CurrentWockets._Controller.Initialize();
                        Core._Connected = true;
                        break;
                    case (KernelResponse)KernelResponse.DISCONNECTED:
                        Core._Connected = false;
                        break;
                    case (KernelResponse)KernelResponse.BATTERY_LEVEL_UPDATED:
                        Core.READ_BATTERY_LEVEL();
                        break;
                    case (KernelResponse)KernelResponse.BATTERY_PERCENT_UPDATED:
                        Core.READ_BATTERY_PERCENT();
                        break;
                    case (KernelResponse)KernelResponse.PC_COUNT_UPDATED:
                        Core.READ_PDU_COUNT();
                        break;
                    case (KernelResponse)KernelResponse.SENSITIVITY_UPDATED:
                        Core.READ_SENSITIVITY();
                        break;
                    case (KernelResponse)KernelResponse.CALIBRATION_UPDATED:
                        Core.READ_CALIBRATION(); 
                        break;

                    case (KernelResponse)KernelResponse.SAMPLING_RATE_UPDATED:
                        Core.READ_SAMPLING_RATE();
                        break;
                    case (KernelResponse)KernelResponse.TRANSMISSION_MODE_UPDATED:
                        Core.READ_TRANSMISSION_MODE();      
                        break;
                    case (KernelResponse)KernelResponse.ACTIVITY_COUNT_UPDATED:
                        Core.READ_ACTIVITY_COUNT();              
                        break;
                    default:
                        break;
                }

                FireEvent(myevent);
            }
        }

        /*  public static bool _KernelStarted
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
              set
              {
              }
   
          }
          */
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
 

          

       }
        public static bool Start()
        {          
            if (!Core._KernalStarted)
            {
                System.Diagnostics.Process po = new System.Diagnostics.Process();
                ProcessStartInfo startInfo = new ProcessStartInfo();
                //startInfo.
                startInfo.WorkingDirectory = KERNEL_PATH;
                startInfo.FileName = KERNEL_PATH + "\\" + KERNEL_EXECUTABLE;
                startInfo.UseShellExecute = false;
                po.StartInfo = startInfo;
                return po.Start();               
            }
            return false;
        }

        public static bool Terminate()
        {

            storagePath = "";
            Core.Send(KernelCommand.TERMINATE);
            Thread.Sleep(2000);

            //If termination failed try killing the process
            if (Core._KernalStarted)
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
                    if (Core._KernalStarted)
                        return false;
                }
            }

            return true;
        }
        public static void Send(KernelCommand command)
        {
            NamedEvents namedEvent = new NamedEvents();
            registryLock.WaitOne();
            RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
            rk.SetValue("Message", command.ToString(), RegistryValueKind.String);
            rk.SetValue("Param", Core.COMMAND_CHANNEL.ToString(), RegistryValueKind.String);
            rk.Flush();
            rk.Close();
            registryLock.Release();
            namedEvent.Send(Channels.COMMAND.ToString());
        }

        public static void SetSensors(ArrayList s)
        {
            if ((Core._Registered) && (!Core._Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
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
                namedEvent.Send(Core._OutgoingChannel);
            }
        }


        public static bool Disconnect()
        {
            bool success = false;
            if (_Registered)
            {
                storagePath = "";
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();

                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.DISCONNECT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
               
            }
            return success;
        }

        public static bool Discover()
        {
            bool success = false;
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();

                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.DISCOVER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
            }
            return success;
        }
        
        public static bool Connect()
        {
            bool success = false;
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.CONNECT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
            }
            return success;
        }
        public static bool Register()
        {
            if (_KernalStarted)
            {
                NamedEvents namedEvent = new NamedEvents();
                bool success = false;
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                rk.SetValue("Message", KernelCommand.REGISTER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", _IcomingChannel.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();

                namedEvent.Send(Channels.COMMAND.ToString());

                int count = 0;
                while (true)
                {
                    rk = Registry.LocalMachine.OpenSubKey(REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}");
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
                    _Registered = true;
            }
            return _Registered;           
        }

        public static bool Unregister()
        {
            bool success = false;
            if (_Registered)
            {
                NamedEvents namedEvent = new NamedEvents();               
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                rk.SetValue("Message", KernelCommand.UNREGISTER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", Core._IcomingChannel.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Channels.COMMAND.ToString());
                _Registered = false;
            }
            return success;
        }

        public static bool GET_BATTERY_LEVEL(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_BATTERY_LEVEL.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();   
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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
        public static bool READ_BATTERY_LEVEL()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)                        
                            CurrentWockets._Controller._Sensors[i]._BatteryLevel = Convert.ToInt32(rk.GetValue("BATTERY_LEVEL"));                                                    
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;             
            }
            catch
            {
                registryLock.Release();
            }
            return false;
        }

        public static bool GET_BATTERY_PERCENT(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_BATTERY_PERCENT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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

        public static bool READ_BATTERY_PERCENT()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                            CurrentWockets._Controller._Sensors[i]._BatteryPercent = Convert.ToInt32(rk.GetValue("BATTERY_PERCENT"));
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;
            }
            catch
            {
                registryLock.Release();
            }
            return true;
        }
        public static bool GET_PDU_COUNT(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_PDU_COUNT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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
        public static bool READ_PDU_COUNT()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                            CurrentWockets._Controller._Sensors[i]._PDUCount = Convert.ToInt32(rk.GetValue("PDU_COUNT"));                            
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;

            }
            catch
            {
                registryLock.Release();
            }
            return false;
        }

        public static bool GET_WOCKET_SENSITIVITY(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_SENSITIVITY.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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
        public static bool READ_SENSITIVITY()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Sensitivity = (Sensitivity)Enum.Parse(typeof(Sensitivity), (string)rk.GetValue("SENSITIVITY"), true);                                               
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;

            }
            catch
            {
                registryLock.Release();
            }
            return false;
        }

        public static bool SET_WOCKET_SENSITIVITY(string mac,Sensitivity sensitivity)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_SENSITIVITY.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString()+":"+sensitivity.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                success = true;
            }
            return success;
        }

        public static bool GET_WOCKET_CALIBRATION(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_CALIBRATION.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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

        public static bool READ_CALIBRATION()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._X1G=(ushort) Convert.ToUInt16(rk.GetValue("_X1G"));
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._XN1G = (ushort)Convert.ToUInt16(rk.GetValue("_XN1G"));
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._Y1G = (ushort)Convert.ToUInt16(rk.GetValue("_Y1G"));
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._YN1G = (ushort)Convert.ToUInt16(rk.GetValue("_YN1G"));
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._Z1G = (ushort)Convert.ToUInt16(rk.GetValue("_Z1G"));
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._ZN1G = (ushort)Convert.ToUInt16(rk.GetValue("_ZN1G"));
                        }
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;

            }
            catch
            {
                registryLock.Release();
            }
            return false;
        }

        public static bool SET_WOCKET_CALIBRATION(string channel, string mac, string calibration)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
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


        public static bool GET_WOCKET_SAMPLING_RATE(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_WOCKET_SAMPLING_RATE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                success = true;
            }
            return success;
        }


        public static bool SET_WOCKET_SAMPLING_RATE(string mac, int sr)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_SAMPLING_RATE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + sr.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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
        public static bool READ_SAMPLING_RATE()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)                        
                            CurrentWockets._Controller._Sensors[i]._SamplingRate = Convert.ToInt32((string)rk.GetValue("SAMPLING_RATE"));                                        
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;
            }
            catch
            {
                registryLock.Release();
            }
            return false;
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

        public static bool READ_ACTIVITY_COUNT()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._ActivityCount = Convert.ToInt32((string)rk.GetValue("ACTIVITY_COUNT"));                   
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();
                return true;
            }
            catch
            {
                registryLock.Release();
            }
            return false;
        }

        public static bool GET_WOCKET_POWERDOWN_TIMEOUT(string channel, string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
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


        public static bool SET_WOCKET_POWERDOWN_TIMEOUT(string mac, int timeout)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_POWERDOWN_TIMEOUT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + timeout.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                success = true;
            }
            return success;
        }




        public static bool GET_TRANSMISSION_MODE( string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_TRANSMISSION_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
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

        public static bool READ_TRANSMISSION_MODE()
        {
            try
            {
                RegistryKey rk = null;
                registryLock.WaitOne();
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                            ((Wocket)CurrentWockets._Controller._Sensors[i])._TransmissionMode = (TransmissionMode)Enum.Parse(typeof(TransmissionMode), (string)rk.GetValue("TRANSMISSION_MODE"), true);
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                registryLock.Release();

                return true;

            }
            catch
            {
                registryLock.Release();
            }
            return false;
        }


        public static bool SET_TRANSMISSION_MODE(string mac, TransmissionMode mode)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_TRANSMISSION_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + mode.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                success = true;
            }
            return success;
        }


        public static bool GET_MEMORY_MODE(string mac)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_MEMORY_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                success = true;
            }
            return success;
        }


        public static bool SET_MEMORY_MODE(string mac, MemoryMode mode)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_MEMORY_MODE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + mode.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                success = true;
            }
            return success;
        }
    }
}
