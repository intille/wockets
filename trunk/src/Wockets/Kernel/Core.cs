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

    /// <summary>
    /// This singelton class implements most of the functionality that will allow an application to talk to
    /// the wockets kernel using inter-process communication.
    /// </summary>
    public class Core       
    {
        public static string REGISTRY_WOCKETS_PATH="Software\\MIT\\Wockets";
        public static string REGISTRY_REGISTERED_APPLICATIONS_PATH = REGISTRY_WOCKETS_PATH + "\\RegisteredApplications";
        public static string REGISTRY_SENSORS_PATH = REGISTRY_WOCKETS_PATH + "\\Sensors";
        public static string REGISTRY_DISCOVERED_SENSORS_PATH = REGISTRY_WOCKETS_PATH + "\\Discovered";
        public static string COMMAND_CHANNEL = Core.REGISTRY_WOCKETS_PATH + "\\Command";
        public static string REGISTRY_KERNEL_PATH = REGISTRY_WOCKETS_PATH + "\\Kernel";
        public static string KERNEL_LOCK = "WocketsKLock";
        public static string KERNEL_PATH = @"\Program Files\wockets\";
        public static string KERNEL_EXECUTABLE = "Kernel.exe";
        public static string BROADCAST_EVENT_PREFIX = "WOCKET_BROADCAST_";

        /// <summary>
        /// A system-wide semaphore that serializes writes to the registry
        /// </summary>
        private static Semaphore kernelLock;

        /// <summary>
        /// Indicates if an application is registered with the wockets kernel. True if the application is registered otherwise
        /// false
        /// </summary>
        public static bool _Registered = false;        

        /// <summary>
        /// Indicates if the wockets current configuration is in connectable mode (i.e. either a wocket is connected or 
        /// attempting to connect). True if the wockets are connectable, otherwise false
        /// </summary>
        public static bool _Connected = false;

        /// <summary>
        /// Specifies the path where the wockets raw data is stored.
        /// </summary>
        public static string storagePath = "";

        /// <summary>
        /// A guid that uniquely identifies the incoming channel used by the kernel to send messages to the application
        /// </summary>
        public static string _IcomingChannel = null;

        /// <summary>
        /// A guid that uniquely identifies the outgoing channel used by the application to send messages to the kernel
        /// </summary>
        public static string _OutgoingChannel = null;

        /// <summary>
        /// Stores the different events that the kernel can send to the application
        /// </summary>
        private static Hashtable events = new Hashtable();

        /// <summary>
        /// Stores the different threads that the application have blocked on particular kernel events. These threads
        /// are always blocked waiting for system-wide events from the kernel
        /// </summary>
        private static Hashtable threads = new Hashtable();

        /// <summary>
        /// Stores the addresses of sensors that have been discovered by the kernel
        /// </summary>
        public static Hashtable _DiscoveredSensors = new Hashtable();


        /// <summary>
        /// Indicates if the kernel has been started. True if the kernel started, otherwise false
        /// </summary>
        public static bool _KernalStarted;

        /// <summary>
        /// A delegrate that is a place-holder for an application handler of kernel responses. Applications that want to
        /// capture responses from the kernel need to implement a handler with that particular signature
        /// </summary>
        /// <param name="rsp">A kernel response</param>
        public delegate void KernelResponseHandler(KernelResponse rsp);

        /// <summary>
        /// An array that can hold up to the maximum number of kernel response that an application might be interested in.
        /// </summary>
        protected static KernelResponseHandler[] delegates = new KernelResponseHandler[30];

        /// <summary>
        /// An array indicating if an application is interested in a particular kernel response
        /// </summary>
        protected static bool[] subscribed = new bool[] { false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false };

        /// <summary>
        /// Fires events based on kernel response events to subscribed event handlers that are provided by applications
        /// </summary>
        /// <param name="rsp">A kernel response</param>
        private static void FireEvent(KernelResponse rsp)
        {
            if (subscribed[(int)rsp])
                delegates[(int)rsp](rsp);
        }

        /// <summary>
        /// Allows applications to subscribe to specific kernel events
        /// </summary>
        /// <param name="type">The kernel event to subscribe to</param>
        /// <param name="handler">The event handler to be invoked once the event is fired</param>
        public static void SubscribeEvent(KernelResponse type, KernelResponseHandler handler)
        {
            subscribed[(int)type] = true;
            delegates[(int)type] = handler;

            Thread t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, type);
            t.Start();
            
        }

        /// <summary>
        /// Allows applications to unsubscribe to kernel events
        /// </summary>
        /// <param name="type">The kernel event to subscribe to</param>       
        public static void UnsubscribeEvent(KernelResponse type)
        {
            subscribed[(int)type] = false;
        }

        /// <summary>
        /// A static class constructor that initializes IPC, synchronization primitives and listener threads
        /// to kernel events
        /// </summary>
        static Core()
        {            
            kernelLock = new Semaphore(1, 1, KERNEL_LOCK);
            _IcomingChannel = Guid.NewGuid().ToString();
            _OutgoingChannel = _IcomingChannel + "-kernel";

            RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + Core._IcomingChannel + "}");
            rk.SetValue("Message", "", RegistryValueKind.String);
            rk.SetValue("Param", "", RegistryValueKind.String);
            rk.Close();

            Core.Ping();

/*            Thread t = new Thread(EventListener);
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

            t = new Thread(EventListener);
            threads.Add(t.ManagedThreadId, t);
            events.Add(t.ManagedThreadId, KernelResponse.PING_RESPONSE);
            t.Start();

            Thread.Sleep(1000);
            
            */
        }

        /// <summary>
        /// A destructor that releases kernel event listener threads
        /// </summary>
        ~Core()
        {
            foreach (Thread t in threads.Values)
            {
                try
                {
                    t.Abort();
                }
                catch { }
            }
        }

        /// <summary>
        /// Listens to kernel events, updates wockets objects with new information and fires events to any subscribers
        /// </summary>
        private static void EventListener()
        {
            int myid = System.Threading.Thread.CurrentThread.ManagedThreadId;
            KernelResponse myevent = (KernelResponse)events[myid];
            string eventName = Core._IcomingChannel +"-"+ myevent.ToString();
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
                    case (KernelResponse)KernelResponse.PING_RESPONSE:
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
                        kernelLock.WaitOne();
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
                        kernelLock.Release();
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

        /// <summary>
        /// Gets and sets the storage path for the wockets data
        /// </summary>
        public static string _StoragePath
        {
            get
            {
                kernelLock.WaitOne();
                try
                {
                    if (_Connected)
                    {
                        if (storagePath == "")
                        {
                            kernelLock.WaitOne();
                            RegistryKey rk = Registry.LocalMachine.OpenSubKey(REGISTRY_KERNEL_PATH);
                            storagePath = (string)rk.GetValue("Storage");
                            rk.Close();
                            kernelLock.Release();
                        }

                    }
                    else
                        storagePath = "";
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:_StoragePath:" + e.ToString());
                }
                kernelLock.Release();
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

        /// <summary>
        /// Spawns the kernel process if it is not started
        /// </summary>
        /// <returns>True on successful spawning, otherwise false</returns>
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

        /// <summary>
        /// Terminates the kernel process
        /// </summary>
        /// <returns>True if the kernel successfully terminated, otherwise false</returns>
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


        /// <summary>
        /// Sends kernel commands before an application registers (e.g. register) on the shared command channel
        /// </summary>
        /// <param name="command"></param>
        public static void Send(KernelCommand command)
        {
            NamedEvents namedEvent = new NamedEvents();
            kernelLock.WaitOne();
            RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
            rk.SetValue("Message", command.ToString(), RegistryValueKind.String);
            rk.SetValue("Param", Core.COMMAND_CHANNEL.ToString(), RegistryValueKind.String);
            rk.Flush();
            rk.Close();
            kernelLock.Release();
            namedEvent.Send(Channels.COMMAND.ToString());
        }

        
        /// <summary>
        /// Sends a request to the kernel to select a list of wockets
        /// </summary>
        /// <param name="s">a list of mac addresses</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool SetSensors(ArrayList s)
        {
            if ((Core._Registered) && (!Core._Connected) && (s.Count<=5))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                kernelLock.WaitOne();
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
                kernelLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                return true;
            }

            return false;
        }


        /// <summary>
        /// Sends a request to the kernel to disconnect from the currently connected wockets
        /// </summary>
        /// <returns>True if the request is successfully sent to the kernel, otherwise false</returns>
        public static bool Disconnect()
        {            
            if (_Registered)
            {
                storagePath = "";
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.DISCONNECT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                kernelLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                return true;               
            }
            return false;
        }

        /// <summary>
        /// Sends a request to the kernel to discover wockets
        /// </summary>
        /// <returns>True if the request is sent successfully, otherwise false</returns>
        public static bool Discover()
        {            
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();

                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.DISCOVER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                kernelLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                return true;
            }
            return false;
        }
        
        /// <summary>
        /// Sends a request to the kernel to connect to the currently selected wockets
        /// </summary>
        /// <returns>True if the request is sent successfully, otherwise false</returns>
        public static bool Connect()
        {            
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();                
                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.CONNECT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "all", RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                kernelLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                return true;
            }
            return false;
        }
        /// <summary>
        /// Sends a request to the kernel to register with it
        /// </summary>
        /// <returns>True if the application successfully sends the request, otherwise returns false</returns>
        public static bool Register()
        {
            if (_KernalStarted)
            {       
                NamedEvents namedEvent = new NamedEvents();                
                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                rk.SetValue("Message", KernelCommand.REGISTER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", _IcomingChannel.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                kernelLock.Release();
                namedEvent.Send(Channels.COMMAND.ToString());
                return true;
            }
            return false;           
        }


        public static bool Ping()
        {
            NamedEvents namedEvent = new NamedEvents();
            kernelLock.WaitOne();
            RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
            rk.SetValue("Message", KernelCommand.PING.ToString(), RegistryValueKind.String);
            rk.SetValue("Param", _IcomingChannel.ToString(), RegistryValueKind.String);
            rk.Flush();
            rk.Close();
            kernelLock.Release();
            namedEvent.Send(Channels.COMMAND.ToString());
            return true;
        }
        /// <summary>
        /// Sends a request to unregister the application with the kernel
        /// </summary>
        /// <returns>True if the application successfully sends the request, otherwise false</returns>
        public static bool Unregister()
        {            
            if (_Registered)
            {
                NamedEvents namedEvent = new NamedEvents();               
                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                rk.SetValue("Message", KernelCommand.UNREGISTER.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", Core._IcomingChannel.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                kernelLock.Release();
                namedEvent.Send(Channels.COMMAND.ToString());
                _Registered = false;
                return true;
            }
            return false;
        }

        /// <summary>
        /// Sends a request to the kernel to retrieve the battery level for a specific wocket
        /// </summary>
        /// <param name="mac">A wocket's mac address</param>
        /// <returns>True if the application successfully sends the request, otherwise false</returns>
        public static bool GET_BATTERY_LEVEL(string mac)
        {            
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                NamedEvents namedEvent = new NamedEvents();
                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.GET_BATTERY_LEVEL.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();   
                kernelLock.Release();
                namedEvent.Send(Core._OutgoingChannel);
                return true;
            }
            return false;
        }

        /// <summary>
        /// Writes a battery level value to the registry
        /// </summary>
        /// <param name="bl">Battery level response PDU</param>
        public static void WRITE_BATTERY_LEVEL(BL_RSP bl)
        {
            kernelLock.WaitOne();
            try
            {                
                
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + bl._SensorID.ToString("0"));
                rk.SetValue("BATTERY_LEVEL", bl._BatteryLevel, RegistryValueKind.String);
                rk.Close();                
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:WRITE_BATTERY_LEVEL: " + e.ToString());
            }
            kernelLock.Release();                
        }

        /// <summary>
        /// Reads battery levels from the registry and stores it in the singelton wockets controller
        /// </summary>
        /// <returns>True if battery levels are read, otherwise false</returns>
        public static bool READ_BATTERY_LEVEL()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;                
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
                success = true;
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs: READ_BATTERY_LEVEL: " + e.ToString());
            }

            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to get battery percent for a specific wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool GET_BATTERY_PERCENT(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();

                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_BATTERY_PERCENT.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs: GET_BATTERY_PERCENT: " + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Writes to the registry a battery percent
        /// </summary>
        /// <param name="bp">Battery percent response PDU</param>
        public static void WRITE_BATTERY_PERCENT(BP_RSP bp)        
        {
            kernelLock.WaitOne();
            try
            {                            
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + bp._SensorID.ToString("0"));
                rk.SetValue("BATTERY_PERCENT", bp._Percent, RegistryValueKind.String);
                rk.Close();                
            }
            catch(Exception e)
            {
                Logger.Error("Core.cs:WRITE_BATTERY_PERCENT:" + e.ToString());
            }

            kernelLock.Release();
        }


        /// <summary>
        /// Reads from the registry battery percents for the wockets
        /// </summary>
        /// <returns>True if battery percents are read and updated in the singelton wockets controller, otherwise false</returns>
        public static bool READ_BATTERY_PERCENT()
        {
            bool success = false;

            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;

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

                success = true;
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to get a PDU count
        /// </summary>
        /// <param name="mac">A mac address for a wocket</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool GET_PDU_COUNT(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_PDU_COUNT.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_PDU_COUNT:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Writes a packet count to the registry
        /// </summary>
        /// <param name="pc">Packet count response PDU</param>
        public static void WRITE_PDU_COUNT(PC_RSP pc)
        {
            kernelLock.WaitOne();
            try
            {                
                
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + pc._SensorID.ToString("0"));
                rk.SetValue("PDU_COUNT", pc._Count, RegistryValueKind.String);
                rk.Close();                
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:WRITE_PDU_COUNT:" + e.ToString());
            }
            kernelLock.Release();                
        }

        /// <summary>
        /// Reads packet count from the registry for the wockets and stores it in the wockets controller
        /// </summary>
        /// <returns>True if the PDU counts are read, otherwise false</returns>
        public static bool READ_PDU_COUNT()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;
                
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
                
                success = true;

            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_PDU_COUNT:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to get the wocket's sensitivity
        /// </summary>
        /// <param name="mac">The mac address for the wocket</param>
        /// <returns>True it the request is successfully sent, otherwise false</returns>
        public static bool GET_WOCKET_SENSITIVITY(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_WOCKET_SENSITIVITY.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_WOCKET_SENSITIVITY:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Writes the sensitivity of the wocket to the registry
        /// </summary>
        /// <param name="sen">Sensitivity response PDU</param>
        public static void WRITE_SENSITIVITY(SENS_RSP sen)
        {
            kernelLock.WaitOne();
            try
            {                
                
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sen._SensorID.ToString("0"));
                rk.SetValue("SENSITIVITY", sen._Sensitivity, RegistryValueKind.String);
                rk.Close();                

            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:WRITE_SENSITIVITY:" + e.ToString());
            }

            kernelLock.Release();
        }
        
        /// <summary>
        /// Reads the sensitivity of the wockets from the registries and loads it into the wockets controller
        /// </summary>
        /// <returns>True if the sensitivities are read from the registry, otherwise false</returns>
        public static bool READ_SENSITIVITY()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;                
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
                success = true;

            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_SENSITIVITY:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Sends a request to the kernel to set the wockets sensitivity
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="sensitivity">Sensitivity of the wocket</param>
        /// <returns>True if the request is sent successfully, otherwise false</returns>
        public static bool SET_WOCKET_SENSITIVITY(string mac,Sensitivity sensitivity)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();

                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.SET_WOCKET_SENSITIVITY.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString() + ":" + sensitivity.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();

                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:SET_WOCKET_SENSITIVITY:" + e.ToString());
            }
                
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to retrieve the wockets calibration values
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool GET_WOCKET_CALIBRATION(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();                    
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_WOCKET_CALIBRATION.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();                    
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_WOCKET_CALIBRATION:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Writes calibration values in the registry
        /// </summary>
        /// <param name="cal">Calibration response PDU</param>
        public static void WRITE_CALIBRATION(CAL_RSP cal)
        {
            kernelLock.WaitOne();
            try
            {                
                
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + cal._SensorID.ToString("0"));
                rk.SetValue("_X1G", cal._X1G, RegistryValueKind.String);
                rk.SetValue("_XN1G", cal._XN1G, RegistryValueKind.String);
                rk.SetValue("_Y1G", cal._Y1G, RegistryValueKind.String);
                rk.SetValue("_YN1G", cal._YN1G, RegistryValueKind.String);
                rk.SetValue("_Z1G", cal._Z1G, RegistryValueKind.String);
                rk.SetValue("_ZN1G", cal._ZN1G, RegistryValueKind.String);
                rk.Close();                
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:WRITE_CALIBRATION:" + e.ToString());
            }

            kernelLock.Release();                
        }

        /// <summary>
        /// Reads calibration values from the registry and loads them into the current wockets controller
        /// </summary>
        /// <returns>True if the registry is read successfully, otherwise false</returns>
        public static bool READ_CALIBRATION()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;
                for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                {
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                        int status = (int)rk.GetValue("Status");
                        if (status == 1)
                        {
                            ((Accelerometer)CurrentWockets._Controller._Sensors[i])._Calibration._X1G = (ushort)Convert.ToUInt16(rk.GetValue("_X1G"));
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

                success = true;

            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_CALIBRATION:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to set the calibration values for a wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        /// <param name="calibration">A string specifiying the calibration values</param>
        /// <returns>True if the request is sent successfully, otherwise false</returns>
        public static bool SET_WOCKET_CALIBRATION(string mac, string calibration)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();

                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_BATTERY_PERCENT.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString() + ":" + calibration.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();

                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:SET_WOCKET_CALIBRATION:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to get the sampling rate for a wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        /// <returns>True if the request is sent successfully, otherwise false</returns>
        public static bool GET_WOCKET_SAMPLING_RATE(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_WOCKET_SAMPLING_RATE.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_WOCKET_SAMPLING_RATE:"+e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Sends a request to the kernel to set a wocket's sampling rate
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="sr">Sampling rate of the wocket</param>
        /// <returns>True if the request is successfully sent to the kernel, otherwise false</returns>
        public static bool SET_WOCKET_SAMPLING_RATE(string mac, int sr)
        {
            bool success = false;
            kernelLock.WaitOne();

            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.SET_WOCKET_SAMPLING_RATE.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString() + ":" + sr.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:SET_WOCKET_SAMPLING_RATE:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Writes the sampling rate to the registry
        /// </summary>
        /// <param name="sr">Sampling rate response PDU</param>
        public static void WRITE_SAMPLING_RATE(SR_RSP sr)
        {
            kernelLock.WaitOne();
            try
            {                   
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sr._SensorID.ToString("0"));
                rk.SetValue("SAMPLING_RATE", sr._SamplingRate, RegistryValueKind.String);
                rk.Close();                            
            }
            catch (Exception    e)
            {
                Logger.Error("Core.cs:WRITE_SAMPLING_RATE:" + e.ToString());
            }
            kernelLock.Release();
        }

        /// <summary>
        /// Reads the sampling rate from the registry and loads it into the current wockets controller
        /// </summary>
        /// <returns>True if the read is successful, otherwise false</returns>
        public static bool READ_SAMPLING_RATE()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;                
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
                success = true;
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_SAMPLING_RATE:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Writes the activity count to the registry
        /// </summary>
        /// <param name="ac">Activity count response packet</param>
        public static void WRITE_ACTIVITY_COUNT(AC_RSP ac)
        {
            kernelLock.WaitOne();
            try
            {                
                
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + ac._SensorID.ToString("0"));
                rk.SetValue("ACTIVITY_COUNT", ac._Count, RegistryValueKind.String);
                rk.Close();
                
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:WRITE_ACTIVITY_COUNT:" + e.ToString());
            }

            kernelLock.Release();                
        }


        /// <summary>
        /// Reads the activity count for the wockets from the registry and loads it in the current wockets controller
        /// </summary>
        /// <returns>True if the request is successful, otherwise false</returns>
        public static bool READ_ACTIVITY_COUNT()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;                
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
                
                success = true;
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_ACTIVITY_COUNT:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Sends a request to the kernel to get the powerdown timeout for the wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool GET_WOCKET_POWERDOWN_TIMEOUT(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_WOCKET_POWERDOWN_TIMEOUT.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_WOCKET_POWERDOWN_TIMEOUT:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to set the wockets power down timeout
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="timeout">Timeout for powering down in ?</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool SET_WOCKET_POWERDOWN_TIMEOUT(string mac, int timeout)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.SET_WOCKET_POWERDOWN_TIMEOUT.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString() + ":" + timeout.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:SET_WOCKET_POWERDOWN_TIMEOUT:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Sends a request to the kernel to get the transmission mode
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool GET_TRANSMISSION_MODE( string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_TRANSMISSION_MODE.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_TRANSMISSION_MODE:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Writes transmission mode to the registry
        /// </summary>
        /// <param name="tm">Transmission Mode response PDU</param>
        public static void WRITE_TRANSMISSION_MODE(TM_RSP tm)
        {
            kernelLock.WaitOne();
            try
            {                
                
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + tm._SensorID.ToString("0"));
                rk.SetValue("TRANSMISSION_MODE", tm._TransmissionMode.ToString(), RegistryValueKind.String);
                rk.Close();
                
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:WRITE_TRANSMISSION_MODE:" + e.ToString());
            }
            kernelLock.Release();                
        }


        /// <summary>
        /// Reads the transmission mode from the registry and loads it in the current wockets controller
        /// </summary>
        /// <returns>True if the registry is successfully read, otherwise is false</returns>
        public static bool READ_TRANSMISSION_MODE()
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                RegistryKey rk = null;                
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
                success = true;
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:READ_TRANSMISSION_MODE:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Sends a request to the kernel to set the transmission mode of a wocket
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="mode">Mode of transmission</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool SET_TRANSMISSION_MODE(string mac, TransmissionMode mode)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();

                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.SET_TRANSMISSION_MODE.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString() + ":" + mode.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:SET_TRANSMISSION_MODE:" + e.ToString());
            }

            kernelLock.Release();
            return success;
        }


        /// <summary>
        /// Sends a request to the kernel to get the memory mode
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <returns>True if the request is successfully sent, otherwise false</returns>
        public static bool GET_MEMORY_MODE(string mac)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();

                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.GET_MEMORY_MODE.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();

                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:GET_MEMORY_MODE:" + e.ToString());
            }
            kernelLock.Release();
            return success;
        }

        /// <summary>
        /// Sends a request to the kernel to set the memory mode
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="mode">Memory mode</param>
        /// <returns>True if the request is sent successfully, otherwise false</returns>
        public static bool SET_MEMORY_MODE(string mac, MemoryMode mode)
        {
            bool success = false;
            kernelLock.WaitOne();
            try
            {
                if ((_Registered) && (_Connected))
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();

                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.SET_MEMORY_MODE.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", mac.ToString() + ":" + mode.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();

                    namedEvent.Send(Core._OutgoingChannel);
                    success = true;
                }
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:SET_MEMORY_MODE:" + e.ToString());
            }

            kernelLock.Release();
            return success;
        }
    }
}
