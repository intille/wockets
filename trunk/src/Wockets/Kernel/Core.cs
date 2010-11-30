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
using System.Threading;


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
            Core.KERNEL_PATH=System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase)+"\\";
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
                    case (KernelResponse)KernelResponse.TCT_UPDATED:
                        Core.READ_TCT();
                        break;
                    default:
                        break;
                }
                namedEvent.Reset();
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
  
                            RegistryKey rk = Registry.LocalMachine.OpenSubKey(REGISTRY_KERNEL_PATH);
                            storagePath = (string)rk.GetValue("Storage");
                            rk.Close();
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

       private static System.Diagnostics.Process _KernelProcess=null;
        /// <summary>
        /// Spawns the kernel process if it is not started
        /// </summary>
        /// <returns>True on successful spawning, otherwise false</returns>
        public static bool Start()
        {          
            if (!Core._KernalStarted)
            {
                try
                {
                    //System.Diagnostics.Process po = new System.Diagnostics.Process();
                    ProcessStartInfo startInfo = new ProcessStartInfo();
                    //startInfo.
                    startInfo.WorkingDirectory = KERNEL_PATH;
                    startInfo.FileName = KERNEL_PATH + KERNEL_EXECUTABLE;
                    //startInfo.FileName = startInfo.FileName;
                    startInfo.UseShellExecute = false;
                     //System.Diagnostics.Process.Start(
                    //po.StartInfo = startInfo;
                    return ((_KernelProcess=System.Diagnostics.Process.Start(startInfo.FileName, ""))!=null);
                }
                catch (Exception e)
                {
                    return false;
                }
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
            
          
           // kernelLock.WaitOne();
            try
            {
                NamedEvents namedEvent = new NamedEvents();
                /*RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                rk.SetValue("Message", KernelCommand.TERMINATE.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", Core._IcomingChannel.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();*/
                namedEvent.Send("TerminateKernel");
            }
            catch (Exception e)
            {
                Logger.Error("Core.cs:Terminate:" + e.ToString());
            }
            //kernelLock.Release();
       

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
                        RegistryKey rk1 = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
                        rk1.SetValue("Status", 0, RegistryValueKind.DWord);
                        rk1.Close();
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
        /// Sends a request to the kernel to select a list of wockets
        /// </summary>
        /// <param name="s">a list of mac addresses</param>
        public static void SetSensors(ArrayList s)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

                if ((Core._Registered) && (!Core._Connected) && (s.Count <= 5))
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
                }
                
            });

        }


        /// <summary>
        /// Sends a request to the kernel to disconnect from the currently connected wockets
        /// </summary>
        public static void Disconnect()
        {
            ThreadPool.QueueUserWorkItem(func =>
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
                }

            });
        }

        /// <summary>
        /// Sends a request to the kernel to discover wockets
        /// </summary>
        public static void Discover()
        {
            ThreadPool.QueueUserWorkItem(func =>
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
                }
            });
        }


        public static void Connect()
        {
            Connect(TransmissionMode.Continuous);
        }
        /// <summary>
        /// Sends a request to the kernel to connect to the currently selected wockets
        /// </summary>        
        public static void Connect(TransmissionMode tmode)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                if (_Registered)
                {
                    string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                    NamedEvents namedEvent = new NamedEvents();
                    kernelLock.WaitOne();
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                    rk.SetValue("Message", KernelCommand.CONNECT.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", "all", RegistryValueKind.String);
                    rk.SetValue("TMode",tmode.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    kernelLock.Release();
                    namedEvent.Send(Core._OutgoingChannel);
                }
            });
        }
        /// <summary>
        /// Sends a request to the kernel to register with it
        /// </summary>
        public static void Register()
        {
            ThreadPool.QueueUserWorkItem(func =>
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

                }
            });
        }

        /// <summary>
        /// Sends a request to the kernel to ping it
        /// </summary>
        public static void Ping()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

                NamedEvents namedEvent = new NamedEvents();
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(COMMAND_CHANNEL, true);
                    rk.SetValue("Message", KernelCommand.PING.ToString(), RegistryValueKind.String);
                    rk.SetValue("Param", _IcomingChannel.ToString(), RegistryValueKind.String);
                    rk.Flush();
                    rk.Close();
                    namedEvent.Send(Channels.COMMAND.ToString());
                }
                catch 
                { 
                }
                kernelLock.Release();                
            });

        }
        /// <summary>
        /// Sends a request to unregister the application with the kernel
        /// </summary>
        public static void Unregister()
        {
            ThreadPool.QueueUserWorkItem(func =>
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
                }
            });

        }

        /// <summary>
        /// Sends a request to the kernel to retrieve the battery level for a specific wocket
        /// </summary>
        /// <param name="mac">A wocket's mac address</param>        
        public static void GET_BATTERY_LEVEL(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
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
                }
            });
        }

        /// <summary>
        /// Writes a battery level value to the registry
        /// </summary>
        /// <param name="bl">Battery level response PDU</param>
        public static void WRITE_BATTERY_LEVEL(BL_RSP bl)
        {
           ThreadPool.QueueUserWorkItem(func =>
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
           });
        }

        /// <summary>
        /// Reads battery levels from the registry and stores it in the singelton wockets controller
        /// </summary>
        public static void READ_BATTERY_LEVEL()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: READ_BATTERY_LEVEL: " + e.ToString());
                }

                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to get battery percent for a specific wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>        
        public static void GET_BATTERY_PERCENT(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: GET_BATTERY_PERCENT: " + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Writes to the registry a battery percent
        /// </summary>
        /// <param name="bp">Battery percent response PDU</param>
        public static void WRITE_BATTERY_PERCENT(BP_RSP bp)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + bp._SensorID.ToString("0"));
                    rk.SetValue("BATTERY_PERCENT", bp._Percent, RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_BATTERY_PERCENT:" + e.ToString());
                }

                kernelLock.Release();
            });
        }


        /// <summary>
        /// Reads from the registry battery percents for the wockets
        /// </summary>        
        public static void READ_BATTERY_PERCENT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to get a PDU count
        /// </summary>
        /// <param name="mac">A mac address for a wocket</param>        
        public static void GET_PDU_COUNT(string mac)
        {
           ThreadPool.QueueUserWorkItem(func =>
           {
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
                   }
               }
               catch (Exception e)
               {
                   Logger.Error("Core.cs:GET_PDU_COUNT:" + e.ToString());
               }
               kernelLock.Release();
           });
        }


        /// <summary>
        /// Writes a packet count to the registry
        /// </summary>
        /// <param name="pc">Packet count response PDU</param>
        /// 
        public static void READ_RECEIVED_COUNT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._ReceivedPackets = Convert.ToInt32(rk.GetValue("RECEIVED_COUNT"));
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }
        public static void WRITE_RECEIVED_COUNT(int sensorID, int received)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensorID.ToString("0"));
                    rk.SetValue("RECEIVED_COUNT", received, RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_RECEIVED_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }




        public static void READ_RECEIVED_ACs()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._ReceivedACs = Convert.ToInt32(rk.GetValue("RECEIVED_ACs"));
                                CurrentWockets._Controller._Sensors[i]._TotalReceivedACs = Convert.ToInt32(rk.GetValue("RECEIVED_TACs"));
                            }
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }
        public static void WRITE_RECEIVED_ACs(int sensorID, int received)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensorID.ToString("0"));
                  
                    if (received == -1)
                    {
                        rk.SetValue("RECEIVED_ACs", 0, RegistryValueKind.String);
                        rk.SetValue("RECEIVED_TACs", 0, RegistryValueKind.String);
                    }
                    else
                    {
                        ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._ReceivedACs = received;
                        ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._TotalReceivedACs += received;
                        rk.SetValue("RECEIVED_ACs", ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._ReceivedACs, RegistryValueKind.String);
                        rk.SetValue("RECEIVED_TACs", ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._TotalReceivedACs, RegistryValueKind.String);
                    }                   
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_RECEIVED_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }






        public static void READ_SAVED_ACs()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._SavedACs = Convert.ToInt32(rk.GetValue("SAVED_ACs"));
                                CurrentWockets._Controller._Sensors[i]._TotalSavedACs = Convert.ToInt32(rk.GetValue("SAVED_TACs"));
                            }
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }
        public static void WRITE_SAVED_ACs(int sensorID, int saved)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensorID.ToString("0"));

                    if (saved == -1)
                    {
                        rk.SetValue("SAVED_ACs", 0, RegistryValueKind.String);
                        rk.SetValue("SAVED_TACs",0, RegistryValueKind.String);

                    }
                    else
                    {
                        ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._SavedACs = saved;
                        ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._TotalSavedACs += saved;
                        rk.SetValue("SAVED_ACs", ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._SavedACs, RegistryValueKind.String);
                        rk.SetValue("SAVED_TACs", ((Wocket)CurrentWockets._Controller._Sensors[sensorID])._TotalSavedACs, RegistryValueKind.String);

                    }
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_RECEIVED_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        public static void READ_FULL_RECEIVED_COUNT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._Full = Convert.ToInt32(rk.GetValue("FULL_RECEIVED_COUNT"));
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }
        public static void WRITE_FULL_RECEIVED_COUNT(int sensorID, int full)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensorID.ToString("0"));
                    rk.SetValue("FULL_RECEIVED_COUNT", full, RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_RECEIVED_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        public static void READ_PARTIAL_RECEIVED_COUNT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._Partial = Convert.ToInt32(rk.GetValue("PARTIAL_RECEIVED_COUNT"));
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }
        public static void WRITE_PARTIAL_RECEIVED_COUNT(int sensorID, int partial)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensorID.ToString("0"));
                    rk.SetValue("PARTIAL_RECEIVED_COUNT", partial, RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_RECEIVED_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }




        public static void READ_EMPTY_RECEIVED_COUNT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._Empty = Convert.ToInt32(rk.GetValue("EMPTY_RECEIVED_COUNT"));
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }
        public static void WRITE_EMPTY_RECEIVED_COUNT(int sensorID, int partial)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sensorID.ToString("0"));
                    rk.SetValue("EMPTY_RECEIVED_COUNT", partial, RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_RECEIVED_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        public static void READ_MAC()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {

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
                                CurrentWockets._Controller._Sensors[i]._Address = (string)rk.GetValue("MacAddress");
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_BATTERY_PERCENT:" + e.ToString());

                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Writes a packet count to the registry
        /// </summary>
        /// <param name="pc">Packet count response PDU</param>
        public static void WRITE_PDU_COUNT(PC_RSP pc)
        {
            ThreadPool.QueueUserWorkItem(func =>
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
            });
        }

        /// <summary>
        /// Reads packet count from the registry for the wockets and stores it in the wockets controller
        /// </summary>        
        public static void READ_PDU_COUNT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_PDU_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to get the wocket's sensitivity
        /// </summary>
        /// <param name="mac">The mac address for the wocket</param>
        public static void GET_WOCKET_SENSITIVITY(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_WOCKET_SENSITIVITY:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Writes the sensitivity of the wocket to the registry
        /// </summary>
        /// <param name="sen">Sensitivity response PDU</param>
        public static void WRITE_SENSITIVITY(SENS_RSP sen)
        {
            ThreadPool.QueueUserWorkItem(func =>
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
            });
        }
        
        /// <summary>
        /// Reads the sensitivity of the wockets from the registries and loads it into the wockets controller
        /// </summary>
        public static void READ_SENSITIVITY()
        {

            ThreadPool.QueueUserWorkItem(func =>
            {
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
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_SENSITIVITY:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to set the wockets sensitivity
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="sensitivity">Sensitivity of the wocket</param>
        public static void SET_WOCKET_SENSITIVITY(string mac, Sensitivity sensitivity)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_WOCKET_SENSITIVITY:" + e.ToString());
                }

                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to retrieve the wockets calibration values
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>        
        public static void GET_WOCKET_CALIBRATION(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_WOCKET_CALIBRATION:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Writes calibration values in the registry
        /// </summary>
        /// <param name="cal">Calibration response PDU</param>
        public static void WRITE_CALIBRATION(CAL_RSP cal)
        {
            ThreadPool.QueueUserWorkItem(func =>
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
            });
        }

        /// <summary>
        /// Reads calibration values from the registry and loads them into the current wockets controller
        /// </summary>        
        public static void READ_CALIBRATION()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_CALIBRATION:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to set the calibration values for a wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        /// <param name="calibration">A string specifiying the calibration values</param>
        public static void SET_WOCKET_CALIBRATION(string mac, string calibration)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_WOCKET_CALIBRATION:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to get the sampling rate for a wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        public static void GET_WOCKET_SAMPLING_RATE(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_WOCKET_SAMPLING_RATE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to set a wocket's sampling rate
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="sr">Sampling rate of the wocket</param>
        public static void SET_WOCKET_SAMPLING_RATE(string mac, int sr)
        {

            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_WOCKET_SAMPLING_RATE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Writes the sampling rate to the registry
        /// </summary>
        /// <param name="sr">Sampling rate response PDU</param>
        public static void WRITE_SAMPLING_RATE(SR_RSP sr)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + sr._SensorID.ToString("0"));
                    rk.SetValue("SAMPLING_RATE", sr._SamplingRate, RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_SAMPLING_RATE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Reads the sampling rate from the registry and loads it into the current wockets controller
        /// </summary>
        public static void READ_SAMPLING_RATE()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_SAMPLING_RATE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Writes the activity count to the registry
        /// </summary>
        /// <param name="ac">Activity count response packet</param>
        public static void WRITE_ACTIVITY_COUNT(AC_RSP ac)
        {
            ThreadPool.QueueUserWorkItem(func =>
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
            });
        }


        /// <summary>
        /// Reads the activity count for the wockets from the registry and loads it in the current wockets controller
        /// </summary>
        public static void READ_ACTIVITY_COUNT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_ACTIVITY_COUNT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to get the values for the interrupt timer counters for  a sepcific wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>        
        public static void GET_WOCKET_TCT(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    if ((_Registered) && (_Connected))
                    {
                        string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                        NamedEvents namedEvent = new NamedEvents();
                        RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                        rk.SetValue("Message", KernelCommand.GET_TCT.ToString(), RegistryValueKind.String);
                        rk.SetValue("Param", mac.ToString(), RegistryValueKind.String);
                        rk.Flush();
                        rk.Close();
                        namedEvent.Send(Core._OutgoingChannel);
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_TCT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to set the interrupt timer counters
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="tct">value for the timer counter for (reps-1) iterations</param>
        /// <param name="reps">number of reps to wait on that counter before sampling</param>
        /// <param name="last">value of the timer counter for the last iteration</param>
        public static void SET_TCT(string mac, int tct, int reps, int last)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();

                try
                {
                    if ((_Registered) && (_Connected))
                    {
                        string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + _IcomingChannel + "}";
                        NamedEvents namedEvent = new NamedEvents();
                        RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                        rk.SetValue("Message", KernelCommand.SET_TCT.ToString(), RegistryValueKind.String);
                        rk.SetValue("Param", mac.ToString() + ":" + tct.ToString() + ":" + reps.ToString() + ":" + last.ToString(), RegistryValueKind.String);
                        rk.Flush();
                        rk.Close();
                        namedEvent.Send(Core._OutgoingChannel);
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_TCT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Writes the values of the interrupt timer to the registry
        /// </summary>
        /// <param name="tct">Stores the values for the interrupt timer</param>
        public static void WRITE_TCT(TCT_RSP tct)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + tct._SensorID.ToString("0"));
                    rk.SetValue("TCT", tct._TCT, RegistryValueKind.String);
                    rk.SetValue("TCT_REPS", tct._REPS, RegistryValueKind.String);
                    rk.SetValue("TCT_LAST", tct._LAST, RegistryValueKind.String);
                    rk.Close();

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_TCT:" + e.ToString());
                }

                kernelLock.Release();
            });
        }


        /// <summary>
        /// Reads the values of the interrupt timer from the registry
        /// </summary>
        public static void READ_TCT()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                                ((Accelerometer)CurrentWockets._Controller._Sensors[i])._TCT = Convert.ToInt32((string)rk.GetValue("TCT"));
                                ((Accelerometer)CurrentWockets._Controller._Sensors[i])._TCTREPS = Convert.ToInt32((string)rk.GetValue("TCT_REPS"));
                                ((Accelerometer)CurrentWockets._Controller._Sensors[i])._TCTLAST = Convert.ToInt32((string)rk.GetValue("TCT_LAST"));
                            }
                            rk.Close();
                        }
                        catch
                        {
                        }
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_TCT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to get the powerdown timeout for the wocket
        /// </summary>
        /// <param name="mac">MAC address for the wocket</param>
        public static void GET_WOCKET_POWERDOWN_TIMEOUT(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_WOCKET_POWERDOWN_TIMEOUT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to set the wockets power down timeout
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="timeout">Timeout for powering down in ?</param>
        public static void SET_WOCKET_POWERDOWN_TIMEOUT(string mac, int timeout)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_WOCKET_POWERDOWN_TIMEOUT:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to get the transmission mode
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        public static void GET_TRANSMISSION_MODE(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_TRANSMISSION_MODE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Writes transmission mode to the registry
        /// </summary>
        /// <param name="tm">Transmission Mode response PDU</param>
        public static void WRITE_TRANSMISSION_MODE(TM_RSP tm)
        {
            ThreadPool.QueueUserWorkItem(func =>
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
            });
        }


        /// <summary>
        /// Reads the transmission mode from the registry and loads it in the current wockets controller
        /// </summary>        
        public static void READ_TRANSMISSION_MODE()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:READ_TRANSMISSION_MODE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to set the transmission mode of a wocket
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="mode">Mode of transmission</param>
        public static void SET_TRANSMISSION_MODE(string mac, TransmissionMode mode)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_TRANSMISSION_MODE:" + e.ToString());
                }

                kernelLock.Release();
            });
        }


        /// <summary>
        /// Sends a request to the kernel to get the memory mode
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        public static void GET_MEMORY_MODE(string mac)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:GET_MEMORY_MODE:" + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Sends a request to the kernel to set the memory mode
        /// </summary>
        /// <param name="mac">MAC address of the wocket</param>
        /// <param name="mode">Memory mode</param>
        public static void SET_MEMORY_MODE(string mac, MemoryMode mode)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
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

                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:SET_MEMORY_MODE:" + e.ToString());
                }

                kernelLock.Release();
            });
        }








        //CORE REGISTRY COMMANDS FOR UPLOAD TRACKING


        /// <summary>
        /// Writes last upload time
        /// </summary>
        /// <param name=""></param>
        public static void WRITE_LAST_UPLOAD_TIME(DateTime uploadtime)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {

                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_KERNEL_PATH);
                    rk.SetValue("upload_time", uploadtime.ToString("yyyy-MM-dd HH:mm tt"), RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_LAST_UPLOAD_TIME: " + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Reads last upload time
        /// </summary>
        public static void READ_LAST_UPLOAD_TIME()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = null;

                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH);
                        CurrentWockets._UploadLastTime = DateTime.ParseExact((string)rk.GetValue("upload_time"), "yyyy-MM-dd HH:mm tt", null);
                        rk.Close();
                    }
                    catch
                    {
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: READ_LAST_UPLOAD_TIME: " + e.ToString());
                }

                kernelLock.Release();
            });
        }


        /// <summary>
        /// Writes last upload duration
        /// </summary>
        /// <param name=""></param>
        public static void WRITE_LAST_UPLOAD_DURATION(TimeSpan duration)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {                  
                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_KERNEL_PATH);
                    rk.SetValue("upload_duration", duration.Hours.ToString("00")+":"+duration.Minutes.ToString("00")+":"+duration.Seconds.ToString("00"), RegistryValueKind.String);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_LAST_UPLOAD_TIME: " + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Reads last upload duration
        /// </summary>
        public static void READ_LAST_UPLOAD_DURATION()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = null;

                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH);
                        CurrentWockets._UploadDuration = (string)rk.GetValue("upload_duration");
                        rk.Close();
                    }
                    catch
                    {
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: READ_LAST_UPLOAD_DURATION: " + e.ToString());
                }

                kernelLock.Release();
            });
        }




        /// <summary>
        /// Writes last # of new files to be uploaded
        /// </summary>
        /// <param name=""></param>
        public static void WRITE_LAST_UPLOAD_NEWFILES(int numFiles)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_KERNEL_PATH);
                    rk.SetValue("newfiles", numFiles, RegistryValueKind.DWord);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_LAST_UPLOAD_NEWFILES: " + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Reads last upload duration
        /// </summary>
        public static void READ_LAST_UPLOAD_NEWFILES()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = null;
                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH);
                        CurrentWockets._UploadNewFiles = (int)rk.GetValue("newfiles");
                        rk.Close();
                    }
                    catch
                    {
                    }
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: READ_LAST_UPLOAD_NEWFILES: " + e.ToString());
                }

                kernelLock.Release();
            });
        }









        /// <summary>
        /// Writes last # of successful files uploaded
        /// </summary>
        /// <param name=""></param>
        public static void WRITE_LAST_UPLOAD_SUCCESSFILES(int numFiles)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_KERNEL_PATH);
                    rk.SetValue("successfiles", numFiles, RegistryValueKind.DWord);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_LAST_UPLOAD_SUCCESSFILES: " + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Reads last # of successful files uploaded
        /// </summary>
        public static void READ_LAST_UPLOAD_SUCCESSFILES()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = null;

                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH);
                        CurrentWockets._UploadSuccessFiles = (int)rk.GetValue("successfiles");
                        rk.Close();
                    }
                    catch
                    {
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: READ_LAST_UPLOAD_SUCCESSFILES: " + e.ToString());
                }

                kernelLock.Release();
            });
        }



        /// <summary>
        /// Writes last # of failed files uploaded
        /// </summary>
        /// <param name=""></param>
        public static void WRITE_LAST_UPLOAD_FAILEDFILES(int numFiles)
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_KERNEL_PATH);
                    rk.SetValue("failedfiles", numFiles, RegistryValueKind.DWord);
                    rk.Close();
                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs:WRITE_LAST_UPLOAD_FAILEDFILES: " + e.ToString());
                }
                kernelLock.Release();
            });
        }

        /// <summary>
        /// Reads last # of failed files uploaded
        /// </summary>
        public static void READ_LAST_UPLOAD_FAILEDFILES()
        {
            ThreadPool.QueueUserWorkItem(func =>
            {
                kernelLock.WaitOne();
                try
                {
                    RegistryKey rk = null;

                    try
                    {
                        rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH);
                        CurrentWockets._UploadFailedFiles = (int)rk.GetValue("failedfiles");
                        rk.Close();
                    }
                    catch
                    {
                    }

                }
                catch (Exception e)
                {
                    Logger.Error("Core.cs: READ_LAST_UPLOAD_FAILEDFILES: " + e.ToString());
                }

                kernelLock.Release();
            });
        }
    }
}
