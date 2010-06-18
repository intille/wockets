using System;
using System.Threading;
using System.Collections;
using System.IO;
using Wockets;
using Wockets.Utils;
using Wockets.Receivers;
using Wockets.Utils.network;
using Wockets.Kernel.Types;
using Wockets.Utils.IPC;
using Wockets.Data.Commands;
using Wockets.Sensors.Accelerometers;
using Microsoft.Win32;
using InTheHand.Net.Sockets;


namespace Wockets.Kernel
{
    public class Booter
    {
        public static bool _Running = false;
        public static bool _WocketsRunning = false;
        private static object booterLock = new object();
        private static object kernelLock = new object();
        //private static object registryLock = new object();
        private static object discoveryLock = new object();
        private static Thread commandThread;
        public static int _NumRegistrations = 0;

        private static Hashtable applicationPaths = new Hashtable();
        private static Hashtable applicationThreads = new Hashtable();
        private static Semaphore registryLock;
        private static WocketsController wcontroller = null;
        private static string rootStorageDirectory = "";
        private static string storageDirectory = "";
        private static string path = "";

        static Booter()
        {

            //Send a termination event for any running kernel to abort           
            //Fix the registry if needed

            path = Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase);
            registryLock = new Semaphore(1, 1, Core.REGISTRY_LOCK);
            //initialize the path as an empty string
            string firstCard = "";

            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();

            //iterate through them
            for (int x = 0; x < fsi.Length; x++)
            {
                //check to see if this is a temporary storage card (e.g. SD card)
                if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                {
                    //if so, return the path
                    firstCard = fsi[x].FullName;
                    break;
                }
            }
            rootStorageDirectory = firstCard + "\\Wockets\\";
            Directory.CreateDirectory(rootStorageDirectory);
            
            wcontroller = new WocketsController("", "", "");           
            wcontroller.FromXML(path+"//NeededFiles//Master//SensorData.xml");
            Logger.InitLogger(rootStorageDirectory + "kernellog\\");
            Logger.Debug2("Time,Time,PowerPercent,Voltage,Current,Temperature\n");

            //Used for logging the battery
            //wcontroller.InitializeBatteryThread();
            
        }
        public static void Boot()
        {
            try
            {
                lock (booterLock)
                {
                    if (!_Running)
                    {
                        Initialize();
                        commandThread = new Thread(new ThreadStart(CommandHandler));
                        commandThread.Start();
                        _Running = true;
                        commandThread.Join();

                    }
                }
            }
            catch
            {
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
                rk.SetValue("Status", 0, RegistryValueKind.DWord);
                rk.Close();
                Logger.Close();
                System.Diagnostics.Process.GetCurrentProcess().Close();
                System.Diagnostics.Process.GetCurrentProcess().Kill();
            }
        }

        

        public static void ApplicationHandler()
        {
            int tid = Thread.CurrentThread.ManagedThreadId;
            string commandPath = Core.REGISTRY_REGISTERED_APPLICATIONS_PATH+"\\{" + (string)applicationPaths[tid] + "}";
            NamedEvents namedEvent = new NamedEvents();
            string applicationGuid = ((string)applicationPaths[tid]);
            string channel = applicationGuid + "-kernel";
            //WocketsController lwcontroller = null;
            while (true)
            {
                //ensures prior synchronization
                namedEvent.Receive(channel.ToString());
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                string msg = (string)rk.GetValue("Message");
                string param = (string)rk.GetValue("Param");
                rk.Close();
                registryLock.Release();

                //lock the kernel to avoid changing wockets controller at the
                //same time from multiple applications
                lock (kernelLock)
                {
                    /*if (msg == KernelCommand.SET_SNIFF.ToString())
                    {
                        if (_WocketsRunning)
                        {                           
                            EnterCommandMode enter = new EnterCommandMode();
                            BT_RST reset = new BT_RST();
                            ushort tsniff=0;
                            if (param == SleepModes.Sleep1Second.ToString())
                                tsniff = 1000;
                            else if (param == SleepModes.Sleep2Seconds.ToString())
                                tsniff = 2000;
                                
                            SET_SM sniff=new SET_SM(tsniff);
                            PAUSE pause = new PAUSE();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(pause._Bytes);
                                Thread.Sleep(500);
                                ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(enter._Bytes);
                                ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(sniff._Bytes);
                                ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(reset._Bytes);
                            }
                        }
                    }
                    else*/ if (msg == KernelCommand.CONNECT.ToString())
                    {
                        if (!_WocketsRunning)
                        {


                            storageDirectory = rootStorageDirectory + "Session" + DateTime.Now.Month + "-" + DateTime.Now.Day + "-" + DateTime.Now.Hour + "-" + DateTime.Now.Minute + "-" + DateTime.Now.Second;
                            if (!Directory.Exists(storageDirectory))
                                Directory.CreateDirectory(storageDirectory);
                            try
                            {
                                File.Copy(path + "//NeededFiles//Master//Configuration.xml", storageDirectory + "\\Configuration.xml");
                            }
                            catch (Exception e)
                            {
                            }

                            CurrentWockets._Configuration = new Wockets.Data.Configuration.WocketsConfiguration();
                            CurrentWockets._Configuration.FromXML(storageDirectory + "\\Configuration.xml");
                            CurrentWockets._Configuration._MemoryMode = Wockets.Data.Configuration.MemoryConfiguration.SHARED;

                            //load local wockets controller
                            CurrentWockets._Controller = new WocketsController("", "", "");
                            CurrentWockets._Controller.FromXML(path + "//NeededFiles//Master//SensorData.xml");
                            int index=0;
                            for (int i = 0; (i < Booter.wcontroller._Sensors.Count); i++)
                            {
                                if (Booter.wcontroller._Sensors[i]._Loaded)
                                {
                                    CurrentWockets._Controller._Receivers[index]._ID = index;
                                    ((RFCOMMReceiver)CurrentWockets._Controller._Receivers[index])._Address = ((RFCOMMReceiver)Booter.wcontroller._Receivers[i])._Address;
                                    CurrentWockets._Controller._Decoders[index]._ID = index;
                                    CurrentWockets._Controller._Sensors[index]._ID = index;
                                    CurrentWockets._Controller._Sensors[index]._Receiver = CurrentWockets._Controller._Receivers[index];
                                    CurrentWockets._Controller._Sensors[index]._Decoder = CurrentWockets._Controller._Decoders[index];
                                    CurrentWockets._Controller._Sensors[index]._Loaded = true;
                                    index++;
                                }
                            }
                            CurrentWockets._Controller._storageDirectory = storageDirectory;
                            for (int i = CurrentWockets._Controller._Sensors.Count - 1; (i >= 0); i--)
                            {
                                if (!CurrentWockets._Controller._Sensors[i]._Loaded)
                                {
                                    CurrentWockets._Controller._Receivers.RemoveAt(i);
                                    CurrentWockets._Controller._Sensors.RemoveAt(i);
                                    CurrentWockets._Controller._Decoders.RemoveAt(i);
                                }
                                else
                                {
                                    CurrentWockets._Controller._Sensors[i]._RootStorageDirectory = storageDirectory + "\\data\\raw\\PLFormat\\";
                                }
                            }

                            CurrentWockets._Controller._Receivers.SortByAddress();
                            for (int i = 0; (i < CurrentWockets._Controller._Sensors.Count); i++)
                                ((Wocket)CurrentWockets._Controller._Sensors[i])._Receiver = CurrentWockets._Controller._Receivers[i];

                            if (CurrentWockets._Controller._Sensors.Count > 0)
                            {
                                registryLock.WaitOne();
                                rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH,true);
                                rk.SetValue("Storage", storageDirectory);                                                                   
                                rk.Close();                                
                                registryLock.Release();
              
                                TextWriter tw = new StreamWriter(storageDirectory + "\\SensorData.xml");
                                tw.WriteLine(CurrentWockets._Controller.ToXML());
                                tw.Close();
                           
                               _WocketsRunning = true;
                               CurrentWockets._Controller.Initialize();
                               Send(ApplicationResponse.CONNECT_SUCCESS, applicationGuid);
                            }else
                                Send(ApplicationResponse.CONNECT_FAILURE, applicationGuid);
                            
                        }
                        else
                            Send(ApplicationResponse.CONNECT_FAILURE, applicationGuid);
                    }
                    else if (msg == KernelCommand.DISCONNECT.ToString())
                    {
                        if (_WocketsRunning)
                        {
                            CurrentWockets._Controller.Dispose();
                            _WocketsRunning = false;
                            Send(ApplicationResponse.DISCONNECT_SUCCESS, applicationGuid);
                        }
                        else
                            Send(ApplicationResponse.DISCONNECT_FAILURE, applicationGuid);

                    }
                    else if (msg == KernelCommand.SET_SENSORS.ToString())
                    {
                        if (!_WocketsRunning)
                        {
                            registryLock.WaitOne();
                            int index = 0;
                            for (int i = 0; (i < 5); i++)
                            {
                                rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                                int status = (int)rk.GetValue("Status");
                                if (status == 1)
                                {
                                    string mac = (string)rk.GetValue("MacAddress");

                                    ((RFCOMMReceiver)Booter.wcontroller._Receivers[index])._Address = mac;
                                    Booter.wcontroller._Sensors[index++]._Loaded = true;

                                }
                                rk.Close();
                            }
                            registryLock.Release();
                            Send(ApplicationResponse.SET_SENSORS_SUCCESS, applicationGuid);
                        }
                        else
                            Send(ApplicationResponse.SET_SENSORS_FAILURE, applicationGuid);
                    }
                }

                namedEvent.Reset();
            }
        }

        /** Processes any application registrations with the kernel **/
        private static void CommandHandler()
        {       
            NamedEvents namedEvent = new NamedEvents();

            while (true)
            {
                //ensures prior synchronization
                namedEvent.Receive(Channels.COMMAND.ToString());
                lock (registryLock)
                {
                    RegistryKey rk = Registry.LocalMachine.OpenSubKey(Core.COMMAND_CHANNEL, true);
                    string msg = (string)rk.GetValue("Message");//, KernelNamedEvents.REGISTER.ToString(), RegistryValueKind.DWord);
                    string param = (string)rk.GetValue("Param");//, processID.ToString(), RegistryValueKind.DWord);        
                    rk.Close();

                    if (msg == KernelCommand.TERMINATE.ToString())
                    {


                        rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
                        rk.SetValue("Status", 0, RegistryValueKind.DWord);
                        rk.Close();                        
                        Logger.Close();
                        System.Diagnostics.Process.GetCurrentProcess().Close();
                        System.Diagnostics.Process.GetCurrentProcess().Kill();
                    }
                    else if (msg == KernelCommand.REGISTER.ToString())
                    {
                        rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + param + "}");                        
                        rk.SetValue("Message", "", RegistryValueKind.String);
                        rk.SetValue("Param", "", RegistryValueKind.String);
                        rk.Close();

                        //spawn the processing thread
                        Thread applicationThread = new Thread(new ThreadStart(ApplicationHandler));        
                        applicationPaths.Add(applicationThread.ManagedThreadId, param);
                        applicationThreads.Add(param,applicationThread);
                        applicationThread.Start();
                        _NumRegistrations++;

                        rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);                                                                  
                        rk.SetValue("Count", _NumRegistrations, RegistryValueKind.DWord);
                        rk.Close();
                    }
                    else if (msg == KernelCommand.UNREGISTER.ToString())
                    {


                        //Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + param + "}");

                        //kill the processing thread
                        applicationPaths.Remove(((Thread)applicationThreads[param]).ManagedThreadId);
                        ((Thread)applicationThreads[param]).Abort();
                        applicationThreads.Remove(param);
                        _NumRegistrations--;

                        rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);                        
                        rk.SetValue("Count", _NumRegistrations, RegistryValueKind.DWord);
                        rk.Close();
                    }
                    else if (msg == KernelCommand.DISCOVER.ToString())
                    {
                        Thread discovery = new Thread(new ThreadStart(Discover));
                        discoveryGuid = param;
                        discovery.Start();
                    }                    
                }


                namedEvent.Reset();
            }

        }
        private static string discoveryGuid="";
        private static void Discover()
        {
            lock (discoveryLock)
            {

                try
                {
                    Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
                }
                catch (Exception)
                {
                }

                NetworkStacks._BluetoothStack.Initialize();
                BluetoothClient btc = new BluetoothClient();
                BluetoothDeviceInfo[] devices = btc.DiscoverDevices();
                int wocketCount = 0;
                for (int i = 0; (i < devices.Length); i++)
                {
                    //if the device is a wocket
                    if (((devices[i].DeviceName.IndexOf("WKT") >= 0) || (devices[i].DeviceName.IndexOf("Wocket") >= 0) || (devices[i].DeviceName.IndexOf("FireFly") >= 0)) && (wocketCount < 100))
                    {
                        string hex = "";
                        //byte[] address = devices[i].DeviceAddress.ToByteArray();
                        //for (int j = 0; j < address.Length; j++)
                          //  hex += address[j].ToString("X2");

                        hex=devices[i].DeviceAddress.ToString();
                        registryLock.WaitOne();
                        RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH + "\\" + wocketCount.ToString("00"));
                        rk.SetValue("Name", devices[i].DeviceName, RegistryValueKind.String);
                        rk.SetValue("MacAddress", hex, RegistryValueKind.String);
                        rk.Close();
                        registryLock.Release();


                        wocketCount++;
                    }
                }


                //Send to the appropriate application a response
                Send(ApplicationResponse.DISCOVERY_COMPLETED, discoveryGuid);

            }
        }

        //send a response to an application
        public static void Send(ApplicationResponse response, string senderGuid)
        {
            registryLock.WaitOne();
            RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + senderGuid + "}");
            rk.SetValue("Message", response.ToString(), RegistryValueKind.String);
            rk.SetValue("Param", "", RegistryValueKind.String);
            rk.Close();
            registryLock.Release();

            NamedEvents namedEvent = new NamedEvents();
            namedEvent.Send(senderGuid);
        }

        /* Initializes the kernel */
        private static void Initialize()
        {
            //Always attempt to delete registered applications
            //at the beginning
            //this will fail only if the registry tree is being accessed at that time (i.e. not writable)
            registryLock.WaitOne();
            try
            {
                Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);
            }
            catch (Exception)
            {
            }


            RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
            rk.SetValue("Handle", 00000, RegistryValueKind.DWord);
            rk.SetValue("OnBoot", 1, RegistryValueKind.DWord);
            rk.SetValue("Status", 1, RegistryValueKind.DWord);
            rk.SetValue("Storage","", RegistryValueKind.String);
            rk.Close();
            rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel\\Commands");
            rk.SetValue("GET_BT", 0, RegistryValueKind.DWord);
            rk.SetValue("GET_PC", 1, RegistryValueKind.DWord);
            rk.SetValue("GET_SM", 2, RegistryValueKind.DWord);
            rk.SetValue("SET_SM", 3, RegistryValueKind.DWord);
            rk.SetValue("GET_SEN", 6, RegistryValueKind.DWord);
            rk.SetValue("SET_SEN", 7, RegistryValueKind.DWord);
            rk.SetValue("GET_CAL", 8, RegistryValueKind.DWord);
            rk.SetValue("SET_CAL", 9, RegistryValueKind.DWord);
            rk.SetValue("GET_TP", 10, RegistryValueKind.DWord);
            rk.SetValue("SET_TP", 11, RegistryValueKind.DWord);
            rk.SetValue("GET_SR", 12, RegistryValueKind.DWord);
            rk.SetValue("SET_SR", 13, RegistryValueKind.DWord);
            rk.SetValue("GET_DSC", 14, RegistryValueKind.DWord);
            rk.SetValue("SET_DSC", 15, RegistryValueKind.DWord);
            rk.SetValue("GET_TM", 16, RegistryValueKind.DWord);
            rk.SetValue("SET_TM", 17, RegistryValueKind.DWord);
            rk.SetValue("GET_ALT", 18, RegistryValueKind.DWord);
            rk.SetValue("SET_ALT", 19, RegistryValueKind.DWord);
            rk.SetValue("GET_PDT", 20, RegistryValueKind.DWord);
            rk.SetValue("SET_PDT", 21, RegistryValueKind.DWord);
            rk.SetValue("RST_WK", 22, RegistryValueKind.DWord);
            rk.SetValue("GET_CFT", 23, RegistryValueKind.DWord);
            rk.SetValue("SET_CFT", 24, RegistryValueKind.DWord);
            rk.SetValue("GET_BR", 25, RegistryValueKind.DWord);
            rk.SetValue("SET_BR", 26, RegistryValueKind.DWord);
            rk.Flush();
            rk.Close();
            rk = Registry.LocalMachine.CreateSubKey(Core.COMMAND_CHANNEL);
            rk.SetValue("Message", "", RegistryValueKind.String);
            rk.SetValue("Param", "", RegistryValueKind.String);
            rk.Flush();
            rk.Close();
            rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH);
            rk.Flush();
            rk.Close();
            for (int i = 0; (i < 5); i++)
            {
                rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_SENSORS_PATH + "\\" + i.ToString("0"));
                rk.SetValue("MacAddress", "");         
                rk.SetValue("Status",0, RegistryValueKind.DWord);                
                rk.Close();
            }
            
            rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
            rk.Flush();
            rk.Close();
            rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);                      
            rk.SetValue("Count", 0, RegistryValueKind.DWord);
            rk.Flush();
            rk.Close();
            registryLock.Release();

        }
    }
}
