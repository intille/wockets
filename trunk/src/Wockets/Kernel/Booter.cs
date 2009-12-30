using System;
using System.Threading;
using System.Collections;
using System.IO;
using Wockets;
using Wockets.Utils;
using Wockets.Receivers;
using Wockets.Utils.network;
using Wockets.Kernel.Types;
using Wockets.IPC;
using Wockets.Data.Commands;
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
        private static string storageDirectory = "";
        private static string path = "";

        static Booter()
        {
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
            storageDirectory = firstCard + "\\Wockets\\";
            Directory.CreateDirectory(storageDirectory);
            
            wcontroller = new WocketsController("", "", "");           
            wcontroller.FromXML(path+"//NeededFiles//SensorConfigurations//SensorData43.xml");
            Logger.InitLogger(storageDirectory);
            Logger.Debug2("Time,Time,PowerPercent,Voltage,Current,Temperature\n");
            
        }
        public static void Boot()
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

        

        public static void ApplicationHandler()
        {
            int tid = Thread.CurrentThread.ManagedThreadId;
            string commandPath = Core.REGISTRY_REGISTERED_APPLICATIONS_PATH+"\\{" + (string)applicationPaths[tid] + "}";
            NamedEvents namedEvent = new NamedEvents();
            string applicationGuid = ((string)applicationPaths[tid]);
            string channel = applicationGuid + "-kernel";
            WocketsController lwcontroller = null;
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
                    if (msg == KernelCommand.SET_SNIFF.ToString())
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
                            for (int i = 0; (i < lwcontroller._Receivers.Count); i++)
                            {
                                ((SerialReceiver)lwcontroller._Receivers[i]).Write(pause._Bytes);
                                Thread.Sleep(500);
                                ((SerialReceiver)lwcontroller._Receivers[i]).Write(enter._Bytes);  
                                ((SerialReceiver)lwcontroller._Receivers[i]).Write(sniff._Bytes);
                                ((SerialReceiver)lwcontroller._Receivers[i]).Write(reset._Bytes);
                            }
                        }
                    }
                    else if (msg == KernelCommand.CONNECT.ToString())
                    {
                        if (!_WocketsRunning)
                        {

                            //load local wockets controller
                            lwcontroller = new WocketsController("", "", "");
                            lwcontroller.FromXML(path + "//NeededFiles//SensorConfigurations//SensorData43.xml");
                            int index=0;
                            for (int i = 0; (i < Booter.wcontroller._Sensors.Count); i++)
                            {
                                if (Booter.wcontroller._Sensors[i]._Loaded)
                                {
                                    lwcontroller._Receivers[index]._ID = index;
                                    ((RFCOMMReceiver)lwcontroller._Receivers[index])._Address=((RFCOMMReceiver)Booter.wcontroller._Receivers[i])._Address;
                                    lwcontroller._Decoders[index]._ID = index;
                                    lwcontroller._Sensors[index]._ID=index;
                                    lwcontroller._Sensors[index]._Receiver = lwcontroller._Receivers[index];
                                    lwcontroller._Sensors[index]._Decoder = lwcontroller._Decoders[index];
                                    lwcontroller._Sensors[index]._Loaded = true;
                                    index++;
                                }
                            }
                            lwcontroller._storageDirectory = storageDirectory;
                            for (int i = lwcontroller._Sensors.Count-1; (i>=0); i--)
                            {
                                if (!lwcontroller._Sensors[i]._Loaded)
                                {
                                    lwcontroller._Receivers.RemoveAt(i);
                                    lwcontroller._Sensors.RemoveAt(i);
                                    lwcontroller._Decoders.RemoveAt(i);
                                }
                                else
                                {
                                    lwcontroller._Sensors[i]._RootStorageDirectory = storageDirectory;
                                }
                            }

                            _WocketsRunning = true;
                            lwcontroller.Initialize();
                            Send(ApplicationResponse.CONNECT_SUCCESS, applicationGuid);
                        }
                        else
                            Send(ApplicationResponse.CONNECT_FAILURE, applicationGuid);
                    }
                    else if (msg == KernelCommand.DISCONNECT.ToString())
                    {
                        if (_WocketsRunning)
                        {
                            lwcontroller.Dispose();
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
                NetworkStacks._BluetoothStack.Initialize();
                BluetoothClient btc = new BluetoothClient();
                BluetoothDeviceInfo[] devices = btc.DiscoverDevices();
                int wocketCount = 0;
                for (int i = 0; (i < devices.Length); i++)
                {
                    //if the device is a wocket
                    if (((devices[i].DeviceName.IndexOf("Wocket") >= 0) || (devices[i].DeviceName.IndexOf("FireFly") >= 0)) && (wocketCount < 100))
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

            try
            {
                Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
            }
            catch (Exception)
            {
            }

            RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
            rk.SetValue("Handle", 00000, RegistryValueKind.DWord);
            rk.SetValue("OnBoot", 1, RegistryValueKind.DWord);
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
