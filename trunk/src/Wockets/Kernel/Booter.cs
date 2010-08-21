﻿using System;
using System.Threading;
using System.Collections;
using System.IO;
using Wockets;
using Wockets.Utils;
using Wockets.Receivers;
using Wockets.Decoders;
using Wockets.Utils.network;
using Wockets.Data.Responses;
using Wockets.Kernel.Types;
using Wockets.Utils.IPC;
using Wockets.Data.Commands;
using Wockets.Data.Types;
using Wockets.Sensors.Accelerometers;
using Microsoft.Win32;
using InTheHand.Net.Sockets;


namespace Wockets.Kernel
{
    public class Booter
    {
        /// <summary>
        /// Specifies if the kernel is running
        /// </summary>
        public static bool _Running = false;

        /// <summary>
        /// Specifies if the wockets are running
        /// </summary>
        public static bool _WocketsRunning = false;

        /// <summary>
        /// Locks the kernel during booting to ensure that only 1 instance is ever running
        /// </summary>
        private static object booterLock = new object();

        /// <summary>
        /// Locks the processing of a command from an application to avoid processing multiple commands simultaneously
        /// </summary>
        //private static object kernelLock = new object();        

        /// <summary>
        /// Locks the discovery of wockets to avoid multiple requests at the same time
        /// </summary>
        private static object discoveryLock = new object();

        /// <summary>
        /// Processes pre-registration requests from applications
        /// </summary>
        private static Thread commandThread;

        /// <summary>
        /// Stores the number of registered applications
        /// </summary>
        public static int _NumRegistrations = 0;

        /// <summary>
        /// Stores applications guids
        /// </summary>
        private static Hashtable applicationPaths = new Hashtable();

        /// <summary>
        /// Stores application command handler threads
        /// </summary>
        private static Hashtable applicationThreads = new Hashtable();

        /// <summary>
        /// A system wide semaphore to lock the registry
        /// </summary>
        //private static Semaphore registryLock;

        private static Semaphore kernelLock;

        /// <summary>
        /// An instance of the wockets controller
        /// </summary>
        private static WocketsController wcontroller = null;

        /// <summary>
        /// Root storage path for the wockets data
        /// </summary>
        private static string rootStorageDirectory = "";

        /// <summary>
        /// Storage path for the wockets data
        /// </summary>
        private static string storageDirectory = "";

        /// <summary>
        /// Application path
        /// </summary>
        private static string path = "";


        /// <summary>
        /// Constructor for initializing the kernel
        /// </summary>
        static Booter()
        {

            //Send a termination event for any running kernel to abort           
            //Fix the registry if needed

            path = Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().GetName().CodeBase);
            kernelLock = new Semaphore(1, 1, Core.KERNEL_LOCK);

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
            wcontroller._Mode = MemoryMode.BluetoothToShared;

            Logger.InitLogger(rootStorageDirectory + "kernellog\\");
            Logger.Debug2("Time,Time,PowerPercent,Voltage,Current,Temperature\n");            
            
        }

        /// <summary>
        /// Kernel booter that initiates the command thread
        /// </summary>
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
//                        Broadcast(KernelResponse.STARTED);
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



        /// <summary>
        /// Handler for decoder callbacks when wockets response packets are received
        /// </summary>
        /// <param name="e">Wockets response pakcet</param>
        private static void DecoderCallback(object e)
        {
            Response response = (Response)e;
            switch (response._Type)
            {
                case ResponseTypes.BL_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
//                        Broadcast(KernelResponse.BATTERY_LEVEL_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;

                case ResponseTypes.BP_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
//                        Broadcast(KernelResponse.BATTERY_PERCENT_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;

                case ResponseTypes.PC_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
                        //Broadcast(KernelResponse.PC_COUNT_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                case ResponseTypes.SENS_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
                        //Broadcast(KernelResponse.SENSITIVITY_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                case ResponseTypes.CAL_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
                        //Broadcast(KernelResponse.CALIBRATION_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;

                case ResponseTypes.SR_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
                        //Broadcast(KernelResponse.SAMPLING_RATE_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                case ResponseTypes.TM_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
                        //Broadcast(KernelResponse.TRANSMISSION_MODE_UPDATED);
                    }
                    catch
                    {                     
                    }
                    break;

                case ResponseTypes.AC_RSP: //write to the registry
                    try
                    {
                        foreach (string guid in applicationPaths.Values)
                            Send(KernelResponse.BATTERY_LEVEL_UPDATED, guid);
                        //Broadcast(KernelResponse.ACTIVITY_COUNT_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                default:
                    break;
            }
        }

        /// <summary>
        /// Handler for processing application messages
        /// </summary>
        public static void ApplicationHandler()
        {
            int tid = Thread.CurrentThread.ManagedThreadId;
            string commandPath = Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + (string)applicationPaths[tid] + "}";
            NamedEvents namedEvent = new NamedEvents();
            string applicationGuid = ((string)applicationPaths[tid]);
            string channel = applicationGuid + "-kernel";
            //WocketsController lwcontroller = null;
            while (true)
            {
                //ensures prior synchronization
                namedEvent.Receive(channel.ToString());
                kernelLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                string msg = (string)rk.GetValue("Message");
                string param = (string)rk.GetValue("Param");
                rk.Close();


                //lock the kernel to avoid changing wockets controller at the
                //same time from multiple applications


                #region DISCOVER
                if (msg == KernelCommand.DISCOVER.ToString())
                {
                    Thread discovery = new Thread(new ThreadStart(Discover));
                    discoveryGuid = param;
                    discovery.Start();
                }
                #endregion DISCOVER

                #region CONNECT
                else if (msg == KernelCommand.CONNECT.ToString())
                {
                    try
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
                            CurrentWockets._Controller._Mode = MemoryMode.BluetoothToShared;
                            int index = 0;
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
                                rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH, true);
                                rk.SetValue("Storage", storageDirectory);
                                rk.Close();                                

                                TextWriter tw = new StreamWriter(storageDirectory + "\\SensorData.xml");
                                tw.WriteLine(CurrentWockets._Controller.ToXML());
                                tw.Close();

                                _WocketsRunning = true;
                                CurrentWockets._Controller.Initialize();

                                //Subscribe to all callback events
                                foreach (Decoder d in CurrentWockets._Controller._Decoders)
                                {
                                    d.Subscribe(ResponseTypes.BL_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.BP_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.PC_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.SENS_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.CAL_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.SR_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.TM_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                    d.Subscribe(ResponseTypes.AC_RSP, new Decoder.ResponseHandler(DecoderCallback));
                                }
                                // If not connected send the connect event
                                Send(KernelResponse.CONNECTED, applicationGuid);
                            }
                            else // if already connected send the connected event
                                Send(KernelResponse.CONNECTED, applicationGuid);

                        }

                    }
                    catch (Exception e)
                    {
                        Send(KernelResponse.CONNECT_FAILED, applicationGuid);
                        Logger.Error("Booter.cs:ApplicationHandler: CONNECT:" + e.ToString());
                    }
                }
                #endregion CONNECT

                #region DISCONNECT
                else if (msg == KernelCommand.DISCONNECT.ToString())
                {
                    try
                    {
                        if (_WocketsRunning)
                        {
                            CurrentWockets._Controller.Dispose();
                            _WocketsRunning = false;
                            Send(KernelResponse.DISCONNECTED, applicationGuid);
                        }
                        else
                            Send(KernelResponse.DISCONNECTED, applicationGuid);

                    }
                    catch (Exception e)
                    {
                        Send(KernelResponse.DISCONNECT_FAILED, applicationGuid);
                        Logger.Error("Booter.cs:ApplicationHandler: DISCONNECT:" + e.ToString());
                    }

                }
                #endregion DISCONNECT

                #region SET_WOCKETS
                else if (msg == KernelCommand.SET_WOCKETS.ToString())
                {
                    try
                    {
                        if (!_WocketsRunning)
                        {
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
                            Send(KernelResponse.SENSORS_UPDATED, applicationGuid);
                        }
                        else
                            Send(KernelResponse.SENSORS_UPDATED_FAILED, applicationGuid);
                    }
                    catch (Exception e)
                    {
                        Send(KernelResponse.SENSORS_UPDATED_FAILED, applicationGuid);
                        Logger.Error("Booter.cs:ApplicationHandler: SET_WOCKETS:" + e.ToString());
                    }
                }
                #endregion SET_WOCKETS

                #region GET_BATTERY_LEVEL
                else if (msg == KernelCommand.GET_BATTERY_LEVEL.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_BT();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_BATTERY_LEVEL:" + e.ToString());
                        }
                    }
                }
                #endregion GET_BATTERY_LEVEL

                #region GET_BATTERY_PERCENT
                else if (msg == KernelCommand.GET_BATTERY_PERCENT.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_BP();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }

                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_BATTERY_PERCENT:" + e.ToString());
                        }
                    }
                }
                #endregion GET_BATTERY_PERCENT

                #region GET_PDU_COUNT
                else if (msg == KernelCommand.GET_PDU_COUNT.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_PC();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_PDU_COUNT:" + e.ToString());
                        }
                    }
                }
                #endregion GET_PDU_COUNT

                #region GET_WOCKET_SENSITIVITY
                else if (msg == KernelCommand.GET_WOCKET_SENSITIVITY.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_SEN();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_WOCKET_SENSITIVITY:" + e.ToString());
                        }
                    }
                }

                #endregion GET_WOCKET_SENSITIVITY

                #region SET_WOCKET_SENSITIVITY
                else if (msg == KernelCommand.SET_WOCKET_SENSITIVITY.ToString())
                {
                    if (_WocketsRunning)
                    {

                        try
                        {
                            string[] tokens = param.Split(new char[] { ':' });
                            Sensitivity sensitivity = (Sensitivity)Enum.Parse(typeof(Sensitivity),
                               tokens[1], true);
                            Command command = new SET_SEN(sensitivity);
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (tokens[0] == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == tokens[0])
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_WOCKET_SENSITIVITY:" + e.ToString());
                        }
                    }
                }
                #endregion SET_WOCKET_SENSITIVITY

                #region GET_WOCKET_CALIBRATION
                else if (msg == KernelCommand.GET_WOCKET_CALIBRATION.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_CAL();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_WOCKET_CALIBRATION:" + e.ToString());
                        }
                    }
                }

                #endregion GET_WOCKET_CALIBRATION

                #region SET_WOCKET_CALIBRATION
                else if (msg == KernelCommand.SET_WOCKET_CALIBRATION.ToString())
                {
                    if (_WocketsRunning)
                    {

                        try
                        {
                            string[] tokens = param.Split(new char[] { ':' });
                            string mac = tokens[0];
                            Calibration calibration = new Calibration();
                            calibration._X1G = (ushort)Convert.ToUInt32(tokens[1]);
                            calibration._XN1G = (ushort)Convert.ToUInt32(tokens[2]);
                            calibration._Y1G = (ushort)Convert.ToUInt32(tokens[3]);
                            calibration._YN1G = (ushort)Convert.ToUInt32(tokens[4]);
                            calibration._Z1G = (ushort)Convert.ToUInt32(tokens[5]);
                            calibration._ZN1G = (ushort)Convert.ToUInt32(tokens[6]);
                            Command command = new SET_CAL(calibration);
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == mac)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_WOCKET_CALIBRATION:" + e.ToString());
                        }
                    }
                }
                #endregion SET_WOCKET_CALIBRATION

                #region GET_WOCKET_SAMPLING_RATE
                else if (msg == KernelCommand.GET_WOCKET_SAMPLING_RATE.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_SR();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_WOCKET_SAMPLING_RATE:" + e.ToString());
                        }
                    }
                }

                #endregion GET_WOCKET_SAMPLING_RATE

                #region SET_WOCKET_SAMPLING_RATE
                else if (msg == KernelCommand.SET_WOCKET_SAMPLING_RATE.ToString())
                {
                    if (_WocketsRunning)
                    {

                        try
                        {
                            string[] tokens = param.Split(new char[] { ':' });
                            Command command = new SET_SR(Convert.ToInt32(tokens[1]));
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (tokens[0] == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == tokens[0])
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_WOCKET_SAMPLING_RATE:" + e.ToString());
                        }
                    }
                }
                #endregion SET_WOCKET_SAMPLING_RATE

                #region GET_WOCKET_POWERDOWN_TIMEOUT
                else if (msg == KernelCommand.GET_WOCKET_POWERDOWN_TIMEOUT.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_PDT();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_WOCKET_SAMPLING_RATE:" + e.ToString());
                        }
                    }
                }

                #endregion GET_WOCKET_POWERDOWN_TIMEOUT

                #region SET_WOCKET_POWERDOWN_TIMEOUT
                else if (msg == KernelCommand.SET_WOCKET_POWERDOWN_TIMEOUT.ToString())
                {
                    if (_WocketsRunning)
                    {

                        try
                        {
                            string[] tokens = param.Split(new char[] { ':' });
                            Command command = new SET_PDT(Convert.ToInt32(tokens[1]));
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (tokens[0] == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == tokens[0])
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_WOCKET_SAMPLING_RATE:" + e.ToString());
                        }
                    }
                }
                #endregion SET_WOCKET_POWERDOWN_TIMEOUT

                #region GET_TRANSMISSION_MODE
                else if (msg == KernelCommand.GET_TRANSMISSION_MODE.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                            Command command = new GET_TM();
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (param == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == param)
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_TRANSMISSION_MODE:" + e.ToString());
                        }
                    }
                }

                #endregion GET_TRANSMISSION_MODE

                #region SET_TRANSMISSION_MODE
                else if (msg == KernelCommand.SET_TRANSMISSION_MODE.ToString())
                {
                    if (_WocketsRunning)
                    {

                        try
                        {
                            string[] tokens = param.Split(new char[] { ':' });

                            TransmissionMode mode = (TransmissionMode)Enum.Parse(typeof(TransmissionMode),
                                tokens[1], true);

                            if (mode == TransmissionMode.Continuous)
                                CurrentWockets._Continuous = true;
                            Command command = new SET_TM(mode);
                            for (int i = 0; (i < CurrentWockets._Controller._Receivers.Count); i++)
                            {
                                if (tokens[0] == "all")
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address == tokens[0])
                                {
                                    ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                    break;
                                }
                            }
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_TRANSMISSION_MODE:" + e.ToString());
                        }
                    }
                }
                #endregion SET_TRANSMISSION_MODE

                #region GET_MEMORY_MODE
                else if (msg == KernelCommand.GET_MEMORY_MODE.ToString())
                {
                    if (_WocketsRunning)
                    {
                        try
                        {
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: GET_TRANSMISSION_MODE:" + e.ToString());
                        }
                    }
                }

                #endregion GET_MEMORY_MODE

                #region SET_MEMORY_MODE
                else if (msg == KernelCommand.SET_MEMORY_MODE.ToString())
                {
                    if (_WocketsRunning)
                    {

                        try
                        {
                            MemoryMode mode = (MemoryMode)Enum.Parse(typeof(MemoryMode),
                                param.Split(new char[] { ':' })[1], true);
                            CurrentWockets._Controller._Mode = mode;
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Booter.cs:ApplicationHandler: SET_MEMORY_MODE:" + e.ToString());
                        }
                    }
                }
                #endregion SET_MEMORY_MODE

                kernelLock.Release();

                namedEvent.Reset();
            }
        }
        
        /// <summary>
        /// Handler to process pre-registration messages from applications
        /// </summary>
        private static void CommandHandler()
        {
            NamedEvents namedEvent = new NamedEvents();

            while (true)
            {
                //ensures prior synchronization
                namedEvent.Receive(Channels.COMMAND.ToString());
                kernelLock.WaitOne();
                //lock (registryLock)
                //{
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(Core.COMMAND_CHANNEL, true);
                string msg = (string)rk.GetValue("Message");//, KernelNamedEvents.REGISTER.ToString(), RegistryValueKind.DWord);
                string param = (string)rk.GetValue("Param");//, processID.ToString(), RegistryValueKind.DWord);        
                rk.Close();

                if (msg == KernelCommand.PING.ToString())
                {
                    Send(KernelResponse.PING_RESPONSE, param);
                 //   Broadcast(KernelResponse.PING_RESPONSE);
                }
                else if (msg == KernelCommand.TERMINATE.ToString())
                {


                    rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
                    rk.SetValue("Status", 0, RegistryValueKind.DWord);
                    rk.Close();
                    Logger.Close();
                    Send(KernelResponse.STOPPED, param);
                    //Broadcast(KernelResponse.STOPPED);
                    System.Diagnostics.Process.GetCurrentProcess().Close();
                    System.Diagnostics.Process.GetCurrentProcess().Kill();
                }
                else if (msg == KernelCommand.REGISTER.ToString())
                {
                    if (!applicationThreads.ContainsKey(param))
                    {
                        //spawn the processing thread
                        Thread applicationThread = new Thread(new ThreadStart(ApplicationHandler));
                        applicationPaths.Add(applicationThread.ManagedThreadId, param);
                        applicationThreads.Add(param, applicationThread);
                        applicationThread.Start();
                        _NumRegistrations++;

                        rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);
                        rk.SetValue("Count", _NumRegistrations, RegistryValueKind.DWord);
                        rk.Close();
                        Send(KernelResponse.REGISTERED, param);
                        //Broadcast(KernelResponse.REGISTERED);
                    }
                }
                else if (msg == KernelCommand.UNREGISTER.ToString())
                {


                    //Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + param + "}");

                    if (applicationThreads.ContainsKey(param))
                    {
                        //kill the processing thread
                        applicationPaths.Remove(((Thread)applicationThreads[param]).ManagedThreadId);
                        ((Thread)applicationThreads[param]).Abort();
                        applicationThreads.Remove(param);
                        _NumRegistrations--;

                        rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);
                        rk.SetValue("Count", _NumRegistrations, RegistryValueKind.DWord);
                        rk.Close();
                        //Broadcast(KernelResponse.UNREGISTERED);
                        Send(KernelResponse.UNREGISTERED, param);
                    }
                }
                //}
                kernelLock.Release();
                namedEvent.Reset();
            }

        }

        /// <summary>
        /// Guid of application requesting wockets to be discovered
        /// </summary>
        private static string discoveryGuid="";

        /// <summary>
        /// Initiates wockets discovery and updates the registry
        /// </summary>
        private static void Discover()
        {
            kernelLock.WaitOne();
            try
            {
                Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
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
                        hex = devices[i].DeviceAddress.ToString();
                        RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH + "\\" + wocketCount.ToString("00"));
                        rk.SetValue("Name", devices[i].DeviceName, RegistryValueKind.String);
                        rk.SetValue("MacAddress", hex, RegistryValueKind.String);
                        rk.Close();

                        wocketCount++;
                    }
                }
                //Send to the appropriate application a response
                //Send(KernelResponse.DISCOVERED, discoveryGuid);
                foreach (string guid in applicationPaths.Values)
                    Send(KernelResponse.DISCOVERED, guid);
            }
            catch (Exception e)
            {
                Logger.Error("Booter.cs: "+ e.ToString());
            }
            kernelLock.Release();
        }

        /// <summary>
        /// Sends a kernel response to a specific application
        /// </summary>
        /// <param name="response">Kernel response</param>
        /// <param name="senderGuid">Guid of the sender application</param>
        public static void Send(KernelResponse response, string senderGuid)
        {
            try
            {
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + senderGuid + "}");
                rk.SetValue("Message", response.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", "", RegistryValueKind.String);
                rk.Close();
                NamedEvents namedEvent = new NamedEvents();
                namedEvent.Send(senderGuid+"-"+response.ToString());
            }
            catch (Exception e)
            {
                Logger.Error("Booter.cs:Send: " + e.ToString());
            }
        }

        /// <summary>
        /// Broadcast a kernel response to a specific application
        /// </summary>
        /// <param name="response">Kernel response</param>
        public static void Broadcast(KernelResponse response)
        {
            NamedEvents namedEvent = new NamedEvents();
            namedEvent.Send(Core.BROADCAST_EVENT_PREFIX + response.ToString());
        }

        
        /// <summary>
        /// Initializes kernel's registry for the first time
        /// </summary>
        private static void Initialize()
        {

            //If the kernel crashed or an application crashed while locking a semaphore then restarting the kernel should ensures
            //that the lock is released            
            //registryLock.Release();

            //Always attempt to delete registered applications
            //at the beginning
            //this will fail only if the registry tree is being accessed at that time (i.e. not writable)            
            kernelLock.WaitOne();

            try
            {
                Registry.LocalMachine.DeleteSubKeyTree(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);
                RegistryKey rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_WOCKETS_PATH + "\\Kernel");
                rk.SetValue("Handle", 00000, RegistryValueKind.DWord);
                rk.SetValue("OnBoot", 1, RegistryValueKind.DWord);
                rk.SetValue("Status", 1, RegistryValueKind.DWord);
                rk.SetValue("Storage", "", RegistryValueKind.String);
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
                    rk.SetValue("Status", 0, RegistryValueKind.DWord);
                    rk.Close();
                }

                rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_DISCOVERED_SENSORS_PATH);
                rk.Flush();
                rk.Close();
                rk = Registry.LocalMachine.CreateSubKey(Core.REGISTRY_REGISTERED_APPLICATIONS_PATH);
                rk.SetValue("Count", 0, RegistryValueKind.DWord);
                rk.Flush();
                rk.Close();
            }
            catch (Exception e)
            {
                Logger.Error("Booter.cs:Initialize: " + e.ToString());
            }
            kernelLock.Release();
        }
    }
}
