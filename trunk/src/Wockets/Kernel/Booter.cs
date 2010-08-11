using System;
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
            wcontroller._Mode = MemoryMode.BluetoothToShared;

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
                        Broadcast(KernelResponse.STARTED);
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


        private static void DecoderCallback(object e)
        {
            Response response = (Response)e;
            switch (response._Type)
            {
                case ResponseTypes.BL_RSP: //write to the registry
                    try
                    {
                        Broadcast(KernelResponse.BATTERY_LEVEL_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;

                case ResponseTypes.BP_RSP: //write to the registry
                    try
                    {
                        Broadcast(KernelResponse.BATTERY_PERCENT_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;

                case ResponseTypes.PC_RSP: //write to the registry
                    try
                    {           
                        Broadcast(KernelResponse.PC_COUNT_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                case ResponseTypes.SENS_RSP: //write to the registry
                    try
                    {        
                        Broadcast(KernelResponse.SENSITIVITY_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                case ResponseTypes.CAL_RSP: //write to the registry
                    try
                    {     
                        Broadcast(KernelResponse.CALIBRATION_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;

                case ResponseTypes.SR_RSP: //write to the registry
                    try
                    {
                        Broadcast(KernelResponse.SAMPLING_RATE_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                case ResponseTypes.TM_RSP: //write to the registry
                    try
                    {
                        Broadcast(KernelResponse.TRANSMISSION_MODE_UPDATED);
                    }
                    catch
                    {                     
                    }
                    break;

                case ResponseTypes.AC_RSP: //write to the registry
                    try
                    {                       
                        Broadcast(KernelResponse.ACTIVITY_COUNT_UPDATED);
                    }
                    catch
                    {                        
                    }
                    break;
                default:
                    break;
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

                    #region CONNECT
                    if (msg == KernelCommand.CONNECT.ToString())
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
                                    registryLock.WaitOne();
                                    rk = Registry.LocalMachine.OpenSubKey(Core.REGISTRY_KERNEL_PATH, true);
                                    rk.SetValue("Storage", storageDirectory);
                                    rk.Close();
                                    registryLock.Release();

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
                                    Send(KernelResponse.CONNECTED, applicationGuid);
                                }
                              //  else
                                //    Send(ApplicationResponse.CONNECT_FAILURE, applicationGuid);

                                Broadcast(KernelResponse.CONNECTED);                                
                            }
                           // else
                             //   Send(ApplicationResponse.CONNECT_FAILURE, applicationGuid);
                        }
                        catch (Exception e)
                        {
                            Broadcast(KernelResponse.DISCONNECTED);
                            Logger.Error("Failure: Booter.cs: CONNECT:" + e.ToString());
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
                                Broadcast(KernelResponse.DISCONNECTED);
                            }
                           // else
                             //   Send(ApplicationResponse.DISCONNECT_FAILURE, applicationGuid);
                           
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Failure: Booter.cs: DISCONNECT:" + e.ToString());
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
                                Send(KernelResponse.SENSORS_UPDATED, applicationGuid);
                                Broadcast(KernelResponse.SENSORS_UPDATED);
                            }
                            //else
                              //  Send(ApplicationResponse.SET_SENSORS_FAILURE, applicationGuid);
                        }
                        catch (Exception e)
                        {
                            Logger.Error("Failure: Booter.cs: SET_WOCKETS:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_BATTERY_LEVEL:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: SET_BATTERY_PERCENT:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_PDU_COUNT:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_WOCKET_SENSITIVITY:" + e.ToString());
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
                                    else if (((RFCOMMReceiver)CurrentWockets._Controller._Receivers[i])._Address ==tokens[0])
                                    {
                                        ((SerialReceiver)CurrentWockets._Controller._Receivers[i]).Write(command._Bytes);
                                        break;
                                    }
                                }
                            }
                            catch (Exception e)
                            {
                                Logger.Error("Failure: Booter.cs: SET_WOCKET_SENSITIVITY:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_WOCKET_CALIBRATION:" + e.ToString());
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
                                calibration._X1G = (ushort) Convert.ToUInt32(tokens[1]);
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
                                Logger.Error("Failure: Booter.cs: SET_WOCKET_CALIBRATION:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_WOCKET_SAMPLING_RATE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: SET_WOCKET_SAMPLING_RATE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_WOCKET_SAMPLING_RATE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: SET_WOCKET_SAMPLING_RATE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_TRANSMISSION_MODE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: SET_TRANSMISSION_MODE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: GET_TRANSMISSION_MODE:" + e.ToString());
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
                                Logger.Error("Failure: Booter.cs: SET_MEMORY_MODE:" + e.ToString());
                            }
                        }
                    }
                    #endregion SET_MEMORY_MODE
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
                        Broadcast(KernelResponse.REGISTERED);
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
                        Broadcast(KernelResponse.UNREGISTERED);
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
                Send(KernelResponse.DISCOVERED, discoveryGuid);
                Broadcast(KernelResponse.DISCOVERED);

            }
        }

        //send a response to a specific application
        public static void Send(KernelResponse response, string senderGuid)
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

        //Broadcast the response to everyone
        public static void Broadcast(KernelResponse response)
        {
            NamedEvents namedEvent = new NamedEvents();
            namedEvent.Send(Core.BROADCAST_EVENT_PREFIX + response.ToString());
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
