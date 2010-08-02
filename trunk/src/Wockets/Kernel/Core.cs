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
                rk.SetValue("Message", KernelCommand.GET_BATTERY_PERCENT.ToString(), RegistryValueKind.String);
                rk.SetValue("Param", mac.ToString() + ":" + sr.ToString(), RegistryValueKind.String);
                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
                success = true;
            }
            return success;
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


        public static bool SET_TRANSMISSION_MODE(string channel, string mac, TransmissionMode mode)
        {
            bool success = false;
            if ((_Registered) && (_Connected))
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_WOCKET_POWERDOWN_TIMEOUT.ToString(), RegistryValueKind.String);
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


        public static bool SET_TRANSMISSION_MODE(string channel, string mac, MemoryMode mode)
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
