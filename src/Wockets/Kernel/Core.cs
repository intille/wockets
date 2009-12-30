using System;
using System.Collections;
using System.Threading;
using Wockets.IPC;
using Wockets.Kernel.Types;
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
        public static string REGISTRY_LOCK = "WocketsRLock";
        private static Semaphore registryLock;
        public static bool _Registered = false;


        static Core()
        {
            registryLock = new Semaphore(1, 1, REGISTRY_LOCK);
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
        public static bool SetSniff(string channel, SleepModes mode)
        {
            bool success = false;
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();

                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_SNIFF.ToString(), RegistryValueKind.String);     
                rk.SetValue("Param", mode.ToString(), RegistryValueKind.String);


                rk.Flush();
                rk.Close();
                registryLock.Release();
                namedEvent.Send(channel + "-kernel");
            }
            return success;
        }
        public static void SetSensors(string channel, ArrayList s)
        {
            if (_Registered)
            {
                string commandPath = REGISTRY_REGISTERED_APPLICATIONS_PATH + "\\{" + channel + "}";
                NamedEvents namedEvent = new NamedEvents();
                registryLock.WaitOne();
                RegistryKey rk = Registry.LocalMachine.OpenSubKey(commandPath, true);
                rk.SetValue("Message", KernelCommand.SET_SENSORS.ToString(), RegistryValueKind.String);
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
        public static string Register()
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
                return guid;
            }
            else
                return null;
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
    }
}
