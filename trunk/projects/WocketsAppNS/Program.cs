using System;
using System.Collections.Generic;
using System.Windows.Forms;
using System.Diagnostics;

namespace WocketsAppNS
{
    static class Program
    {
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        //[MTAThread]
        static void Main()
        {

            //Console.WriteLine("    new priority class: {0}", thisProc.PriorityClass);
            //if (WocketsApplication.Utils.Platform.NativeMethods.GetPlatformType()=="PocketPC")                
            Application.Run(new WocketsForm());

        }
    }
}