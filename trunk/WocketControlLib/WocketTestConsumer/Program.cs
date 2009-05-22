using System;
using System.Collections.Generic;
using System.Windows.Forms;
using System.Diagnostics;

namespace WocketTestConsumer
{
    static class Program
    {
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [MTAThread]
        static void Main()
        {
            Application.Run(new ConsumerForm());
            //Application.Exit();
            //throw new Exception();
            //Process.GetCurrentProcess().Close();
            //Process.GetCurrentProcess().Kill();
            //Process.GetCurrentProcess().Kill();
        }
    }
}