using System;
using System.Collections.Generic;
using System.Windows.Forms;

namespace DataMerger
{
    static class Program
    {
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [STAThread]
        static void Main(string[] args)
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            if (args.Length > 0)
            {
                try
                {
                    System.IO.DirectoryInfo di = new System.IO.DirectoryInfo(args[0]);
                    Application.Run(new Form1(di));
                }
                catch
                {
                    Application.Run(new Form1());
                }
            }
            else
            {
                Application.Run(new Form1());
            }
        }
    }
}