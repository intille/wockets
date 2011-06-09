using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using System.Runtime.InteropServices;

namespace CollectData
{
    public partial class ParentScreen : Form
    {
        public ParentScreen()
        {
            InitializeComponent();
            Screens.screen1 = new Screen1();
            Screens.screen1.Show();

        }

    }
}