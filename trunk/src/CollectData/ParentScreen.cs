using System;
using System.Linq;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace CollectData
{
    public partial class ParentScreen : Form
    {
        public ParentScreen()
        {
            InitializeComponent();
            this.Size = new Size(0, 0);
            this.Visible = false;            
            Screens.screen1 = new Screen1();
            Screens.screen1.Show();
        }
    }
}