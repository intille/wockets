using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using Microsoft.WindowsCE.Forms;

namespace WocketsApplication.Controls.Utils
{
    public class Keyboard
    {
        private static InputPanel m_inputPanel = new InputPanel();
        public static bool KeyboardOpen
        {
            get { return m_inputPanel.Enabled; }
            set { m_inputPanel.Enabled = value; }
        }
    }
}
