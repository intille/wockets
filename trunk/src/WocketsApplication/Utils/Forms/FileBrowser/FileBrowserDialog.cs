//
// Common Dialog wrapper class for FileBrowserForm
// Designed to follow object model of desktop framework control
// (c) 2004 Peter Foot, OpenNETCF
//
using System;
using System.Windows.Forms;
using WocketsApplication;

namespace WocketsApplication.Utils.Forms.FileBrowser
{
    /// <summary>
    /// Represents a common dialog box that allows the user to choose a File.
    /// </summary>
    public class FileBrowserDialog : CommonDialog
    {
        private FileBrowserForm m_dialog;



        /// <summary>
        /// Initializes a new instance of the OpenNETCF.Windows.Forms.FileBrowserDialog class.
        /// </summary>
        public FileBrowserDialog()
        {
            m_dialog = new FileBrowserForm();
        }

        /// <summary>
        /// Runs a common dialog box with a default owner.
        /// </summary>
        /// <returns></returns>
        public new DialogResult ShowDialog()
        {
            return m_dialog.ShowDialog();
        }

        public void Show()
        {
            m_dialog.Show();
        }


        public void Cleanup()
        {
            m_dialog.Cleanup();
        }
        /// <summary>
        /// Resets properties to their default values.
        /// </summary>
        /// 
#if (PocketPC)
        public void Reset()
#else
        public override void Reset()
#endif

        {
            m_dialog.Reset();
        }

        public string SelectedFile
        {
            get
            {
                return m_dialog.SelectedFile;
            }
        }
        /// <summary>
        /// Gets or sets the path selected by the user.
        /// </summary>
        public string SelectedPath
        {
            get
            {
                return m_dialog.SelectedPath;
            }
            set
            {
                m_dialog.SelectedPath = value;
            }
        }

        /// <summary>
        /// Gets or sets a value indicating whether the New File button appears in the File browser dialog box.
        /// </summary>
        public bool ShowNewFolderButton
        {
            get
            {
                return m_dialog.ShowNewFolderButton;
            }
            set
            {
                m_dialog.ShowNewFolderButton = value;
            }
        }

        /// <summary>
        /// </summary>
        public void Dispose()
        {
            m_dialog.Dispose();
        }

#if (PocketPC)
        protected bool RunDialog(System.IntPtr hwndOwner)
#else
        protected override bool RunDialog(System.IntPtr hwndOwner)
#endif

        {
            return true;
        }
    }
}
