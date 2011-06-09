//
// Common Dialog wrapper class for FolderBrowserForm
// Designed to follow object model of desktop framework control
// (c) 2004 Peter Foot, OpenNETCF
//
using System;
using System.Windows.Forms;

namespace WocketsApplication.Utils.Forms.FileBrowser
{
	/// <summary>
	/// Represents a common dialog box that allows the user to choose a folder.
	/// </summary>
	public class FolderBrowserDialog : CommonDialog
	{
		private FolderBrowserForm m_dialog;
        

		/// <summary>
		/// Initializes a new instance of the OpenNETCF.Windows.Forms.FolderBrowserDialog class.
		/// </summary>
        public FolderBrowserDialog()
		{
			m_dialog = new FolderBrowserForm();            

            
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

		/// <summary>
		/// Resets properties to their default values.
		/// </summary>
#if (PocketPC)
        public void Reset()
#else
        public override void Reset()
#endif
		{
			m_dialog.Reset();
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
		/// Gets or sets a value indicating whether the New Folder button appears in the folder browser dialog box.
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
