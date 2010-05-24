using System;
using System.Collections.Generic;
using System.Text;
using System.Runtime.InteropServices;

namespace WocketsApplication.Feedback
{
    public class Sound
    {
        private string m_fileName;

        private enum Flags
        {
            SND_SYNC = 0x0000,  /* play synchronously (default) */
            SND_ASYNC = 0x0001,  /* play asynchronously */
            SND_NODEFAULT = 0x0002,  /* silence (!default) if sound not found */
            SND_MEMORY = 0x0004,  /* pszSound points to a memory file */
            SND_LOOP = 0x0008,  /* loop the sound until next sndPlaySound */
            SND_NOSTOP = 0x0010,  /* don't stop any currently playing sound */
            SND_NOWAIT = 0x00002000, /* don't wait if the driver is busy */
            SND_ALIAS = 0x00010000, /* name is a registry alias */
            SND_ALIAS_ID = 0x00110000, /* alias is a predefined ID */
            SND_FILENAME = 0x00020000, /* name is file name */
            SND_RESOURCE = 0x00040004  /* name is resource name or atom */
        }

        [DllImport("CoreDll.DLL", EntryPoint = "PlaySound", SetLastError = true)]
        private extern static int WCE_PlaySound(string szSound, IntPtr hMod, int flags);

        /// <summary>
        /// Construct the Sound object to play sound data from the specified file.
        /// </summary>
        public Sound(string fileName)
        {
            m_fileName = fileName;
        }

        /// <summary>
        /// Play the sound
        /// </summary>
        public void Play()
        {
            // if a file name has been registered, call WCE_PlaySound,
            //  otherwise call WCE_PlaySoundBytes
            if (m_fileName != null)
                WCE_PlaySound(m_fileName, IntPtr.Zero, (int)(Flags.SND_ASYNC | Flags.SND_FILENAME));
        }
        public void LoopPlay()
        {
            // if a file name has been registered, call WCE_PlaySound,
            //  otherwise call WCE_PlaySoundBytes
            if (m_fileName != null)
                WCE_PlaySound(m_fileName, IntPtr.Zero, (int)(Flags.SND_ASYNC | Flags.SND_FILENAME | Flags.SND_LOOP));
        }

        public void Stop()
        {
            WCE_PlaySound(null, IntPtr.Zero, (int)(Flags.SND_ASYNC));
        }
    }
}