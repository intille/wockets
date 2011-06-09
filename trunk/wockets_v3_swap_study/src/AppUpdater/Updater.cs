using System;
using System.Collections;//ArrayList
using System.Text;

using System.Threading; //Thread.Sleep
using System.IO; //File Exists, Create Directory, etc.
using ICSharpCode.SharpZipLib.Zip;//Decompress
using System.Reflection; //Assembly
using System.Runtime.InteropServices;//PInvoke Exe Launch

//using Microsoft.WindowsCE.Forms;
//using System.Diagnostics;
using System.Collections.Generic; //List
using System.Security.Permissions;

namespace AppUpdater
{

    #region EVENT HANDLERS
    public delegate void StatusHandler(string status);
    public delegate void LogErrorHandler(string codeLocation, Exception ex);
    public delegate void LogHandler(string logevent);
    #endregion

    public class Updater
    {
  
        #region STATUS variables
        private string _status = "";
        private DateTime _dtLastUpdated = new DateTime();
        private DateTime _dtLastDownload = new DateTime();
        #endregion

        #region APPLICATION variables
        private string _pathApplicationFolder = "";
        private string _applicationExe = "";
        
        private string _pathDownloadFolder = "";
        #endregion

        #region FILE LIST
        struct downloadFile
        {
            public string filename;
            public string URL;
            public string path;
            public DateTime lastModified;
        }
        private ArrayList _alToDownload = new ArrayList();
        #endregion

        #region EVENT HANDLERS
        public event StatusHandler StatusChanged;        
        public event LogHandler LogItemGenerated;
        public event LogErrorHandler LogErrorGenerated;
        #endregion

        #region PROPERTIES
        public string DownloadFolderPath
        {
            get { return _pathDownloadFolder; }
            set
            {
                _pathDownloadFolder = value;
                if (!Directory.Exists(_pathDownloadFolder))
                    Directory.CreateDirectory(_pathDownloadFolder);
            }
        }
        public string ApplicationFolderPath
        {
            get { return _pathApplicationFolder; }
            set
            {
                _pathApplicationFolder = value;
                DownloadFolderPath = Path.Combine(_pathApplicationFolder, "updater_temp");
            }
        }
        public string ApplicationExe
        {
            get { return _applicationExe; }
            set { _applicationExe = value; }
        }
        #endregion

        #region PUBLIC METHODS
        public void RetrieveUpdates(string[] urls)
        {
            if (_pathApplicationFolder.Length > 0)
            {
                RetrieveLastDownload();
                RetrieveLastUpdated();

                _alToDownload = new ArrayList();
                for (int i = 0; i < urls.Length; i++)
                {
                    MarkForDownload(urls[i]);
                }

                bool successDownloading = DownloadFiles();
                if (successDownloading) UnzipFiles();
            }
            else OnErrorGenerated("Run", new Exception("No application folder specified"));

        }

#if (!PC)
        public void UpdateApplication()
        {
            if (_pathApplicationFolder.Length > 0)
            {
                //delay in case app is closing
                for (int i = 0; i < 20; i++) Thread.Sleep(100);

                if (_applicationExe.Length > 0)
                {
                    //KillIfRunning(_applicationExe);
                    TerminateApp(_applicationExe);

                    //Wait for receive msg that application has closed successfully
                }

                ////delay to give files chance to unlock
                //for (int i = 0; i < 20; i++) Thread.Sleep(100);

                //bool isError = false;
                //isError = RemoveDeletedFiles();
                //if (!isError)
                //    isError = ReplaceFiles();

                //#region IF NO ERRORS, RECORD UPDATED
                //if (!isError)
                //{
                //    _dtLastUpdated = _dtLastDownload;
                //    SaveLastUpdated();
                //    OnNoteGenerated("update successful");
                //}
                //#endregion

                //ClearDownloadFolder();
                ////if (_applicationExe.Length > 0)
                ////   LaunchApplication();


            }
            else OnErrorGenerated("UpdateApplication", new Exception("No application folder specified"));
        }
#endif

        public bool IsReadyToUpdate()
        {
            bool isReady = false;
            
            if (Directory.Exists(_pathDownloadFolder))
            {
                if ((Directory.GetFiles(_pathDownloadFolder).Length > 0) || (Directory.GetDirectories(_pathDownloadFolder).Length > 0))
                {
                    ArrayList alZippedFiles = BuildFileArray(_pathDownloadFolder, false, true, "*.zip");
                    isReady = alZippedFiles.Count == 0;
                }
            }

            return isReady;
        }
        public bool IsFileDownloaded(string filePath)
        {
            bool isDownloaded = false;
            try
            {
                filePath = filePath.Replace(_pathApplicationFolder, "");
                isDownloaded = File.Exists(Path.Combine(_pathDownloadFolder, filePath));
            }
            catch (Exception ex)
            {
                OnErrorGenerated("IsAppUpdaterUpdateDownloaded", ex);
            }

            return isDownloaded;
        }
        public bool ReplaceSpecificFile(string filePath)
        {
            bool isSuccess = false;

            string pathToTransfer = Path.Combine(_pathDownloadFolder, filePath.Replace(_pathApplicationFolder, ""));
            if (File.Exists(pathToTransfer))
            {
                try
                {
                    bool isAdding = true;
                    #region DELETE EXISTING FILE
                    if (File.Exists(filePath))
                    {
                        File.Delete(filePath);
                        isAdding = false;
                    }
                    else if (!Directory.Exists(Path.GetDirectoryName(filePath)))
                    {
                        Directory.CreateDirectory(Path.GetDirectoryName(filePath));
                    }
                    #endregion

                    #region MOVE NEW FILE
                    File.Move(pathToTransfer, filePath);
                    if (isAdding)
                        OnNoteGenerated("Add new file " + filePath);
                    else OnNoteGenerated("Update existing file " + filePath);
                    #endregion

                    isSuccess = true;
                }
                catch (Exception ex)
                {
                    OnErrorGenerated("ReplaceSpecificFile " + filePath, ex);
                }
            }
            else OnErrorGenerated("ReplaceSpecificFile path does not exist" + pathToTransfer, null);

            return isSuccess;
        }


        #endregion

        #region PRIVATE METHODS

        #region ACTION METHODS
        private ArrayList FilesOnServer(string url)
        {

            ArrayList alFilesAtUrl = new ArrayList();

            OnStatusChange("Contacting server");
            int countTries = 0; bool successGetlist = false;
            while (!successGetlist && (countTries < 3))
            {
                if (countTries > 0) OnStatusChange("Contacting server, try " + (countTries + 1));
                try
                {
                    alFilesAtUrl = Downloader.GetDirectoryContents(url);
                    successGetlist = true;
                }
                catch
                {
                    countTries++;
                    if (countTries < 3) Thread.Sleep(countTries * 1000);//1 second, 2 seconds
                }
            }

            return alFilesAtUrl;

        }

        private void MarkForDownload(string url)
        {
            ArrayList alFilesAtUrl = FilesOnServer(url);
            if (alFilesAtUrl.Count > 0)
            {
                OnStatusChange("Comparing files");               

                for (int i = 0; i < alFilesAtUrl.Count; i++)
                {

                    Downloader.Resource rsFile = ((Downloader.Resource)alFilesAtUrl[i]);
                    string pathRelative = rsFile.Url.Replace(url, "").Trim('\\').Trim('/');

                    if (rsFile.Name.EndsWith("-delete") || (pathRelative.IndexOf("-delete") > -1))
                    {

                        #region MARK for delete
                        if (rsFile.LastModified > _dtLastUpdated)
                        {
                            if (rsFile.IsFolder)
                            {
                                #region CREATE DUMMY FOLDER TO MARK DELETE
                                string pathDownload = Path.Combine(_pathDownloadFolder, pathRelative);
                                if (!Directory.Exists(pathDownload)) Directory.CreateDirectory(pathDownload);
                                #endregion
                            }
                            else
                            {
                                #region CREATE DUMMY FILE TO MARK DELETE
                                pathRelative = pathRelative.Replace(rsFile.Name, "").Trim('\\').Trim('/');
                                string pathDownload = Path.Combine(_pathDownloadFolder, pathRelative);
                                if (!Directory.Exists(pathDownload)) Directory.CreateDirectory(pathDownload);
                                pathDownload = Path.Combine(pathDownload, RemoveZip(rsFile.Name));
                                SaveTextToFile(pathDownload, "delete");
                                #endregion
                            }
                            if (rsFile.LastModified > _dtLastDownload) _dtLastDownload = rsFile.LastModified;
                            SaveLastDownload();
                        }
                        #endregion
                    }
                    else
                    {
                        if (rsFile.IsFolder)
                        {
                            string pathFolder = Path.Combine(_pathDownloadFolder, pathRelative);
                            if (!Directory.Exists(pathFolder))
                            {
                                Directory.CreateDirectory(pathFolder);
                                OnNoteGenerated("MarkForDownload created directory at " + pathFolder);
                            }
                        }
                        else
                        {
                            #region resolve paths
                            pathRelative = pathRelative.Replace(rsFile.Name, "").Trim('\\').Trim('/');
                            string pathDownload = Path.Combine(_pathDownloadFolder, pathRelative);
                            if (!Directory.Exists(pathDownload)) Directory.CreateDirectory(pathDownload);
                            pathDownload = Path.Combine(pathDownload, rsFile.Name);

                            string pathFinal = Path.Combine(_pathApplicationFolder, pathRelative);
                            pathFinal = Path.Combine(pathFinal, RemoveZip(rsFile.Name));
                            #endregion

                            #region mark for download
                            //if file doesn't exist or server file updated since lastupdate, download
                            if ((!File.Exists(pathFinal) || (rsFile.LastModified > _dtLastUpdated))
                                && ((!File.Exists(pathDownload) && !File.Exists(RemoveZip(pathDownload))) || (rsFile.LastModified > _dtLastDownload)))
                            {
                                downloadFile dfile = new downloadFile();
                                dfile.filename = rsFile.Name;
                                dfile.URL = rsFile.Url;
                                dfile.lastModified = rsFile.LastModified;
                                dfile.path = pathDownload;
                                _alToDownload.Add(dfile);

                            }//mark for download
                            #endregion
                        }//file
                    }//not delete


                }//for each file
            }

        }

        private bool DownloadFiles()
        {
            bool wasErrorGetting = false;

            #region DOWNLOAD
            if (_alToDownload.Count > 0)
            {
                OnNoteGenerated("Download " + _alToDownload.Count + " files");

                OnStatusChange("Downloading files");


                int countFilesToGo = _alToDownload.Count;
                int countFilesDone = 0;

                while ((countFilesDone < countFilesToGo) && !wasErrorGetting)
                {
                    downloadFile dfile = (downloadFile)_alToDownload[countFilesDone];
                    #region DOWNLOAD
                    OnNoteGenerated("Downloading " + dfile.filename);
                    bool isDownloaded = false; int count_tries = 0;
                    while (!isDownloaded && (count_tries < 30))
                    {
                        try
                        {
                            Downloader.CopyToDisk(dfile.URL, dfile.path);
                            isDownloaded = true;
                        }
                        catch { }
                        if (!isDownloaded) { Thread.Sleep(5000); count_tries++; }
                    }
                    #endregion
                    #region UPDATE LastDownload DateTime
                    if (isDownloaded)
                    {
                        //use the date the file was last modified (on the server)
                        OnNoteGenerated("Downloaded " + dfile.path);
                        if (dfile.lastModified > _dtLastDownload) _dtLastDownload = dfile.lastModified;
                        SaveLastDownload();
                        countFilesDone++;
                    }
                    else wasErrorGetting = true;
                    #endregion

                }

            }
            else
            {
                OnNoteGenerated("No files to download");

            }
            #endregion

            return !wasErrorGetting;
        }

        private void UnzipFiles()
        {
            ArrayList alZippedFiles = BuildFileArray(_pathDownloadFolder, false, true, "*.zip");


            OnStatusChange("Unzipping files");
            OnNoteGenerated("Unzipping " + alZippedFiles.Count + " files");

            for (int i = 0; i < alZippedFiles.Count; i++)
            {
                string pathZip = alZippedFiles[i].ToString();
                if (IsZip(pathZip) && File.Exists(pathZip)) //Is existing zipped file
                {
                    try
                    {
                        string pathFolder = Path.GetDirectoryName(pathZip);
                        string filename = Decompress(pathZip, pathFolder);
                        File.Delete(pathZip); //delete zip file
                        OnNoteGenerated("Unzipped " + filename);
                    }
                    catch (Exception ex)
                    {
                        OnErrorGenerated("Decompress " + pathZip, ex);
                        //try once more
                        try
                        {
                            string filename = Decompress(pathZip, _pathDownloadFolder);
                            File.Delete(pathZip); //delete zip file 
                        }
                        catch (Exception ex2)
                        {
                            //if try 2 doesn't work, clear zip folder (assume problem with download)
                            OnErrorGenerated("Decompress 2nd try " + pathZip, ex2);
                            ClearDownloadFolder();
                        }

                    }

                }
            }
        }


        private bool RemoveDeletedFiles()
        {
            bool isError = false;
            OnStatusChange("Removing deleted files");

            ArrayList alDeleteFolders = BuildFileArray(_pathDownloadFolder, true, false, "");

            for (int i = 0; i < alDeleteFolders.Count; i++)
            {
                string pathDir = alDeleteFolders[i].ToString();
                if (pathDir.IndexOf("-delete") > -1)
                {
                    #region DETERMINE PATH
                    pathDir = pathDir.Replace("-delete", "");
                    pathDir = pathDir.Replace(_pathDownloadFolder, "").Trim('\\').Trim('/');

                    string pathFinal = Path.Combine(_pathApplicationFolder, pathDir);
                    #endregion
                    #region DELETE CORRESPONDING DIRECTORY
                    if (Directory.Exists(pathFinal))
                    {
                        try
                        {
                            Directory.Delete(pathFinal, true);
                            OnNoteGenerated("RemoveDeletedFiles delete folder " + pathFinal);
                        }
                        catch (Exception ex)
                        {
                            isError = true;
                            OnErrorGenerated("RemoveDeletedFiles delete folder " + pathFinal, ex);
                        }
                    }
                    #endregion
                    #region DELETE DIRECTORY MARKER
                    try
                    {
                        Directory.Delete(alDeleteFolders[i].ToString(), true);
                    }
                    catch (Exception ex)
                    {
                        OnErrorGenerated("RemoveDeletedFiles delete marker folder " + pathDir, ex);
                    }
                    #endregion


                }
            }

            ArrayList alDeleteFiles = BuildFileArray(_pathDownloadFolder, false, true, "*-delete");
            for (int i = 0; i < alDeleteFiles.Count; i++)
            {
                #region DETERMINE PATH
                string pathMarker = alDeleteFiles[i].ToString().Replace("-delete", "");
                string filename = Path.GetFileName(pathMarker);
                string pathRelative = pathMarker.Replace(_pathDownloadFolder, "").Trim('\\').Trim('/');
                pathRelative = pathRelative.Replace(filename, "");

                string pathFinal = Path.Combine(_pathApplicationFolder, pathRelative);
                pathFinal = Path.Combine(pathFinal, filename);
                #endregion

                #region DELETE CORRESPONDING FILE
                if (File.Exists(pathFinal))
                {
                    try
                    {
                        File.Delete(pathFinal);
                        OnNoteGenerated("RemoveDeletedFiles delete " + pathFinal);

                    }
                    catch (Exception ex)
                    {
                        isError = true;
                        OnErrorGenerated("RemoveDeletedFiles delete " + pathFinal, ex);
                    }
                }
                #endregion

                #region REMOVE MARKER
                try
                {
                    File.Delete(alDeleteFiles[i].ToString());
                }
                catch (Exception ex)
                {
                    OnErrorGenerated("RemoveDeletedFiles marker " + pathMarker, ex);
                }
                #endregion

            }
            return isError;
        }

        private bool ReplaceFiles()
        {
            bool isError = false;

            DeleteLastDownload();

            ArrayList alFilesToTransfer = BuildFileArray(_pathDownloadFolder, true, true, "*");

            if (alFilesToTransfer.Count > 0)
            {
                OnStatusChange("Replacing files");
                OnNoteGenerated("Replacing " + alFilesToTransfer.Count + " files");

                try
                {
                    for (int i = 0; i < alFilesToTransfer.Count; i++)
                    {
                        string pathTransfer = alFilesToTransfer[i].ToString();
                        if (!IsZip(pathTransfer))
                        {
                            if (File.Exists(pathTransfer)) //Is file
                            {
                                
                                string filename = Path.GetFileName(pathTransfer);
                                
                                #region DETERMINE PATH
                                string pathRelative = pathTransfer.Replace(_pathDownloadFolder, "").Trim('\\').Trim('/');
                                pathRelative = pathRelative.Replace(filename, "");

                                string pathFinal = Path.Combine(_pathApplicationFolder, pathRelative);
                                if (!Directory.Exists(pathFinal)) Directory.CreateDirectory(pathFinal);
                                pathFinal = Path.Combine(pathFinal, filename);
                                #endregion

                                bool isAdding = true;
                                #region DELETE EXISTING FILE
                                if (File.Exists(pathFinal))
                                {
                                    File.Delete(pathFinal);
                                    isAdding = false;
                                }
                                #endregion

                                #region MOVE NEW FILE
                                File.Move(pathTransfer, pathFinal);
                                if (isAdding)
                                    OnNoteGenerated("Add new file " + pathFinal);
                                else OnNoteGenerated("Update existing file " + pathFinal);
                                #endregion
                                
                            }
                            else if (Directory.Exists(pathTransfer)) //Is Folder - create directory
                            {
                                string pathRelative = pathTransfer.Replace(_pathDownloadFolder, "").Trim('\\').Trim('/');
                                string pathFinal = Path.Combine(_pathApplicationFolder, pathRelative);

                                #region CREATE DIRECTORY
                                if (!Directory.Exists(pathFinal))
                                {
                                    Directory.CreateDirectory(pathFinal);
                                    OnNoteGenerated("Create directory " + pathFinal);
                                }
                                #endregion
                            }
                        }
                    }
                }
                catch (Exception ex)
                {
                    OnErrorGenerated("ReplaceFiles", ex);
                    isError = true;
                }

            }

            return isError;

        }

        private void ClearDownloadFolder()
        {
            if (Directory.Exists(_pathDownloadFolder))
                Directory.Delete(_pathDownloadFolder, true);
            OnNoteGenerated("removing download folder");
        }
#if (!PC)
        internal void LaunchApplication()
        {
            if (_applicationExe.Length > 0)
            {
                if (!IsExeRunning(_applicationExe))
                {
                    OnStatusChange("Starting application");
                    string pathApp = Path.Combine(_pathApplicationFolder, _applicationExe);
                    try
                    {
                        bool isRunning = false;
                        do
                        {
                            RunExe(pathApp);

                            isRunning = IsExeRunning(_applicationExe);
                            if (isRunning)
                                OnNoteGenerated(_applicationExe + "is now running");
                            else OnErrorGenerated("LaunchApplication", new Exception("unable to restart " + _applicationExe));
                            
                            if (!isRunning)
                                Thread.Sleep(1000); //Pause before trying again
                        } while (!isRunning);

                    }
                    catch (Exception ex)
                    {
                        OnErrorGenerated("LaunchApplication", ex);
                    }
                }
                else OnNoteGenerated("Already running " + _applicationExe);
            }

            else OnErrorGenerated("LaunchApplication", new Exception("no application specified"));

        }
#endif
        #endregion

        #region HELPER FUNCTIONS
        private string RemoveZip(string filename)
        {
            return filename.Replace(".ZIP","").Replace(".zip","");
        }
        private bool IsZip(string filename)
        {
            string ext = Path.GetExtension(filename);
            return (ext.ToLower().Equals(".zip"));
        }
        #endregion

        #region SAVE/GET STATE
        private void SaveLastUpdated()
        {
            SaveTextToFile(Path.Combine(_pathApplicationFolder, "updater_lastupdated.txt"), _dtLastUpdated.ToString());
        }
        private void SaveLastDownload()
        {
            SaveTextToFile(Path.Combine(_pathDownloadFolder, "updater_lastdownload.txt"), _dtLastDownload.ToString());
        }
        private void DeleteLastDownload()
        {
            File.Delete(Path.Combine(_pathDownloadFolder, "updater_lastdownload.txt"));
        }
        private bool SaveTextToFile(string filepath, string content)
        {
            bool success = false;

            StreamWriter sr = null;
            try
            {
                sr = File.CreateText(filepath);
                sr.WriteLine(content);
                success = true;
            }
            catch (Exception ex)
            {
                OnErrorGenerated("SaveTextToFile saving to " + filepath,ex);
            }
            finally
            {
                if (sr != null) sr.Close();
            }
            return success;

        }
        private void RetrieveLastUpdated()
        {
            string filepath = Path.Combine(_pathApplicationFolder, "updater_lastupdated.txt");
            if (File.Exists(filepath))
            {
                string dateAsString = ReadTextFromFile(filepath);
                _dtLastUpdated = Convert.ToDateTime(dateAsString);
                OnNoteGenerated("Last updated on " + _dtLastUpdated.ToString());
            }
            else
            {
                _dtLastUpdated = DateTime.Now.AddYears(-10);
                OnNoteGenerated("No record of previous update");
            }
        }
        private void RetrieveLastDownload()
        {
            string filepath = Path.Combine(_pathDownloadFolder, "updater_lastdownload.txt");
            if (File.Exists(filepath))
            {
                string dateAsString = ReadTextFromFile(filepath);
                _dtLastDownload = Convert.ToDateTime(dateAsString);
                OnNoteGenerated("Last download at " + _dtLastDownload.ToString());
            }
            else
            {
                _dtLastDownload = DateTime.Now.AddYears(-10);
                OnNoteGenerated("No record of previous download");
            }
        }
        private string ReadTextFromFile(string filepath)
        {
            string readtext = "";

            if (File.Exists(filepath))
            {
                try
                {
                    using (StreamReader sr = new StreamReader(filepath))
                    {
                        readtext = sr.ReadToEnd();
                    }
                }
                catch (Exception ex)
                {
                    OnErrorGenerated("ReadTextFromFile reading from " + filepath, ex);
                }
            }
            else OnErrorGenerated("ReadTextFromFile no file at " + filepath,null);

            return readtext;

        }
        #endregion

        #region BUILD FILE LIST
        /// <summary>
        /// Recursively searches subidrectories within SearchPath to assemble a list of full paths of subfolders and files
        /// </summary>
        /// <param name="SearchPath">Full path of directory to search</param>
        /// <param name="RecursionLevel">Start at 0</param>
        /// <param name="FileList">ArrayList that will contain list of filepaths</param>
        private void BuildFileList(string SearchPath, int RecursionLevel, ArrayList FileList, bool includeDirectories, bool includeFiles, string fileSearchPattern)
        {

            DirectoryInfo ThisLevel = new DirectoryInfo(SearchPath);
            DirectoryInfo[] ChildLevel = ThisLevel.GetDirectories();
            if (RecursionLevel != 1)
            {
                foreach (DirectoryInfo Child in ChildLevel)
                {
                    if (includeDirectories) FileList.Add(Child.FullName);
                    BuildFileList(Child.FullName, RecursionLevel - 1, FileList, includeDirectories, includeFiles, fileSearchPattern);                    
                }
            }
            if (includeFiles)
            {
                FileInfo[] ChildFiles = ThisLevel.GetFiles(fileSearchPattern);
                foreach (FileInfo ChildFile in ChildFiles)
                {
                    FileList.Add(ChildFile.FullName);
                }
            }
        }


        public ArrayList BuildFileArray(string searchPath, bool includeDirectories, bool includeFiles, string fileSearchPattern)
        {
            ArrayList filelist = new ArrayList();
            if (fileSearchPattern.Length == 0) fileSearchPattern = "*";
            BuildFileList(searchPath, 0, filelist, includeDirectories, includeFiles, fileSearchPattern);
            return filelist;
        }
        #endregion

        #region COMPRESSION
        /// <summary>
        /// Use ICSharpCode.SharpZipLib to unzip a zipped file; Log error
        /// </summary>
        /// <param name="pathZipFile">Fullpath of zipped file</param>
        /// <param name="pathDestination">Path where unzipped file should be saved</param>
        /// <returns>Filename of unzipped file</returns>
        private string Decompress(string pathZipFile, string pathDestination)
        {
            string filename = "";
            try
            {
                filename = DecompressFile(pathZipFile, pathDestination);
            }
            catch (Exception ex)
            {
                OnErrorGenerated("UpdaterAction decompressing", ex);
                //critical error
                throw ex;
            }
            return filename;
        }
        /// <summary>
        /// Use ICSharpCode.SharpZipLib to unzip a zipped file
        /// </summary>
        /// <param name="pathZipFile">Fullpath of zipped file</param>
        /// <param name="pathDestination">Path where unzipped file should be saved</param>
        /// <returns>Filename of unzipped file</returns>
        public static string DecompressFile(string pathZipFile, string pathDestination)
        {
            string lastfile = "";
            ZipInputStream ins = null;
            FileStream fs = null;
            string pathDestinationFile = "";

            try
            {
                ins = new ZipInputStream(File.OpenRead(pathZipFile));


                ZipEntry ze = ins.GetNextEntry();
                while (ze != null)
                {
                    if (ze.IsDirectory)
                    {
                        Directory.CreateDirectory(pathDestination + "\\" + ze.Name);
                    }
                    else if (ze.IsFile)
                    {
                        pathDestinationFile = Path.Combine(pathDestination, Path.GetDirectoryName(ze.Name));
                        if (!Directory.Exists(pathDestinationFile))
                        {
                            Directory.CreateDirectory(pathDestinationFile);
                        }

                        pathDestinationFile = Path.Combine(pathDestination, ze.Name);
                        fs = File.Create(pathDestinationFile);

                        byte[] writeData = new byte[ze.Size];
                        int iteration = 0;
                        while (true)
                        {
                            int size = 2048;
                            size = ins.Read(writeData, (int)Math.Min(ze.Size, (iteration * 2048)), (int)Math.Min(ze.Size - (int)Math.Min(ze.Size, (iteration * 2048)), 2048));
                            if (size > 0)
                            {
                                fs.Write(writeData, (int)Math.Min(ze.Size, (iteration * 2048)), size);
                            }
                            else
                            {
                                break;
                            }
                            iteration++;
                        }
                        fs.Close();
                    }
                    lastfile = ze.Name;
                    ze = ins.GetNextEntry();
                }
            }
            catch (Exception ex)
            {
                //critical error
                throw ex;
            }
            finally
            {
                if (fs != null) fs.Close();
                fs = null;
                if (ins != null) ins.Close();
                ins = null;
            }


            return lastfile;

        }

        #endregion


        #region EVENT HANDLERS
        private void OnStatusChange(string status)
        {
            _status = status;
            if (StatusChanged != null) StatusChanged(status);
        }
        private void OnErrorGenerated(string logevent, Exception ex)
        {
            if (LogErrorGenerated != null) LogErrorGenerated(logevent, ex);
        }
        private void OnNoteGenerated(string logevent)
        {
            if (LogItemGenerated != null) LogItemGenerated(logevent);
        }
        #endregion

#if (!PC)
        #region PROCESS MANAGEMENT
        /// <summary>
        /// Runs file specified by path if file exists; device specific code supports Smartphone, PocketPC, and PC implementations
        /// </summary>
        /// <param name="path">Fullpath of executable</param>
        private void RunExe(string path)
        {
            
            if (File.Exists(path))
            {
                try
                {
                    Process.StartProcess(path,"");
                }
                catch (Exception ex)
                {
                    OnErrorGenerated("RunExe " + path, ex);
                }
            }
            else OnErrorGenerated("RunExe file does not exist at " + path,null);

        }


        /// <summary>
        /// Checks whether an executable is running by checking the process list; implementations for Smartphone, PocketPC, and PC
        /// </summary>
        /// <param name="executableFilename">Filename of the executable</param>
        /// <returns>true if executable name is found in the process list</returns>
        private bool IsExeRunning(string executableFilename)
        {
            bool isRunning = false;
            try
            {
                isRunning = Process.IsExeRunning(executableFilename);
            }
            catch (Exception ex)
            {
                OnErrorGenerated("IsExeRunning " + executableFilename, ex);
            }
            return isRunning;
        }

        /// <summary>
        /// Locates executable in current running process list; if found, tries to kill
        /// </summary>
        /// <param name="executableFilename">Filename of the executable to kill</param>
        private void KillIfRunning(string executableFilename)
        {
            try
            {
                Process pExecutable = Process.GetProcess(executableFilename);
                if (pExecutable != null)
                {
                    pExecutable.Kill();
                    OnNoteGenerated("Closing " + executableFilename);
                }
            }
            catch (Exception ex)
            {
                OnErrorGenerated("KillIfRunning " + executableFilename, ex);
            }
        }
        #endregion



        #region Event Sender
        //
        [DllImport("coredll.dll")]
        public static extern IntPtr SendMessage(IntPtr hndl, uint Msg, IntPtr wParam, IntPtr lParam);
        [DllImport("coredll.dll")]
        public static extern IntPtr FindWindow(string lpClassName, string lpWindowName);
        [DllImport("coredll.dll")]
        public static extern IntPtr PostMessage(IntPtr hndl, uint Msg, IntPtr wParam, IntPtr lParam);

#region commented
        //----------------------------
        //[DllImport("coredll.dll")]
        //[return: MarshalAs(UnmanagedType.Bool)]
        //static extern bool EnumChildWindows(IntPtr hwndParent, EnumWindowProc lpEnumFunc, IntPtr lParam);


        //public delegate bool Win32Callback(IntPtr hwnd, IntPtr lParam);
        //[DllImport("coredll.dll")]
        //[return: MarshalAs(UnmanagedType.Bool)]
        //public static extern bool EnumChildWindows(IntPtr parentHandle, Win32Callback callback, IntPtr lParam);


        ///// <summary>
        ///// Returns a list of child windows
        ///// </summary>
        ///// <param name="parent">Parent of the windows to return</param>
        ///// <returns>List of child windows</returns>
        //public static List<IntPtr> GetChildWindows(IntPtr parent)
        //{
        //    List<IntPtr> result = new List<IntPtr>();
        //    GCHandle listHandle = GCHandle.Alloc(result);
            
        //    try
        //    {
        //        //Callback
        //        EnumWindowProc childProc = new EnumWindowProc(EnumWindow);
        //        EnumChildWindows(parent, childProc,GCHandleType) ;
        //    }
        //    finally
        //    {
        //        if (listHandle.IsAllocated)
        //            listHandle.Free();
        //    }
        //    return result;
        //}



        ///// <summary>
        ///// Callback method to be used when enumerating windows.
        ///// </summary>
        ///// <param name="handle">Handle of the next window</param>
        ///// <param name="pointer">Pointer to a GCHandle that holds a reference to the list to fill</param>
        ///// <returns>True to continue the enumeration, false to bail</returns>
        //public static bool EnumWindow(IntPtr handle, IntPtr pointer)
        //{
        //    GCHandle gch = GCHandle.FromIntPtr(pointer);
        //    List<IntPtr> list = gch.Target as List<IntPtr>;
        //    if (list == null)
        //    {
        //        throw new InvalidCastException("GCHandle Target could not be cast as List<IntPtr>");
        //    }
        //    list.Add(handle);
        //    //  You can modify this to check to see if you want to cancel the operation, then return a null here
        //    return true;
        //}


        ///// <summary>
        ///// Delegate for the EnumChildWindows method
        ///// </summary>
        ///// <param name="hWnd">Window handle</param>
        ///// <param name="parameter">Caller-defined variable; we use it for a pointer to our list</param>
        ///// <returns>True to continue enumerating, false to bail.</returns>
        //public delegate bool EnumWindowProc(IntPtr hWnd, IntPtr parameter);


        //------------------------------

#endregion


        private const int TERMINATE_MESSAGE = 0xA123;
        private const int MIN_WND_MESSAGE = 0xC00D;


        private void TerminateApp(string executableFilename)
        {
 
             string MsgWindowName = "WocketsMessageWindow";

           try
            {
               IntPtr hndl=new IntPtr();
              
               hndl = FindWindow(null, MsgWindowName);

               if ( hndl != null)
                {
                    
                   if( ((long)SendMessage(hndl, TERMINATE_MESSAGE, IntPtr.Zero, IntPtr.Zero)) == 0)
                   {  OnNoteGenerated("Sending Clossing Msg to " + MsgWindowName); }
                   else
                   {
                        int code = Marshal.GetLastWin32Error();
                        string serr = Marshal.GetLastWin32Error().ToString();
                        throw new SystemException(String.Format("Failed Send Message to " + MsgWindowName+ " , SHCMBM_OVERRIDEKEY Error string" + serr + " Error code:{0} ", code));
                   }

                }

#region Commented
               ////get this running process
               //System.Diagnostics.Process proc = System.Diagnostics.Process.GetCurrentProcess();
               ////get all other (possible) running instances
               //Process[] processes = Process.GetProcesses();  //GetProcessesByName(proc.ProcessName);

               //if (processes.Length > 1)
               //{
               //    //iterate through all running target applications
               //    foreach (Process p in processes)
               //    {
               //        if ( p.ProcessName.CompareTo(executableFilename) == 0)
               //        {
               //            //now send the RF_TESTMESSAGE to the running instance
               //            SendMessage(p.Handle, TERMINATE_MESSAGE, IntPtr.Zero, IntPtr.Zero);
               //        }

               //        if (p.Handle == hndl)
               //        {
               //            //now send the RF_TESTMESSAGE to the running instance
               //            SendMessage(p.Handle, TERMINATE_MESSAGE, IntPtr.Zero, IntPtr.Zero);
               //        }
               //    }
               //}
               //else
               //{
               //    //MessageBox.Show("No other running applications found.");
               //    //OnErrorGenerated("Error Sending Close Msg ");
                //}
#endregion


            }
            catch (Exception ex)
            {
                OnErrorGenerated("Error Sending Close Msg to " + MsgWindowName, ex);   
            }
           

        }


        #endregion



#endif
        #endregion
    }
}
