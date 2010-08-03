using System;
using System.Text;

using System.Xml; //Variables stored in xml file
using System.IO; //Path
using System.Collections;//ArrayList

namespace AppUpdater
{

    public class AppToUpdate
    {
        /// <summary>
        /// File name of application to close before update and launch after update
        /// Should be an .exe in the ApplicationFolder directory
        /// </summary>
        public string ApplicationExe = "";
        /// <summary>
        /// Full path of directory where application files to be updated are located
        /// </summary>
        public string ApplicationFolder = "";

        /// <summary>
        /// List of URLs from which to download files
        /// </summary>
        public string[] URLs = new string[0];

        public override string ToString()
        {
            return String.Format("Update files in {0} using files downloaded from {1} and restart {2}", ApplicationFolder, String.Join(",", URLs), ApplicationExe);
        }
    }
    /// <summary>
    /// A class to access and update the settings for the Updater
    /// </summary>
    public class Settings
    {
        //expects subfolder with this name within current directory
        const string XML_FOLDER = "settings";


        #region EVENT HANDLERS
        public event LogErrorHandler LogErrorGenerated;

        public Exception LastException = null;
        public string LastErrorLocation = "";
        #endregion


        #region APPS TO UPDATE
        private ArrayList _alApps = new ArrayList();

        /// <summary>
        /// ArrayList of AppToUpdate objects 
        /// representing applications listed in XML files in the settings folder
        /// </summary>
        public ArrayList ApplicationsToUpdate
        {
            get { return _alApps; }
        }
        #endregion



        /// <summary>
        /// Loads xml files from the settings subdirectory of the current directory. 
        /// Populates ApplicationsToUpdate ArrayList with AppToUpdate objects
        /// Sets AppToUpdate object fields according to contents of each xml file. 
        /// </summary>
        /// <returns>bool indicating success of loading at least one xml settings file; xml file exists and contains content</returns>
        public bool Load()
        {
            bool isSuccess = false;

            _alApps = new ArrayList(); //reset list of AppsToUpdate

            #region GET LIST OF SETTINGS FILES
            string[] files = new string[0];
            //look for XML setting files within subdirectory of current directory
            string dirSettings = Path.Combine(ExeDirectory, XML_FOLDER);
            if (!Directory.Exists(dirSettings))
                Directory.CreateDirectory(dirSettings);
            else files = Directory.GetFiles(dirSettings, "*.xml");
            #endregion

            if (files.Length > 0)
            {
                XmlDocument xmldoc = new XmlDocument();

                for (int i = 0; i < files.Length; i++)
                {
                    try
                    {
                        xmldoc.Load(files[i]);
                        if (xmldoc.DocumentElement != null)
                        {
                            XmlNode dNode = xmldoc.DocumentElement;

                            AppToUpdate app = new AppToUpdate();

                            #region REQUIRED FIELDS - application folder path and URLs
                            if (dNode["application_folder"] != null)
                                app.ApplicationFolder = dNode["application_folder"].InnerText;
                            else throw (new Exception(String.Format("settings file {0} is missing 'application_folder' element", files[i])));

                            #region DETERMINE WHETHER APPLICATION FOLDER EXISTS
                            string path = DeviceStatus.LocationOfDirectory(app.ApplicationFolder);
                            if (path.Length > 0) app.ApplicationFolder = path;
                            else throw (new Exception(String.Format("application folder specified in {0} does not exist at path {1} on either device or storage card", files[i], app.ApplicationFolder)));
                            #endregion
                            
                            if ((dNode["urls"] != null) && (dNode["urls"].ChildNodes.Count > 0))
                            {
                                app.URLs = new string[dNode["urls"].ChildNodes.Count];
                                for (int u = 0; u < dNode["urls"].ChildNodes.Count; u++)
                                {
                                    app.URLs[u] = dNode["urls"].ChildNodes[u].InnerText;
                                }
                            }
                            else throw (new Exception(String.Format("settings file {0} is missing 'urls' section", files[i])));
                            #endregion

                            #region OPTIONAL FIELD - application filename
                            if (dNode["application_exe"] != null)
                                app.ApplicationExe = dNode["application_exe"].InnerText;
                            #endregion

                            _alApps.Add(app);

                            isSuccess = true; //at least one application to update
                        }
                        else throw (new Exception("no document element in " + files[i]));

                    }
                    catch (Exception ex)
                    {
                        OnErrorGenerated("Load", ex);
                    }
                }
            }
            else OnErrorGenerated("Load", new Exception("no settings files found"));



            return isSuccess;
        }


        //public void SetVariable(string name, string value)
        //{
        //    XmlDocument xmldoc = new XmlDocument();
        //    try
        //    {
        //        string filepath = Path.Combine(ExeDirectory, _xmlFile);
        //        if (File.Exists(filepath))
        //        {
        //            xmldoc.Load(filepath);
        //            if (xmldoc.DocumentElement[name] == null)
        //            {
        //                XmlElement xChild = xmldoc.CreateElement(name);
        //                xmldoc.DocumentElement.AppendChild(xChild);
        //            }
        //            xmldoc.DocumentElement[name].InnerText = value;

        //            xmldoc.Save(filepath);
        //        }
        //        else Logger.LogError("Settings:SetVariable", "no file at " + filepath);


        //    }
        //    catch (Exception ex)
        //    {
        //        Logger.LogError("Settings:SetVariable", ex.ToString(),name + " " + value);
        //    }


        //}


        private void OnErrorGenerated(string logevent, Exception ex)
        {
            LastException = ex;
            LastErrorLocation = logevent;
            if (LogErrorGenerated != null) LogErrorGenerated("Settings:" + logevent, ex);
        }

        public static string ExeDirectory
        {
            get { return System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetCallingAssembly().GetName().CodeBase); }
        }

    }
}
