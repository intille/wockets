using System;
using System.Text;

using System.Xml; //Variables stored in xml file
using System.IO; //Path
using System.Collections;//ArrayList

using MobiRnD_RDT.Logging;

namespace MobiRnD_RDT.RemoteUpdater
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
    }
    /// <summary>
    /// A class to access and update the settings for the Updater
    /// </summary>
    class Settings
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

            _alApps = new ArrayList();

            XmlDocument xmldoc = new XmlDocument();

            
                string[] files = new string[0];

                //look for XML setting files within subdirectory of current directory
                string dirSettings = Path.Combine(ExeDirectory, XML_FOLDER);
                if (!Directory.Exists(dirSettings))
                    Directory.CreateDirectory(dirSettings);
                else files = Directory.GetFiles(dirSettings, "*.xml");

                if (files.Length > 0)
                {
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
                                
                                if (dNode["urls"] != null)
                                {
                                    app.URLs = new string[dNode["urls"].ChildNodes.Count];
                                    for (int u = 0; u < dNode["urls"].ChildNodes.Count; i++)
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

                                if ((app.ApplicationFolder.Length > 0) && (app.URLs.Length > 0)) isSuccess = true; //at least one application to update
                            }

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
