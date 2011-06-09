using System;
using System.Text;

using System.Xml;
using System.Net;
using System.Collections;
using System.IO;


namespace AppUpdater
{
    public class Downloader
    {

        public class Resource
        {
            public string Name = "";
            public string Url = "";
            public bool IsFolder = false;
            public DateTime LastModified;
        }



        //**************************************************************
        // GetDirectoryContents()	
        // - Uses HTTP/DAV to get a list of directories
        //**************************************************************
        
        /// <summary>
        /// Uses HTTP/DAV to get a list of directories and files at the specified url
        /// </summary>
        /// <param name="url">URL address on server that supports HTTP/DAV</param>
        /// <returns>List of file/directories at the URL address structured as Resource objects</returns>
        public static ArrayList GetDirectoryContents(string url)
        {
            //Retrieve the File
            HttpWebRequest Request = (HttpWebRequest)HttpWebRequest.Create(url);
            Request.Headers.Add("Translate: f");
            //Request.Credentials = CredentialCache.DefaultCredentials;

            string requestString = "<?xml version=\"1.0\" encoding=\"utf-8\" ?>" +
                "<a:propfind xmlns:a=\"DAV:\">" +
                "<a:prop>" +
                "<a:displayname/>" +
                "<a:iscollection/>" +
                "<a:getlastmodified/>" +
                "</a:prop>" +
                "</a:propfind>";

            Request.Method = "PROPFIND";
            Request.Headers.Add("Depth: infinity");

            Request.ContentLength = requestString.Length;
            Request.ContentType = "text/xml";

            Stream requestStream = Request.GetRequestStream();
            requestStream.Write(Encoding.ASCII.GetBytes(requestString), 0, Encoding.ASCII.GetBytes(requestString).Length);
            requestStream.Close();

            HttpWebResponse Response;
            StreamReader respStream;
            try
            {
                Response = (HttpWebResponse)Request.GetResponse();
                respStream = new StreamReader(Response.GetResponseStream());
            }
            catch (WebException e)
            {
                throw e;
            }

            StringBuilder SB = new StringBuilder();

            char[] respChar = new char[1024];
            int BytesRead = 0;

            BytesRead = respStream.Read(respChar, 0, 1024);

            while (BytesRead > 0)
            {
                SB.Append(respChar, 0, BytesRead);
                BytesRead = respStream.Read(respChar, 0, 1024);
            }
            respStream.Close();

            XmlDocument XmlDoc = new XmlDocument();
            XmlDoc.LoadXml(SB.ToString());

            XmlNodeList NameList = XmlDoc.GetElementsByTagName("a:displayname");
            XmlNodeList isFolderList = XmlDoc.GetElementsByTagName("a:iscollection");
            XmlNodeList LastModList = XmlDoc.GetElementsByTagName("a:getlastmodified");
            XmlNodeList HrefList = XmlDoc.GetElementsByTagName("a:href");

            ArrayList ResourceList = new ArrayList();
            Resource tempResource;

            for (int i = 0; i < NameList.Count; i++)
            {
                //This check is needed because the PROPFIND request returns the contents of the folder
                //as well as the folder itself.  Exclude the folder.
                //ADDED: exclude Thumbs.db
                if ((HrefList[i].InnerText.ToLower().TrimEnd(new char[] { '/' }) != url.ToLower().TrimEnd(new char[] { '/' }))
                    && (NameList[i].InnerText.ToLower() != "thumbs.db"))
                {
                    tempResource = new Resource();
                    tempResource.Name = NameList[i].InnerText;
                    tempResource.IsFolder = Convert.ToBoolean(Convert.ToInt32(isFolderList[i].InnerText));
                    tempResource.Url = HrefList[i].InnerText;
                    tempResource.LastModified = Convert.ToDateTime(LastModList[i].InnerText);
                    ResourceList.Add(tempResource);
                }
            }

            return ResourceList;
        }


        /// <summary>
        /// Retrieves the file at specified URL address via HttpWebRequest; saves file to filePath
        /// if file already exists at filePath, it is deleted and replaced
        /// </summary>
        /// <param name="url">URL address of file to download</param>
        /// <param name="filePath">Path where file should be saved, including filename</param>
        public static void CopyToDisk(string url, string filePath)
        {
            HttpWebResponse Response = null;
            Stream responseStream = null;

            //Retrieve the File
            HttpWebRequest Request = null; 

            try
            {
                Request = (HttpWebRequest)HttpWebRequest.Create(url);

                Response = (HttpWebResponse)Request.GetResponse();

                responseStream = Response.GetResponseStream();


                byte[] buffer = new byte[4096];
                int length;

                //Copy to a temp file first so that if anything goes wrong with the network
                //while downloading the file, we don't actually update the real on file disk
                //This essentially gives us transaction like semantics.
                string tempPath = Path.GetTempFileName();

                FileStream AFile = File.Open(tempPath, FileMode.Create, FileAccess.ReadWrite);

                length = responseStream.Read(buffer, 0, 4096);
                while (length > 0)
                {
                    AFile.Write(buffer, 0, length);
                    length = responseStream.Read(buffer, 0, 4096);
                }
                AFile.Close();

                if (File.Exists(filePath))
                    File.Delete(filePath);
                File.Move(tempPath, filePath);


            }
            catch (WebException e)
            {
                throw e;
            }
            finally
            {
                if (responseStream != null) responseStream.Close();
                responseStream = null;
                if (Response != null) Response.Close();
                Response = null;
                if (Request != null) Request = null;
            }

        }
    }
}
