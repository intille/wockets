using System;
using System.Collections.Specialized;
using System.Globalization;
using System.IO;
using System.Net;
using System.Text;
using Microsoft.Win32;
using System.Collections;
using System.Collections.Generic;

namespace Wockets.Utils.Http
{
    public class FileUploader
    {
        public static string _Uri = "";
        public static string _Path = "";
        public static string _HourlyPath = "";
        public static string _HistoryPath = "";
        public static Dictionary<string, DateTime> _NotUploaded = new Dictionary<string, DateTime>();
        public static Dictionary<string, DateTime> _Success = new Dictionary<string, DateTime>();
        public static Dictionary<string, DateTime> _Failure = new Dictionary<string, DateTime>();
     
        static FileUploader()
        {
            //Determine the default path to upload from the local file system
            string firstCard = "";
            System.IO.DirectoryInfo di = new System.IO.DirectoryInfo("\\");
            System.IO.FileSystemInfo[] fsi = di.GetFileSystemInfos();

            //iterate through them
            for (int x = 0; x < fsi.Length; x++)
            {
                //check to see if this is a temporary storage card (e.g. SD card)
                if ((fsi[x].Attributes & System.IO.FileAttributes.Temporary) == System.IO.FileAttributes.Temporary)
                {
                    //if so, return the path
                    firstCard = fsi[x].FullName;
                    break;
                }
            }
            _Path = firstCard + "\\Wockets\\";
            _HistoryPath = _Path + "kernellog\\uploadhistory\\";
            
            try
            {
                if (!Directory.Exists(_HistoryPath))
                    Directory.CreateDirectory(_HistoryPath);
            }
            catch
            {
            }
            try
            {
                DateTime now = DateTime.Now;
                _HourlyPath = _Path + "kernellog\\" + now.ToString("yyyy-MM-dd") + "\\" + now.Hour+"\\";
                if (!Directory.Exists(_HourlyPath))
                    Directory.CreateDirectory(_HourlyPath);
            }
            catch
            {
            }
        }

        public static void Load()
        {
            try
            {
                if (File.Exists(_HistoryPath + "files.notuploaded.wockets"))
                {
                    TextReader tr = new StreamReader(_HistoryPath + "files.notuploaded.wockets");
                    string line = "";
                    while ((line = tr.ReadLine()) != null)
                    {
                        string[] tokens = line.Split(new char[] { ',' });
                        _NotUploaded.Add(tokens[0], DateTime.ParseExact(tokens[1], "yyyy-MM-dd HH:mm tt", null));
                    }
                    tr.Close();
                }


            }
            catch (Exception e)
            {
            }


            try
            {
                if (File.Exists(_HistoryPath + "files.uploaded.wockets"))
                {
                    TextReader tr = new StreamReader(_HistoryPath + "files.uploaded.wockets");
                    string line = "";
                    while ((line = tr.ReadLine()) != null)
                    {
                        string[] tokens = line.Split(new char[] { ',' });
                        _Success.Add(tokens[0], DateTime.ParseExact(tokens[1], "yyyy-MM-dd HH:mm tt", null));
                    }
                    tr.Close();
                }

            }
            catch (Exception e)
            {
            }
        }



        public static void Save()
        {
            //Save not uploaded files
            try
            {
                TextWriter tw = new StreamWriter(_HistoryPath + "files.notuploaded.wockets");
                foreach (string filename in _Failure.Keys)
                    tw.WriteLine(filename + "," + File.GetCreationTime(filename).ToString("yyyy-MM-dd HH:mm tt"));
                tw.Close();
            }
            catch (Exception e)
            {
            }


            //Save uploaded files
            try
            {
                TextWriter tw = new StreamWriter(_HistoryPath + "files.uploaded.wockets");
                foreach (string filename in _Success.Keys)
                {
                    DateTime creationTime=File.GetCreationTime(filename);
                    if (DateTime.Now.Subtract(creationTime).Days<=2)
                        tw.WriteLine(filename + "," + creationTime.ToString("yyyy-MM-dd HH:mm tt"));
                }
                tw.Close();
            }
            catch (Exception e)
            {
            }

            //Write files that were successfully uploaded
            try
            {
                TextWriter tw = new StreamWriter(_HourlyPath + "success.upload.wockets-" + DateTime.Now.ToString("yyyy-MM-dd-HH-mm-tt"));
                foreach (string filename in _Success.Keys)
                    tw.WriteLine(filename + "," + File.GetCreationTime(filename).ToString("yyyy-MM-dd HH:mm tt"));
                tw.Close();
            }
            catch (Exception e)
            {
            }


            //Write files that were unsuccessfully uploaded
            try
            {
                TextWriter tw = new StreamWriter(_HourlyPath + "failed.upload.wockets-" + DateTime.Now.ToString("yyyy-MM-dd-HH-mm-tt"));
                foreach (string filename in _Failure.Keys)
                    tw.WriteLine(filename + "," + File.GetCreationTime(filename).ToString("yyyy-MM-dd HH:mm tt"));
                tw.Close();
            }
            catch (Exception e)
            {
            }
        }

        public static Dictionary<string, DateTime> Scan(DateTime from, DateTime until)
        {
            //load successful and not uploaded files
            Load();

            Dictionary<string, DateTime> _scanned= Scan(_Path,from,until);
            foreach (string filename in _scanned.Keys)
            {
                if ( (!_NotUploaded.ContainsKey(filename)) && (!_Success.ContainsKey(filename)))
                    _NotUploaded.Add(filename, File.GetCreationTime(filename));
            }
         
            //Write the files to be uploaded
            try
            {
                TextWriter tw = new StreamWriter(_HourlyPath+ "files.toupload.wockets");
                foreach (string filename in _NotUploaded.Keys)
                    tw.WriteLine(filename + "," + File.GetCreationTime(filename).ToString("yyyy-MM-dd HH:mm tt"));
                tw.Close();
            }
            catch (Exception e)
            {
            }
            return _NotUploaded;
        }
        public static Dictionary<string, DateTime> Scan(string path,DateTime from, DateTime until)
        {
            string[] scannedfiles = Directory.GetFiles(path);
            Dictionary<string, DateTime> files = new Dictionary<string, DateTime>();

            //Directory was scanned before
            if ((path+"\\")==_HistoryPath)
               return files;

            for (int i = 0; (i < scannedfiles.Length); i++)
            {
                DateTime creationTime = File.GetCreationTime(scannedfiles[i]);
                FileInfo f = new FileInfo(scannedfiles[i]);

                if ( (f.Length>0) && (((creationTime.Day != DateTime.Now.Day) || (creationTime.Hour != DateTime.Now.Hour) || (creationTime.Month != DateTime.Now.Month) ||
                    (creationTime.Year != DateTime.Now.Year)) && (DateTime.Compare(creationTime,from)>=0) && 
                    (DateTime.Now.Subtract(creationTime).Hours>=2)))
                    files.Add(scannedfiles[i], creationTime);
            }
            if (Directory.Exists(path))
            {
                string[] scanneddirectories = Directory.GetDirectories(path);                
                for (int j = 0; (j < scanneddirectories.Length); j++)
                {
                    DateTime dCreationTime=Directory.GetCreationTime(scanneddirectories[j]);
                    if ((DateTime.Compare(dCreationTime, from) >= 0) && (DateTime.Compare(until,dCreationTime) >= 0))
                    {
                        Dictionary<string, DateTime> scanneddirectory = Scan(scanneddirectories[j],from,until);
                        foreach (string filename in scanneddirectory.Keys)
                        {
                            DateTime creationTime = File.GetCreationTime(filename);
                            FileInfo f = new FileInfo(filename);
                            if ((f.Length>0) && ((((creationTime.Day != DateTime.Now.Day) || (creationTime.Hour != DateTime.Now.Hour) || (creationTime.Month != DateTime.Now.Month) ||
                                (creationTime.Year != DateTime.Now.Year)))  && (DateTime.Now.Subtract(creationTime).Hours>=2)))
                                files.Add(filename, creationTime);
                        }
                        //if a top level directory... store it in the scanned list
                        //if ((path == _Path) && (!_DirectoryScanned.ContainsKey(scanneddirectories[j])))
                          //  _DirectoryScanned.Add(scanneddirectories[j], Directory.GetCreationTime(scanneddirectories[j]));                        
                    }
                }
            }
            return files;
        }
        public static Dictionary<string, DateTime> Scan()
        {
            _NotUploaded = Scan(_Path);
            return _NotUploaded;
        }
        public static Dictionary<string, DateTime> Scan(string path)
        {
            string[] scannedfiles = Directory.GetFiles(path);           
            Dictionary<string,DateTime> files = new Dictionary<string,DateTime>();
            for (int i = 0; (i < scannedfiles.Length); i++)
            {
                DateTime creationTime = File.GetCreationTime(scannedfiles[i]);               
                if ((DateTime.Now.Subtract(creationTime).Hours>=2) && (((creationTime.Day != DateTime.Now.Day) || (creationTime.Hour != DateTime.Now.Hour) || (creationTime.Month != DateTime.Now.Month) ||
                    (creationTime.Year != DateTime.Now.Year))))
                    files.Add(scannedfiles[i], creationTime);
            }

            if (Directory.Exists(path))
            {
                string[] scanneddirectories = Directory.GetDirectories(path);
                for (int j = 0; (j < scanneddirectories.Length); j++)
                {
                    Dictionary<string, DateTime> scanneddirectory = Scan(scanneddirectories[j]);
                    foreach (string filename in scanneddirectory.Keys)
                    {
                        DateTime creationTime = File.GetCreationTime(filename);
                        if  ((DateTime.Now.Subtract(creationTime).Hours>=2) && (((creationTime.Day != DateTime.Now.Day) || (creationTime.Hour != DateTime.Now.Hour) || (creationTime.Month != DateTime.Now.Month) ||
                            (creationTime.Year != DateTime.Now.Year))))
                            files.Add(filename, creationTime);
                    }
                }
            }
            return files;
        }

        /// <summary>
        /// Uploads a stream using a multipart/form-data POST.
        /// </summary>
        /// <param name="requestUri"></param>
        /// <param name="postData">A NameValueCollection containing form fields to post with file data</param>
        /// <param name="fileData">An open, positioned stream containing the file data</param>
        /// <param name="fileName">Optional, a name to assign to the file data.</param>
        /// <param name="fileContentType">Optional. If omitted, registry is queried using <paramref name="fileName"/>. 
        /// If content type is not available from registry, application/octet-stream will be submitted.</param>
        /// <param name="fileFieldName">Optional, a form field name to assign to the uploaded file data. 
        /// If ommited the value 'file' will be submitted.</param>
        /// <param name="cookies">Optional, can pass null. Used to send and retrieve cookies. 
        /// Pass the same instance to subsequent calls to maintain state if required.</param>
        /// <param name="headers">Optional, headers to be added to request.</param>
        /// <returns></returns>
        /// Reference: 
        /// http://tools.ietf.org/html/rfc1867
        /// http://tools.ietf.org/html/rfc2388
        /// http://www.w3.org/TR/html401/interact/forms.html#h-17.13.4.2
        /// 
        public static HttpWebRequest webrequest;
        public static WebResponse Post(Uri requestUri, NameValueCollection postData, Stream fileData, string fileName,
                                           string fileContentType, string fileFieldName, NameValueCollection headers)
        {
            webrequest = (HttpWebRequest)WebRequest.Create(requestUri);


            string ctype;


            fileFieldName = string.IsNullOrEmpty(fileFieldName) ? "file" : fileFieldName;

            if (headers != null)
            {
                // set the headers
                foreach (string key in headers.AllKeys)
                {
                    string[] values = headers.GetValues(key);
                    if (values != null)
                        foreach (string value in values)
                        {
                            webrequest.Headers.Add(key, value);
                        }
                }
            }
            webrequest.Method = "POST";



            string boundary = "----------" + DateTime.Now.Ticks.ToString("x", CultureInfo.InvariantCulture);

            webrequest.ContentType = "multipart/form-data; boundary=" + boundary;

            string sbHeader = "";

            // add form fields, if any
            if (postData != null)
            {
                foreach (string key in postData.AllKeys)
                {
                    string[] values = postData.GetValues(key);
                    if (values != null)
                        foreach (string value in values)
                        {
                            sbHeader += string.Format("--{0}\r\n", boundary);
                            sbHeader += string.Format("Content-Disposition: form-data; name=\"{0}\";\r\n\r\n{1}\r\n", key,
                                                  value);
                        }
                }
            }


            if (fileData != null)
            {
                sbHeader += string.Format("--{0}\r\n", boundary);
                sbHeader += string.Format("Content-Disposition: form-data; name=\"{0}\"; {1}\r\n", fileFieldName,
                                      string.IsNullOrEmpty(fileName)
                                          ?
                                              ""
                                          : string.Format(CultureInfo.InvariantCulture, "filename=\"{0}\";",
                                                          Path.GetFileName(fileName)));

                sbHeader += string.Format("Content-Type: {0}\r\n\r\n", fileContentType);
            }

            byte[] header = Encoding.UTF8.GetBytes(sbHeader.ToString());
            byte[] footer = Encoding.ASCII.GetBytes("\r\n--" + boundary + "--\r\n");
            long contentLength = header.Length + (fileData != null ? fileData.Length : 0) + footer.Length;

            webrequest.ContentLength = contentLength;
            webrequest.Timeout = 30000;
            webrequest.KeepAlive = true;
            //webrequest.ReadWriteTimeout = 90000;
            
            //webrequest.
            using (Stream requestStream = webrequest.GetRequestStream())
            {
                requestStream.Write(header, 0, header.Length);


                if (fileData != null)
                {
                    // write the file data, if any
                    byte[] buffer = new Byte[checked((uint)System.Math.Min(4096, (int)fileData.Length))];
                    int bytesRead;
                    while ((bytesRead = fileData.Read(buffer, 0, buffer.Length)) != 0)
                    {
                        requestStream.Write(buffer, 0, bytesRead);
                    }
                }

                // write footer
                requestStream.Write(footer, 0, footer.Length);
                requestStream.Close();
                return webrequest.GetResponse();               
            }

            webrequest.Abort();            
            return null;
        }

        /// <summary>
        /// Uploads a file using a multipart/form-data POST.
        /// </summary>
        /// <param name="requestUri"></param>
        /// <param name="postData">A NameValueCollection containing form fields to post with file data</param>
        /// <param name="fileName">The physical path of the file to upload</param>
        /// <param name="fileContentType">Optional. If omitted, registry is queried using <paramref name="fileName"/>. 
        /// If content type is not available from registry, application/octet-stream will be submitted.</param>
        /// <param name="fileFieldName">Optional, a form field name to assign to the uploaded file data. 
        /// If ommited the value 'file' will be submitted.</param>
        /// <param name="cookies">Optional, can pass null. Used to send and retrieve cookies. 
        /// Pass the same instance to subsequent calls to maintain state if required.</param>
        /// <param name="headers">Optional, headers to be added to request.</param>
        /// <returns></returns>
        public static WebResponse Post(Uri requestUri, NameValueCollection postData, string fileName,
                                           string fileContentType, string fileFieldName,
                                           NameValueCollection headers)
        {
            using (FileStream fileData = File.Open(fileName, FileMode.Open, FileAccess.Read, FileShare.Read))
            {
                return Post(requestUri, postData, fileData, fileName, fileContentType, fileFieldName,
                                headers);
            }
        }
   
        
    }
}
