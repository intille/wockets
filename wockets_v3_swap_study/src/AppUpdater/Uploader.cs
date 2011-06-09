using System;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.Net;
using System.IO;
using AppUpdater.Logging;

namespace AppUpdater
{
    class Uploader
    {

        // Most code from VB Rocks on http://www.codeproject.com/KB/vb/WebDAV_Upload.aspx
        internal static void uploadFile(String filePath, String url)
        {
            String fileToUpload = filePath.Trim();
            FileInfo f = new FileInfo(fileToUpload);
            long fileLength = f.Length;
            
            url = url.TrimEnd('/') + "/" + Path.GetFileName(fileToUpload);

            HttpWebRequest request = (HttpWebRequest)System.Net.HttpWebRequest.Create(url);
            //request.Credentials = new NetworkCredential(this.txtUserName.Text.Trim(), this.txtPassword.Text.Trim());
            
            //Let the server know we want to "put" a file on it
            request.Method = @"PUT";
            
            //Set the length of the content (file) we are sending
            request.ContentLength = fileLength;

            //*** This is required for our WebDav server ***
            request.SendChunked = true;
            request.Headers.Add("Translate: f");
            request.AllowWriteStreamBuffering = true;

            Stream s = null;
            try {
                //Send the request to the server, and get the
                // server's (file) Stream in return.
                   
                s = request.GetRequestStream();
            }
            catch (Exception ex) {
                Logger.LogError("Uploader", ex, "An error occurred while attempting to connect to the remote server", false);
            }

            // Start writing file data to stream
            FileStream fs = new FileStream(fileToUpload, FileMode.Open, FileAccess.Read);

            //Create the buffer for storing the bytes read from the file
            int byteTransferRate = 1024;
            byte[] bytes = new byte[byteTransferRate];
            int bytesRead = 0;
            long totalBytesRead = 0;

            //Configure the ProgressBar
            //pb.Minimum = 0;
            //pb.Maximum = (int)fileLength / byteTransferRate;
            //pb.Value = 0;

            //Read from the file and write it to the server's stream.
            try{
                do {
                    //Read from the file
                    bytesRead = fs.Read(bytes, 0, bytes.Length);
                   
                    if (bytesRead > 0) {
                       
                        totalBytesRead += bytesRead;
                       
                        //Write to stream
                        s.Write(bytes, 0, bytesRead);
                       
                        //Update progress
                        //pb.Value = (int)totalBytesRead / byteTransferRate;
                           
                        //if (pb.Value % 500 == 0) Application.DoEvents();
                       
                    }
                }while (bytesRead > 0);
            }catch(Exception ex){
                Logger.LogError("Uploader", ex, "An error occurred while attempting to copy the file stream", false);
            }finally{
                //Close the server stream
                s.Close();
                s.Dispose();
                s = null;
               
                //Close the file
                fs.Close();
                fs.Dispose();
                fs = null;
            }

            // upload file stream
            HttpWebResponse response = null;
            try {
                response = (HttpWebResponse)request.GetResponse();
                
                //Get the StatusCode from the server's Response
                HttpStatusCode code = response.StatusCode;
                
                //Close the response
                response.Close();
                response = null;

                if (totalBytesRead == fileLength && code == HttpStatusCode.Created) {
                    Logger.LogInfo("Uploader","The file has uploaded successfully!", true);                }
                else {
                    Logger.LogError("Uploader", "The file did not upload successfully.", true);
                }
            }
            catch (Exception ex) {
                // no directory.
                Logger.LogError("Uploader", ex, "An error occurred while attempting to upload the file.", false);
            }
        }
    }

}
