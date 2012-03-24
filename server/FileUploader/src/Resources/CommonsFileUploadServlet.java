/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package Resources;

/**
 *
 * @author Nishant Nagwani
 */
import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Iterator;
import java.util.List;
import java.util.zip.GZIPInputStream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import javax.servlet.ServletConfig;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.apache.commons.fileupload.FileItem;
import org.apache.commons.fileupload.FileUploadException;
import org.apache.commons.fileupload.disk.DiskFileItemFactory;
import org.apache.commons.fileupload.servlet.ServletFileUpload;

/*
 * @author Nishant Nagwani
 * 
 * This is the servlet to handle raw file upload requests.
 * The response parameters are <imei> <md5Checksum> <File> 
 * 
 * The filename could be of 2 types:
 * 
 * 1. json.{unixtimestamp}.gzip
 * 2. file.{directory structure}.gzip
 * 
 * If the file is of 1st type, the contents are unzipped and forwarded to
 * Android log service. The response from that service is forwarded to the client.
 * Otherwise, the contents of the files are verified. If the contents are ok, the
 * file is stored on the server in user's file directory.
 * 
 * One exception to the input could be that the directory structure in 2nd file
 * type is not valid. In that case the files are stored in the user's temp directory
 * untill the researcher manually checks whether to keep it.
 * 
 * 
 */

public class CommonsFileUploadServlet extends HttpServlet {

	/**
	 * 
	 */
	private static final long serialVersionUID = 8272111840692668609L;
	// temp directory to store files before verification
	private static final String TMP_DIR_PATH = "/data/WocketsTemp/";
	private File tmpDir;
	// destination directory where files are to be stored after verification
	private static String DESTINATION_DIR_PATH = "/data/Wockets/";
	private File destinationDir;
	//private static String LOGS_DIR_PATH = "/data/WocketsLogs/";
	//private File logsDir;
	//private static PrintWriter pw = null;
	
	
	@Override
	public void init(ServletConfig config) throws ServletException {
		super.init(config);
		tmpDir = new File(TMP_DIR_PATH);
		if (!tmpDir.isDirectory()) {
			throw new ServletException(TMP_DIR_PATH + " is not a directory");
		}

	}

	@Override
	protected void doPost(HttpServletRequest request,
			HttpServletResponse response) throws ServletException, IOException {
		String phoneID = null, md5Checksum = null, subjectID = null;
		PrintWriter out = response.getWriter();
		response.setContentType("text/plain");
		
		DiskFileItemFactory fileItemFactory = new DiskFileItemFactory();
		/*
		 * Set the size threshold, above which content will be stored on disk.
		 */
		fileItemFactory.setSizeThreshold(1 * 1024 * 1024); // 1 MB
		/*
		 * Set the temporary directory to store the uploaded files of size above
		 * threshold.
		 */
		fileItemFactory.setRepository(tmpDir);

		ServletFileUpload uploadHandler = new ServletFileUpload(fileItemFactory);
		try {
			/*
			 * Parse the request
			 */
			List items = uploadHandler.parseRequest(request);
			Iterator itr = items.iterator();
			while (itr.hasNext()) {
				FileItem item = (FileItem) itr.next();
				/*
				 * Handle Form Fields.
				 */
				if (item.isFormField()) {
					String currentItem = item.getFieldName();
					if (currentItem.equalsIgnoreCase("phoneID")) {
						phoneID = item.getString();
					//	pw.write("Recieved ");
						subjectID = ServiceClient.getSubjectID(phoneID);
						if(subjectID.equalsIgnoreCase("NoRecordFound")){
							out.println("No record found for given phoneID : "+phoneID);
							break;
						}
						if(subjectID.equalsIgnoreCase("")){
							out.println("Database Server is temporalily down.");
							break;
						}
						
					} else if (currentItem.equalsIgnoreCase("md5Checksum")) {
						md5Checksum = item.getString();
					} else {
						out.println("Invalid parameter");
						break;
					}
					
				} else {
					
					// Handle uploaded files
					
					String tmpDirectoryString = tmpDir + "/" + "temp" + subjectID;  
					File tempDirectory = new File(tmpDirectoryString);
					if (!tempDirectory.isDirectory())
						tempDirectory.mkdirs();

					File tempFile = new File(tempDirectory, item.getName());
					item.write(tempFile);
					
					String filename = item.getName();

					
					
					// Handle json files
					if (isJsonFile(filename)) {
						
						out.println("Json file received. Request Forwarding to AndroidLogs service.");
						
						String unzippedFile = null;
						// unzip the file
						if(checkIsZIP(filename)){
							unzippedFile = getUnzippedFile(filename, tmpDirectoryString, true);
							if(unzippedFile == null)
								out.println("Problem unzipping file.");
						}else{
							unzippedFile = getFileAsString(filename, tmpDirectoryString);
							if(unzippedFile == null)
								out.println("Problem reading file.");
							
						}
						if(unzippedFile != null){
							int responseFromTest = ServiceClient.callAndroidLogsService(unzippedFile);
							if(responseFromTest == 200){
								out.println("Json file successfully submitted.");
								tempFile.delete();
							}else if(responseFromTest == 400){
								out.println("Android Logs service rejected as Bad Input.");
							}else{
								out.println("Android Logs service is down.");
							}
							out.println(ServiceClient.responseBody);
							
							
						}
					} 
					
					// handle this way if the incoming file is not a json file
					else {
						
						//out.println("Field Name = " + item.getFieldName()
						//		+ ", File Name = " + item.getName()
							//	+ ", Content type = " + item.getContentType()
							//	+ ", File Size = " + item.getSize());

						out.println("Raw data file recieved.");
						
						int verified = verifyFile(filename, md5Checksum, tmpDirectoryString);
						
						String parsedFileName = parseFileName(filename);
						
						// if the filename was valid, delete the file from temp
						// directory. Store it in the desitination directory. On the other
						// hand, if the file name was invalid, leave the file in temp
						// directory for future review.
						if (parsedFileName != null) {
							tempFile.delete();
							
							String[] dirStructure = parsedFileName.split("\\\\");
							String dirPath = dirStructure[0], newFileName = dirStructure[1];
							
							// path to the sub directory for user
							String userDirPath = DESTINATION_DIR_PATH + "/" + subjectID + "/" + dirPath;

							
							if (verified == 0) {
								
								destinationDir = new File(userDirPath);
								if (!destinationDir.isDirectory()) {
									destinationDir.mkdirs();
								}
								/*
								 * Write file to the ultimate location.
								 */
								File file = new File(destinationDir,
										newFileName);
								item.write(file);
								
								out.println("File written to destination directory.");

							} else {
								out.println("File cannot be verified. Please send again.");
							}
						} else {
							out.println("Invalid file name. Needs to be verified by server administrator.");
						}
					}
				}
		}
			out.close();
		}catch (FileUploadException ex) {
			log("Error encountered while parsing the request", ex);
			ex.printStackTrace();
		} catch (Exception ex) {
			log("Error encountered while uploading file", ex);
			ex.printStackTrace();
		}

	}
	
	
	private boolean checkIsZIP(String filename){
		String[] fileNameParts = filename.split("\\.");
		if(fileNameParts[fileNameParts.length - 1].equalsIgnoreCase("zip"))
			return true;
		
		return false;
	}
	
	
	private String getFileAsString(String inFileName, String tmpDirPath){
		StringBuilder sb = new StringBuilder();
		String FilePath = tmpDirPath + "/" + inFileName;
		
		try{
			  // Open the file that is the first 
			  // command line parameter
			  FileInputStream fstream = new FileInputStream(FilePath);
			  // Get the object of DataInputStream
			  DataInputStream in = new DataInputStream(fstream);
			  BufferedReader br = new BufferedReader(new InputStreamReader(in));
			  String strLine;
			  //Read File Line By Line
			  while ((strLine = br.readLine()) != null)   {
			  // Print the content on the console
			  sb.append(strLine);
			  sb.append("\n");
			  }
			  //Close the input stream
			  in.close();
			    }catch (Exception e){//Catch exception if any
			  System.err.println("Error: " + e.getMessage());
			  }
		
		
		return sb.toString().trim();
	}

	// this method takes in a filename and parses the file name.
			// Gets the directory structure from the middle part of file name
			// if the file name fails the specifications, null is returned.
		// this method takes in a filename and parses the file name.
			// Gets the directory structure from the middle part of file name
			// if the file name fails the specifications, null is returned.
			private String parseFileName(String fileName) {
				// file.UniversityTest-S2-Session1__2009-06-25__15__15.3.2009-06-25-15-00-00-015.gzip
				// "Dir1__Dir2__file.baf.gz"
				StringBuilder path = new StringBuilder();
				try {
					if(fileName.contains("__")){
					
						String[] fileNameParts = fileName.split("__");
						//String protocol = fileNameParts[0].substring(5);
						int i = 0, fileDepth = fileNameParts.length;
						while(i < fileDepth - 1){
							path.append(fileNameParts[i]);
							path.append("/");
							i++;
						}
						path.append("\\");
						path.append(fileNameParts[fileDepth -1]);
						
					}else{
						path.append("\\");
						path.append(fileName);
						
					}
					return path.toString();
					
				} catch (Exception ex) {
					//log("Error encountered while parsing filename, needs to be verified by server administrator.",
						//	ex);
					ex.printStackTrace();
					return null;
				}
			//	return path;
			}
			
			// This method checks if the input filename is json file.
			// If yes, returns true. Otherwise return false.
			private boolean isJsonFile(String filename) {
				String[] fileNameParts = filename.split("\\.");
				if (fileNameParts[1].equalsIgnoreCase("json"))
					return true;
				return false;
			}

	// this file calculates the md5 for the input file and compares it with
	// given checksum. returns 0 if file is verified. Otherwise returns 1 or -1.
	private int verifyFile(String filename, String checksum, String tempDirPath) {
		String output = "";
		try {
			MessageDigest digest = MessageDigest.getInstance("MD5");
			File f = new File(tempDirPath + "/" + filename);
			InputStream is = new FileInputStream(f);
			byte[] buffer = new byte[8192];
			int read = 0;
			try {
				while ((read = is.read(buffer)) > 0) {
					digest.update(buffer, 0, read);
				}
				byte[] md5sum = digest.digest();
				BigInteger bigInt = new BigInteger(1, md5sum);
				output = bigInt.toString(16);

			} catch (IOException e) {
				throw new RuntimeException("Unable to process file for MD5", e);
			} finally {
				try {
					is.close();
				} catch (IOException e) {
					throw new RuntimeException(
							"Unable to close input stream for MD5 calculation",
							e);
				}
			}
		} catch (Exception ex) {
			ex.printStackTrace();
		}
		return output.compareToIgnoreCase(checksum);
	}
	
	
	// This method returns the unzipped contents of the input gzip file from temp directory.
	// If an exception is thrown, null is returned.
	public static String getUnzippedFile(String inFileName, String tmpDirPath, boolean isJson) {
		String zipFilePath = tmpDirPath + "/" + inFileName;
		
		
		try {
			FileInputStream fis = new FileInputStream(zipFilePath);
		    ZipInputStream zis = new ZipInputStream(fis);
		    InputStreamReader isReader = new InputStreamReader(zis);
		    BufferedReader reader = new BufferedReader(isReader);
			if(!isJson){
				//TO DO
				// do application logic for raw file uploads
			}
		    
		    ZipEntry entry;

		    while ((entry = zis.getNextEntry()) != null) {
		      //System.out.println("Unzipping: " + entry.getName());

		      StringBuilder sb = new StringBuilder();
				String line;
				while((line = reader.readLine()) != null){	
					sb.append(line);
				}
		      if(isJson)
		    	  return sb.toString();
		    }
		    reader.close();
		    isReader.close();
		    zis.close();
		    fis.close();
		  }catch(Exception ex){
			  ex.printStackTrace();
		  }
		return null;
	}
	
	

    
}
