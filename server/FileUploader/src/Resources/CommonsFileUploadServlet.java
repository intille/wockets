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
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.util.Iterator;
import java.util.List;
import java.util.zip.GZIPInputStream;

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
		String imei = null, md5Checksum = null;
		PrintWriter out = response.getWriter();
		response.setContentType("text/plain");
		out.println("<h1>Servlet File Upload Example using Commons File Upload</h1>");
		out.println();

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
					if (currentItem.equalsIgnoreCase("imei")) {
						imei = item.getString();
					} else if (currentItem.equalsIgnoreCase("md5Checksum")) {
						md5Checksum = item.getString();
					} else {
						out.print("Invalid parameter");
						break;
					}
					
				} else {
					
					// Handle uploaded files
					
					String tmpDirectoryString = tmpDir + "/" + "temp" + imei;  
					File tempDirectory = new File(tmpDirectoryString);
					if (!tempDirectory.isDirectory())
						tempDirectory.mkdirs();

					File tempFile = new File(tempDirectory, item.getName());
					item.write(tempFile);
					
					String filename = item.getName();

					out.println("Field Name = " + item.getFieldName()
							+ ", File Name = " + item.getName()
							+ ", Content type = " + item.getContentType()
							+ ", File Size = " + item.getSize());

					
					// Handle json files
					if (isJsonFile(filename)) {
						
						out.println("Json file recieved. Request Forwarded to AndroidLogs service.");
						
						// unzip the file
						String unzippedFile = getUnzippedFile(filename, tmpDirectoryString);
						if(unzippedFile != null){
							int responseFromTest = ServiceClient.callAndroidLogsService(unzippedFile);
							if(responseFromTest == 200){
								out.println("json file successfully submitted.");
							}else{
								out.println("AndroidLogs service is down");
							}
							out.println(ServiceClient.responseBody);
							tempFile.delete();
							
						}else{
							out.println("problem unzipping file.");
						}
					} 
					
					// handle this way if the incoming file is not a json file
					else {
						int verified = verifyFile(filename, md5Checksum, tmpDirectoryString);
						
						String parsedFileName = parseFileName(filename);
						
						// if the filename was valid, delete the file from temp
						// directory. Store it in the desitination directory. On the other
						// hand, if the file name was invalid, leave the file in temp
						// directory for future review.
						if (parsedFileName != null) {
							tempFile.delete();
							
							// path to the sub directory for user
							String userDirPath = DESTINATION_DIR_PATH + "/" + imei + "/" + parsedFileName;

							
							if (verified == 0) {
								
								destinationDir = new File(userDirPath);
								if (!destinationDir.isDirectory()) {
									destinationDir.mkdirs();
								}
								/*
								 * Write file to the ultimate location.
								 */
								File file = new File(destinationDir,
										filename);
								item.write(file);

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

	// This method checks if the input filename is json file.
	// If yes, returns true. Otherwise return false.
	private boolean isJsonFile(String filename) {
		String[] fileNameParts = filename.split("\\.");
		if (fileNameParts[0].equalsIgnoreCase("json"))
			return true;
		return false;
	}

	// this method takes in a filename and parses the file name.
	// Gets the directory structure from the middle part of file name
	// if the file name fails the specifications, null is returned.
	private String parseFileName(String fileName) {
		// file.UniversityTest-S2-Session1__2009-06-25__15__15.3.2009-06-25-15-00-00-015.gzip
		try {
			String[] fileNameParts = fileName.split("__");
			String protocol = fileNameParts[0].substring(5);

			return (protocol + "/" + fileNameParts[1] + "/" + fileNameParts[2]);
		} catch (Exception ex) {
			log("Error encountered while parsing filename, needs to be verified by server administrator.",
					ex);
			ex.printStackTrace();
			return null;
		}
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
	public String getUnzippedFile(String inFileName, String tmpDirPath) {
		
		try {
			
			String gzipFilePath = tmpDirPath + "/" + inFileName; 
			GZIPInputStream gzipInputStream = null;
			gzipInputStream = new GZIPInputStream(new FileInputStream(gzipFilePath));
			InputStreamReader isReader = new InputStreamReader(gzipInputStream);
		    BufferedReader reader = new BufferedReader(isReader);
			
			StringBuilder sb = new StringBuilder();
			String line;
			while((line = reader.readLine()) != null){	
				sb.append(line);
			}
			
			reader.close();
			isReader.close();
			gzipInputStream.close();
			
			return sb.toString();
		}

		catch (IOException e) {
			System.out.println("Exception has been thrown" + e);
		}
		return null;
	}
	
	

    
}
