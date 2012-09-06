package bafFormat;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.UnsupportedEncodingException;
import java.math.BigInteger;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.UnknownHostException;
import java.security.MessageDigest;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import org.apache.http.HttpEntity;
import org.apache.http.HttpResponse;
import org.apache.http.HttpVersion;
import org.apache.http.client.ClientProtocolException;
import org.apache.http.client.HttpClient;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.entity.mime.MultipartEntity;
import org.apache.http.entity.mime.content.FileBody;
import org.apache.http.entity.mime.content.StringBody;
import org.apache.http.impl.client.DefaultHttpClient;
import org.apache.http.params.CoreProtocolPNames;
import org.apache.http.util.EntityUtils;


public class SummaryDataFileHandler {
	
	private static final String SERVER_ADDR = "http://wockets.ccs.neu.edu:8080/";
	private static final String URL_FILE_UPLOAD_SERVLET = SERVER_ADDR + "FileUploader/Commonsfileuploadservlet";
	private static final int HTTP_RESPONSE_SERVER_UP = 200; 
	private String subjectID = "12349876";
	
	
	public boolean zipRawData(Date dataTime){
		SimpleDateFormat day = new SimpleDateFormat("yyyy-MM-dd");
		File dataDir = new File("C:/test/"+day.format(dataTime)+"/"+ dataTime.getHours() + "/");
		if(dataDir.isDirectory()){
			File[] dataFiles = dataDir.listFiles(new FilenameFilter() {
				
				@Override
				public boolean accept(File dir, String filename) {
					return filename.endsWith(".json");//||(filename.endsWith(".csv")));
				}
			});
			if(dataFiles != null && dataFiles.length > 0){
				try {
					String externalPath = "C:/test/.wockets/summary/"+day.format(dataTime);
					File externalDir = new File(externalPath);
					if(!externalDir.isDirectory())
						if(!externalDir.mkdirs())
							System.out.println("Error: can not make directory for output zip folder.");
					SimpleDateFormat serverDir = new SimpleDateFormat("yyyy__MM__dd__");
					String targetFileName = "Wockets__json__"+serverDir.format(dataTime)+subjectID+".zip";
					File targetFile = new File(externalPath+"/"+targetFileName);
					if(!targetFile.exists())
						if(!targetFile.createNewFile()){
							System.out.println("Error: can not create zip file for Suumary data in the memory.");
							return false;
						}
					if(!zipFiles(dataFiles,targetFile)){
						System.out.println("Error: can not zip files.");
						return false;
					}
					else
						return true;
				} catch (IOException e) {
					// TODO Auto-generated catch block
					System.out.println("Error: can not create zip file.");
				} 			
			}
			else{
				System.out.println("Error: can not find encoded raw data file in internal memory.");
				return false;
			}
		}
		else{
			System.out.println("Error: can not find encoded raw data folder in internal memory.");
			return false;
		}
		return false;
	}
	
	public boolean transmitSummaryData(){
		boolean isTransmitted = false;
		String externalPath = "C:/test/.wockets/summary/";
		
		File dataFolder = new File(externalPath);
		if(!dataFolder.isDirectory()){
			System.out.println("Error in accessing to the directory.");
			return isTransmitted;
		}
		ArrayList<File> dataFiles = getAllZipFilesInFolder(dataFolder);
		for (File file : dataFiles) {
			System.out.println("start to transmit file:  "+file.getAbsolutePath());
			isTransmitted = transmitFile(file.getAbsolutePath(), subjectID, true);
		}
		return isTransmitted;
	}
	private ArrayList<File> getAllZipFilesInFolder(File folder){
		ArrayList<File> fileList = new ArrayList<File>();
		File[] subFiles = folder.listFiles();
		for (File file : subFiles) {
			if(file.isFile()){
				if(file.getName().endsWith(".zip"))
					fileList.add(file);
			}
			else if(file.isDirectory())
				fileList.addAll(getAllZipFilesInFolder(file));
		}
		return fileList;
	}
	private boolean zipFiles(File[] sourceFiles, File targetFile){
		BufferedInputStream origin = null;
		ZipOutputStream out = null;
		boolean isSuccess = true; 
		FileInputStream fi = null;
		FileOutputStream dest = null;

		try  {
			dest = new FileOutputStream(targetFile);
			out = new ZipOutputStream(new BufferedOutputStream(dest));
			byte data[] = new byte[1024];
			for (File sourceFile : sourceFiles) {
				String filePath = sourceFile.getAbsolutePath();
				if (filePath.endsWith(".zip")){
					System.out.println("Warning: File already compressed: " + sourceFile.getName());
				}
				else{
					fi = new FileInputStream(sourceFile);
					origin = new BufferedInputStream(fi, 1024);
					ZipEntry entry = new ZipEntry(filePath.substring(filePath.lastIndexOf("/") + 1));
					out.putNextEntry(entry);
					int count;
					while ((count = origin.read(data, 0, 1024)) != -1) {
							out.write(data, 0, count);
					}

				}
			}
		} catch(Exception e) {
			e.printStackTrace();
			System.out.println("Error when zipping: " + e.toString());
			isSuccess = false; 
		} finally{
			try {
				if(origin != null)
					origin.close();
				if(out != null){
					out.flush();
					out.close();
				}
			} catch (IOException e) {
				System.out.println("Problem closing file when zipping: " + e.toString());
				e.printStackTrace();
				isSuccess = false; 
			}
		}

		if (targetFile.length() == 0)
		{
			System.out.println("Zip created a file of size 0: " + targetFile);
			isSuccess = false; 
		}
		
		/*if (isSuccess)
		{
			for (File sourceFile : sourceFiles) {
				if (!sourceFile.delete())
				{
					System.out.println("Error deleting file after zipping: " + sourceFile.getName());
					isSuccess = false; 
				}
			}
		}*/	
		
		return isSuccess; 
	}
	public boolean transmitFile(String aFileName, String anID, boolean isRemove)
	{	
		File f = new File(aFileName);
		String errMsg = ""; 
		boolean isSuccess = true;
		// get the md5 checksum of file
		if (!isNetworkAvailable())
		{
			errMsg = "Error in transmitFile. Network not available."; 
			System.out.println(errMsg);
			isSuccess = false; 
		}
		HttpPost httppost = null;
		MultipartEntity entity = null;
		HttpClient httpclient = null;

		if (isSuccess)
		{
			String md5Checksum = getMD5forfile(aFileName);

			httpclient = new DefaultHttpClient();
			httpclient.getParams().setParameter("http.connection.timeout", 15000 ); // TODO change from 3000
			httpclient.getParams().setParameter("http.socket.timeout", 15000 );
			httpclient.getParams().setParameter(CoreProtocolPNames.PROTOCOL_VERSION, HttpVersion.HTTP_1_1);
						
			httppost = new HttpPost(URL_FILE_UPLOAD_SERVLET);
 
			entity = new MultipartEntity();
			// adding parameters for request
			try {
	//			entity.addPart("protocol", new StringBody("protocol"));
				entity.addPart(/*"phoneID"*/"subjectID", new StringBody(anID));
	//			entity.addPart("sessionNumber", new StringBody(sessionNumber));
				entity.addPart("md5Checksum", new StringBody(md5Checksum));
				entity.addPart(f.getName(), new FileBody(f));
			} catch (UnsupportedEncodingException e) {
				errMsg = "Error in uploadFile. Unsupported encoding. " + e.toString();
				System.out.println(errMsg);
				e.printStackTrace();
				isSuccess = false; 
			}		
		}

		if (isSuccess)
		{
			httppost.setEntity(entity);
			HttpResponse httpresponse;
			InputStream is = null;
			BufferedReader rd = null;
			try {
				httpresponse = httpclient.execute(httppost);
				String statusLine = httpresponse.getStatusLine().toString();
				int statusCode = httpresponse.getStatusLine().getStatusCode();
				if (statusCode != HTTP_RESPONSE_SERVER_UP)
				{
					errMsg = "Error in uploadFile communicating with server. Did not get a 200 response. " + statusLine; 
					System.out.println(errMsg);
					isSuccess = false; 
				}
				else	
				{
					HttpEntity resEntity = httpresponse.getEntity();
					String responseBody = EntityUtils.toString(resEntity);
					
					if (responseBody.contains("Json file successfully submitted"))
					{
						errMsg = "Json file uploaded and processed.";
						isSuccess = true;
					} else if (responseBody.contains("File written to destination directory"))
					{
						errMsg = "File uploaded to server without error.";
						isSuccess = true; 
					} else // Response body must contain an error
					{
						System.out.println("HTTPRESPONSE BODY (ERROR): " + responseBody);
						errMsg = "Error message from server after upload attempt: " + responseBody; 
						isSuccess = false;
					}
				}
			} catch (ClientProtocolException e) {
				errMsg = "Error in uploadFile. ClientProtocolException in httpclient.execute." + e.toString();
				System.out.println(errMsg);
				e.printStackTrace();
				isSuccess = false; 
			} catch (IOException e) {
				errMsg = "Error in uploadFile. IOException in httpclient.execute." + e.toString();
				System.out.println(errMsg);
				e.printStackTrace();
				isSuccess = false; 
			} finally {
				if (rd != null)
					try {
						rd.close();
					} catch (IOException e) {
						errMsg = "Error closing file";
						System.out.println(errMsg);
						e.printStackTrace();
					} 
				if (is != null)
					try {
						is.close();
					} catch (IOException e) {
						errMsg = "Error closing file";
						System.out.println(errMsg);
						e.printStackTrace();
					} 
			}
		}
		
		if (isRemove && isSuccess)
		{
			if (!deleteFile(new File(aFileName)))
				errMsg = "Error: could not remove file on phone after upload: " + aFileName;
			System.out.println(errMsg);
		}
		return isSuccess; 
	}
	// this method returns the checksum for the input file
	// It calculates the MD5 hash using the native java algorithm for MD5
	private static String getMD5forfile(String filename) {
		String md5 = "";
		try {
			MessageDigest digest = MessageDigest.getInstance("MD5");
			File f = new File(filename);
			InputStream is = new FileInputStream(f);
			byte[] buffer = new byte[8192];
			int read = 0;
			try {
				while ((read = is.read(buffer)) > 0) {
					digest.update(buffer, 0, read);
				}
				byte[] md5sum = digest.digest();
				BigInteger bigInt = new BigInteger(1, md5sum);
				md5 = bigInt.toString(16);
				System.out.println("MD5: " + md5);

			} catch (IOException e) {
				System.out.println("Unable to process file for MD5: " + filename);
				throw new RuntimeException("Unable to process file for MD5", e);
			} finally {
				try {
					is.close();
				} catch (IOException e) {
					System.out.println("Unable to close input stream for MD5 calculation: " + filename);					
					throw new RuntimeException("Unable to close input stream for MD5 calculation", e);
				}
			}
		} catch (Exception ex) {
			System.out.println("Error in getMD5forfile: " + filename + " " + ex.toString());								
			ex.printStackTrace();
		}

		return md5;
	}
		
	//checks for connection to the internet through dummy request
    public static boolean isNetworkAvailable()
    {
            try {
                    //make a URL to a known source
                    URL url = new URL("http://www.google.com");

                    //open a connection to that source
                    HttpURLConnection urlConnect = (HttpURLConnection)url.openConnection();

                    //trying to retrieve data from the source. If there
                    //is no connection, this line will fail
                    Object objData = urlConnect.getContent();

            } catch (UnknownHostException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                    return false;
            }
            catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                    return false;
            }
            return true;
    }
	
	
	public static boolean deleteFile(File orig)
	{ 
		boolean isDeleted = orig.delete(); 
		if (!isDeleted)
		{
			System.out.println("Error: could not delete file in deleteFile: " + orig.getAbsolutePath());
			return false; 
		}
		return true; 
	}

	private static String findTheEarliestTimeStampInBafFileName(File[] dataFiles){
		SimpleDateFormat detailedTime = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-SSS");
		Date earliestTime = null;
		Date tempTime = null;
		String fileName = "";
		try {
			for (int i = 0; i < dataFiles.length; i++) {
				fileName = dataFiles[i].getName();
				fileName = fileName.substring(0, fileName.lastIndexOf("."));
				fileName = fileName.substring(fileName.lastIndexOf(".")+1);
				tempTime = detailedTime.parse(fileName);
				if(earliestTime == null || earliestTime.after(tempTime))
					earliestTime = tempTime;
			}
			return detailedTime.format(earliestTime);
		} catch (ParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
}
