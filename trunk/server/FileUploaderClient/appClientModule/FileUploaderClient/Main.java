package FileUploaderClient;

import java.io.FileInputStream;
import java.io.InputStream;
import java.math.BigInteger;
import java.security.MessageDigest;
import org.apache.commons.httpclient.HttpClient;
import org.apache.commons.httpclient.methods.PostMethod;
import org.apache.commons.httpclient.methods.multipart.MultipartRequestEntity;
import org.apache.commons.httpclient.methods.multipart.Part;
import org.apache.commons.httpclient.methods.multipart.StringPart;


import org.apache.commons.httpclient.methods.multipart.FilePart;
import java.io.File;
import java.io.IOException;

/**
 *
 * @author Nishant Nagwani
 * This is a Client class for CommonsFileUploadServlet
 * Purpose of this class is to call server with raw data files
 *
 */

public class FileUploaderClient 
{

	// @param args the command line argument
	public static void main(String[] args) {
		// TODO code application logic here
		if (args.length > 4) 
		{
			System.out.println("Usage: Client <protocol> <subjectID> <sessionNumber>" +)                    "<list of files seperated with comma (,)");
			System.exit(-1);
		}
		String protocol = args[0];
		String subjectID = args[1];
		String sessionNumber = args[2];

		// get the list of files
		String[] files = args[3].split(",\\s");
		try 
		{
			callService(files, protocol, subjectID, sessionNumber);
		} 
		catch (IOException ex) 
		{
			ex.printStackTrace();
		}
	}

	// This method calls the service with protocol, subjectid, session number and filename for each file
	// in the list of files
	public static void callService(String[] filename, String protocol, String subjectID, String sessionNumber) throws IOException 
	{
		for (int i = 0; i < filename.length; i++) 
		{

			// get the md5 checksum of file
			String md5Checksum = getMD5forfile(filename[i]);
			File f = new File(filename[i]);
			HttpClient client = new HttpClient();
			String URL = "http://wockets.ccs.neu.edu:8080/FileUploader/Commonsfileuploadservlet";
			PostMethod filePost = new PostMethod(URL);

			// adding parameters for request
			Part[] parts = 
			{
					new StringPart("protocol", protocol),
					new StringPart("subjectID", subjectID),
					new StringPart("sessionNumber", sessionNumber),
					new StringPart("md5Checksum", md5Checksum),
					new FilePart(f.getName(), f)
			};

			filePost.setRequestEntity(new MultipartRequestEntity(parts, filePost.getParams()));
			int status = client.executeMethod(filePost);

			System.out.println("status: " + status);
			String response = filePost.getResponseBodyAsString();
			System.out.println(response);
			filePost.releaseConnection();
		}
	}

	// This method returns the checksum for the input file
	// It calculates the MD5 hash using the native java algorithm for MD5
	private static String getMD5forfile(String filename) 
	{
		String md5 = "";
		try 
		{
			MessageDigest digest = MessageDigest.getInstance("MD5");
			File f = new File(filename);
			InputStream is = new FileInputStream(f);
			byte[] buffer = new byte[8192];
			int read = 0;
			try 
			{
				while ((read = is.read(buffer)) > 0) 
				{
					digest.update(buffer, 0, read);
				}
				byte[] md5sum = digest.digest();
				BigInteger bigInt = new BigInteger(1, md5sum);
				md5 = bigInt.toString(16);
				System.out.println("MD5: " + md5);
			} 
			catch (IOException e) 
			{
				throw new RuntimeException("Unable to process file for MD5", e);
			} 
			finally 
			{
				try 
				{
					is.close();
				} 
				catch (IOException e) 
				{
					throw new RuntimeException("Unable to close input stream for MD5 calculation", e);
				}
			}
		} 
		catch (Exception ex) 
		{
			ex.printStackTrace();
		}
		return md5;
	}
}
