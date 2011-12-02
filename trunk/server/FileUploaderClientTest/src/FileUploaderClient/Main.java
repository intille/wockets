package FileUploaderClient;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.http.HttpEntity;
import org.apache.http.HttpResponse;
import org.apache.http.client.HttpClient;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.entity.mime.MultipartEntity;
import org.apache.http.entity.mime.content.FileBody;
import org.apache.http.entity.mime.content.StringBody;
import org.apache.http.impl.client.DefaultHttpClient;

import java.io.File;
import java.io.IOException;

/**
 *
 * @author Nishant Nagwani
 * This is a Client class for CommonsFileUploadServlet
 * Purpose of this class is to call server with raw data files
 *
 */

public class Main 
{

	// @param args the command line argument
	public static void main(String[] args) {
		// TODO code application logic here
		
		//******Hardcoded argument for testing*********
		String[] args1 = {"study","1234","00","/data/Wockets/University-S23-Session99/SensorFolder/2009-06-25/15/[SensorType].[IDof3AxisAccel].2009-06-25-15-0-0-15.baf"};
		if (args.length > 4) 
		{
			System.out.println("Usage: Client <protocol> <subjectID> <sessionNumber>                     <list of files seperated with comma (,)");
			System.exit(-1);
		}
		String protocol = args1[0];
		String subjectID = args1[1];
		String sessionNumber = args1[2];

		// get the list of files
		String[] files = args1[3].split(",\\s");
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

			HttpClient httpclient = new DefaultHttpClient();

			HttpPost httppost = new HttpPost("http://wockets.ccs.neu.edu:8080/FileUploader/Commonsfileuploadservlet");

			MultipartEntity entity = new MultipartEntity();
			entity.addPart("protocol", new StringBody(protocol));
			entity.addPart("subjectID", new StringBody(subjectID));
			entity.addPart("sessionNumber", new StringBody(sessionNumber));
			entity.addPart("md5Checksum", new StringBody(md5Checksum));
			entity.addPart(f.getName(), new FileBody(f));

			httppost.setEntity(entity);
			HttpResponse httpresponse = httpclient.execute(httppost);
			System.out.println(httpresponse.getStatusLine());
			HttpEntity resEntity = httpresponse.getEntity();
            InputStream is = resEntity.getContent();
            BufferedReader rd = new BufferedReader(new InputStreamReader(is));
            String return_result = rd.readLine();
            if (return_result != null) {
                Pattern regex = Pattern.compile("(?<=<body><h1>)(.+?)(?=<)");
                Matcher m = regex.matcher(return_result);
                if (m.find()) {
                    System.out.println(m.group());
                }
            }
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
