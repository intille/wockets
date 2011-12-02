package Resources;

import java.io.IOException;

import org.apache.commons.httpclient.HttpClient;
import org.apache.commons.httpclient.methods.PostMethod;
import org.apache.commons.httpclient.methods.StringRequestEntity;

public class ServiceClient {
	
	private static final String POST_URL = "http://wockets.ccs.neu.edu:8080/Wockets/AndroidDataLog.html";
	public static String responseBody = null;

	 
	// This method calls the Android logs service to HTTP POST the given json string.
	// returns the status code for submission and stores response in the variable each time it is invoked.
	public static int callAndroidLogsService(String jsonString) throws IOException {

	    	
	        HttpClient client = new HttpClient();
	        PostMethod filePost = new PostMethod(POST_URL);
	        
	        
	        filePost.setRequestHeader("Content-type", "application/x-json; charset=UTF-8");
	        filePost.setRequestEntity(new StringRequestEntity(jsonString));
	        
	        int status = client.executeMethod(filePost);

	        System.out.println("status: " + status);
	        responseBody = filePost.getResponseBodyAsString();
	        
	        filePost.releaseConnection();
	        
	        return status;
	    }
}
