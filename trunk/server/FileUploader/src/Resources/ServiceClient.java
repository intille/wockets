package Resources;

import java.io.IOException;

import org.apache.commons.httpclient.HttpClient;
import org.apache.commons.httpclient.HttpException;
import org.apache.commons.httpclient.HttpStatus;
import org.apache.commons.httpclient.NameValuePair;
import org.apache.commons.httpclient.URI;
import org.apache.commons.httpclient.methods.GetMethod;
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
	        
	        
	        filePost.setRequestHeader("Content-type", "application/json; charset=UTF-8");
	        filePost.setRequestEntity(new StringRequestEntity(jsonString));
	        
	        int status = client.executeMethod(filePost);

	        System.out.println("status: " + status);
	        responseBody = filePost.getResponseBodyAsString();
	        
	        filePost.releaseConnection();
	        
	        return status;
	    }
	
	public static String getSubjectID(String phoneID) {

		String subjectID = "";
	    HttpClient client = new HttpClient();
	    client.getParams().setParameter("http.useragent", "Test Client");
	    client.getParams().setParameter("http.connection.timeout",new Integer(5000));

	    GetMethod method  = new GetMethod();
	    
	    try {

	      method.setURI(new URI("http://wockets.ccs.neu.edu:8080/Wockets/android/getParticipantId.html", true));
	      
	      NameValuePair imei = new NameValuePair();
	      imei.setName("imei");
	      imei.setValue(phoneID);
	      
	      NameValuePair[] params = new NameValuePair[] {imei};
	      
	      method.setQueryString(params);
	      
	      
	      int returnCode = client.executeMethod(method);

	      
	      if(returnCode == HttpStatus.SC_OK) {
	        subjectID = method.getResponseBodyAsString();
	      }else if(method.getResponseBodyAsString().contains("No record found for imei:"+phoneID))
	    	  subjectID = "NoRecordFound";
	      
	    } catch (HttpException he) {
	      System.err.println(he);
	    } catch (IOException ie) {
	      System.err.println(ie);
	    } finally {
	      method.releaseConnection();
	    }
	    return subjectID;

	  }
}
