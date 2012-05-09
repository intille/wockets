package decoding;

import java.io.File;

public class FileChecker 
{
	
	public String fileCheck(String directoryName)
	{
		File folder = new File(directoryName);
	    File[] listOfFiles = folder.listFiles();
	    
	    //Check if the directory exists
	    
	    if(!folder.exists())
	    	return null;
	    if(listOfFiles.length<1)
	    	return null;
	    
	    //Check if file already exists for the hour
	    if (!(listOfFiles[0].isFile()))
	    	return null;
	    else
	    	return listOfFiles[0].getName();
	    	  
		
		
		
		
		
		
//		File dir = new File("directoryName");
//		String fileName = null;
//		String[] children = dir.list();
//		if (children == null) 
//		{
//		    // Either dir does not exist or is not a directory
////			return null;
//			
//		} 
//		else 
//		{
//		   
//		        // Get filename of file or directory
//		        fileName = children[0];
//		}
//		
//		
//		System.out.println(fileName);
////		return fileName;
//		
	}

}
