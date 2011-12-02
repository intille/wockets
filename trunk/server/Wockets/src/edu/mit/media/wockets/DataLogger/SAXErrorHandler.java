/***
 * Created By Salim Khan
 * Defauld error handler if any error occurred during XML parsing
 */
package edu.mit.media.wockets.DataLogger;

import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import edu.mit.media.wockets.DataLogger.DefinedExceptions.SAXErrorException;
import edu.mit.media.wockets.DataLogger.DefinedExceptions.SAXFatalException;

public class SAXErrorHandler implements ErrorHandler {

	//call when error occurred (usually when .xsd condition not satisfied)
	@Override
	public void error(SAXParseException spe) throws SAXErrorException 
	{
		String message = "Error: " + getParseExceptionInfo(spe);
        throw new SAXErrorException(message);
	}

	//call when fatal error occurred
	@Override
	public void fatalError(SAXParseException spe) throws SAXFatalException
	{
		String message = "Fatal Error: " + getParseExceptionInfo(spe);
        throw new SAXFatalException(message);
	}

	//call when warning occurred
	@Override
	public void warning(SAXParseException spe) 
	{
		System.out.println("Warning: " + getParseExceptionInfo(spe));
	}

	//return Exception information
	private String getParseExceptionInfo(SAXParseException spe) 
	{
		String systemId = spe.getSystemId();
        if (systemId == null) 
        	systemId = "null";

        String info = "URI=" + systemId +
               		  " Line=" + spe.getLineNumber() +
               		  ": " + spe.getMessage();
           return info;
     }

}
