package edu.mit.media.wockets.DataLogger.DefinedExceptions;

import org.xml.sax.SAXException;


public class SAXFatalException extends SAXException{
	
	private String message;

	public SAXFatalException(String message)
	{
		this.message = message;
	}
	
	public String toString()
	{
		return message;
	}

}
