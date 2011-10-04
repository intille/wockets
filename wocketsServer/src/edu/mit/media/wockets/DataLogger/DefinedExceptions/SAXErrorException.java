package edu.mit.media.wockets.DataLogger.DefinedExceptions;

import org.xml.sax.SAXException;

public class SAXErrorException extends SAXException{

	private String message;

	public SAXErrorException(String message)
	{
		this.message = message;
	}
	
	public String toString()
	{
		return message;
	}

	
}
