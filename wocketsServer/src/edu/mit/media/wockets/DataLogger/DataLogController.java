package edu.mit.media.wockets.DataLogger;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.rowset.spi.XmlReader;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.transform.Source;
import javax.xml.transform.sax.SAXSource;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;

import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;

import edu.mit.media.wockets.DataLogger.DefinedExceptions.SAXErrorException;
import edu.mit.media.wockets.DataLogger.DefinedExceptions.SAXFatalException;

@Controller
public class DataLogController {
	
//	@RequestMapping(value="/isAndroidDataLogValid.html",method=RequestMethod.GET)
//	public void isAndroidDataLogValid(HttpServletRequest request, HttpServletResponse response)
//	{
//		boolean result = true;
//		try{
//			//InputStream inputStream = request.getInputStream();//get input stream from Http request
//			InputStream inputStream = new FileInputStream("C:/Users/Salim/Desktop/Wockets/TestData.xml");
//			SAXSource source = new SAXSource(new InputSource(inputStream));
//			result = DataLoggerUtility.isValidate("C:/Users/Salim/Desktop/Wockets/Wockets_HttpPostreq_Xsd.xsd", source);
//			}
//		catch(Exception ex)
//		{
//			ex.printStackTrace();
//		}
//		if(!result)
////			System.out.println("valid");
////		else
//		{
//			try{response.sendError(response.SC_BAD_REQUEST,"Invalid xml format");}
//			catch(Exception e){e.printStackTrace();}
//		}
//
//	}
	
	@RequestMapping(value="/AndroidDataLog.html", method=RequestMethod.GET)
	public void LogAndroidData(HttpServletRequest request, HttpServletResponse response)
	{
		DataContainer dataContainer;	
		try{
			InputStream inputStream = request.getInputStream();
			SAXParserFactory factory = SAXParserFactory.newInstance();
			factory.setValidating(false);
			factory.setNamespaceAware(true);
			
			//****************************
			SchemaFactory schemaFactory = SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema");
			//factory.setSchema(schemaFactory.newSchema(new Source[] {new StreamSource("C:/Users/Salim/Desktop/Wockets/Wockets_HttpPostreq_Xsd.xsd")}));
			//load xsd as inputStream for validation
			InputStream xsdStream = Thread.currentThread().getContextClassLoader().getResourceAsStream("Wockets_HttpPostreq_Xsd.xsd");
			factory.setSchema(schemaFactory.newSchema(new Source[] {new StreamSource(xsdStream)}));
			//******************************
			SAXParser saxParser = factory.newSAXParser();
			//saxParser.parse(inputStream, new SAXHandler());
			//******************
			XMLReader reader = saxParser.getXMLReader();
			reader.setErrorHandler(new SAXErrorHandler());
			dataContainer = new DataContainer();//create a data container object to contain all wocket log data
			reader.setContentHandler(new SAXHandler(dataContainer));
			reader.parse(new InputSource(new java.io.FileInputStream("C:/Users/Salim/Documents/deskTop/Wockets/TestData.xml")));
			//******************
			//saxParser.parse("C:/Users/Salim/Desktop/Wockets/TestData.xml", new SAXHandler());
			//insert all Log data to DB
			DataLoggerUtility.insertDataToDB(dataContainer);
			}
//			SAXSource source;
//			try{
//				//InputStream inputStream = request.getInputStream();//get input stream from Http request
//				InputStream inputStream = new FileInputStream("C:/Users/Salim/Desktop/Wockets/TestData.xml");
//
//				source = new SAXSource(new InputSource(new java.io.FileInputStream("C:/Users/Salim/Desktop/Wockets/TestData.xml")));
//				source = new SAXSource(new InputSource(inputStream));
//				boolean result = DataLoggerUtility.isValidate("C:/Users/Salim/Desktop/Wockets/Wockets_HttpPostreq_Xsd.xsd", source);
//				if(!result)
//					System.out.println("Invalid");
//				else
//				{
//					SAXParser saxParser = SAXParserFactory.newInstance().newSAXParser();//create instance of SAX parser
//					//parse input http xml and set default handler to instance of SAXHandler class
//					saxParser.parse(inputStream, new SAXHandler());
//				}
//					
//			}
			catch(ParserConfigurationException pce)
			{
				pce.printStackTrace();
			}
			catch(SAXFatalException sfe)
			{
				try{response.sendError(response.SC_BAD_REQUEST,sfe.toString());}
				catch(Exception e){e.printStackTrace();}
			}
			catch(SAXErrorException see)
			{
				try{response.sendError(response.SC_BAD_REQUEST,see.toString());}
				catch(Exception e){e.printStackTrace();}
			}
			catch(SAXException sae)
			{
				try{response.sendError(response.SC_BAD_REQUEST,sae.toString());}
				catch(Exception e){e.printStackTrace();}
			}
			catch(IOException ioEx)
			{
				ioEx.printStackTrace();
			}
			catch(Exception e)
			{
				e.printStackTrace();
			}
			finally
			{
				dataContainer = null;//clear dataContainer resources
			}
}

}
