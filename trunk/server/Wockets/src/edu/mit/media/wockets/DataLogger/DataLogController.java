package edu.mit.media.wockets.DataLogger;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringWriter;

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

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import edu.mit.media.wockets.DataLogger.DefinedExceptions.SAXErrorException;
import edu.mit.media.wockets.DataLogger.DefinedExceptions.SAXFatalException;

@Controller
public class DataLogController {
	
	
	@RequestMapping(value="/AndroidDataLog.html", method=RequestMethod.POST)
	public void LogAndroidData(HttpServletRequest request, HttpServletResponse response)
	{
		//JPN
		DataContainer dataContainer;
		
		try
		{
			InputStream inputStream = request.getInputStream();
			Gson gson = new GsonBuilder().serializeNulls().setDateFormat("MMM d, yyyy h:mm:ss a").create();
			Reader reader = new InputStreamReader(inputStream);
			
			//JPN
//			DataContainer dataContainer = gson.fromJson(reader, DataContainer.class);
			dataContainer = gson.fromJson(reader, DataContainer.class);
			
			String phoneId = dataContainer.getPhoneId();
			//check phoneID null value
			if(phoneId == null)
			{
				try{response.sendError(response.SC_BAD_REQUEST,"PhoneID can not be NULL.");
					return;
				}
				catch(Exception e){e.printStackTrace();}
			}
			
			//validate phoneID and get particpant_Id based on phoneID
			int participant_Id = DataLoggerUtility.getParticipantId(phoneId);
			if(participant_Id == -1)
			{
				try{response.sendError(response.SC_BAD_REQUEST,"No participant_Id found for PhoneID:"+phoneId);
					return;
				}
				catch(Exception e){e.printStackTrace();}
			}
			new UpdateDataContainer().updateDataContainerGSON(dataContainer);
			
			//insert all Log data to DB
			DataLoggerUtility.insertDataToDB(dataContainer,participant_Id);
		}
		catch(IOException ioe)
		{
			try{response.sendError(response.SC_BAD_REQUEST,ioe.getMessage());}
			catch(Exception e){e.printStackTrace();}
		}
        catch(Exception ex)
        {
			try{response.sendError(response.SC_BAD_REQUEST,ex.getMessage());}
			catch(Exception e){e.printStackTrace();}
        }
		finally
		{
			dataContainer = null;
		}
	}

}
