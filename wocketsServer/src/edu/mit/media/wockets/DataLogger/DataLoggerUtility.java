package edu.mit.media.wockets.DataLogger;

import java.io.File;
import java.io.IOException;

import javax.xml.XMLConstants;
import javax.xml.transform.sax.SAXSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;

import org.hibernate.Session;
import org.hibernate.Transaction;
import org.xml.sax.SAXException;

import edu.mit.media.wockets.DataLogger.DataLoggerBean.*;
import edu.mit.media.wockets.utility.HibernateSession;

public class DataLoggerUtility {
	
	public static Schema loadXsdSchema(String name) 
	{
		Schema schema = null;
		try {
		      String language = XMLConstants.W3C_XML_SCHEMA_NS_URI;
		      SchemaFactory factory = SchemaFactory.newInstance(language);
		      schema = factory.newSchema(new File(name));
		    } catch (Exception e) {
		      System.out.println(e.toString());
		    }
		 return schema;
	}
	
	public static boolean isValidate(String xsdFilePath, SAXSource source)
	{
		boolean result = true;
		Schema xsdSchema = loadXsdSchema(xsdFilePath);
		Validator validator = xsdSchema.newValidator();
		try{
		validator.validate(source);
		}
		catch(SAXException saxEx)
		{
			result = false;
		}
		catch(Exception e)
		{
			e.printStackTrace();
		}
		return result;
	}
	
	//insert all data to database
	public static void insertDataToDB(DataContainer dataContainer)
	{
		int rowNbr = 0;//int to check number of records
		Session session = HibernateSession.getSession();
		Transaction tx = session.beginTransaction();
		//insert prompting record
		for(Prompting prompt: dataContainer.getPromptingList())
		{
			session.save(prompt);
			rowNbr++;
			checkFirstLevelCache(rowNbr, session);
		}
		//insert into PhoneStats
		for(PhoneStats ps:dataContainer.getPhoneStatsList())
		{
			session.save(ps);
			rowNbr++;
			checkFirstLevelCache(rowNbr, session);
		}
		//insert WocketStats
		for(WocketStats ws: dataContainer.getWocketStateList())
		{
			session.save(ws);
			rowNbr++;
			checkFirstLevelCache(rowNbr, session);
		}
		//insert swapping and SwappedSensor record
		for(Swapping s: dataContainer.getSwappingList())
		{
			session.save(s);
			rowNbr++;
			for(SwappedSensor sws:s.getSwappedSensor())
			{
				sws.setSwappingId(s.getSwappingId());
				session.save(sws);
				rowNbr++;
				checkFirstLevelCache(rowNbr, session);
			}
			
			checkFirstLevelCache(rowNbr, session);
		}
		
		tx.commit();
		HibernateSession.sessionClose(session);
	}
	
	//flush and clear session cache once it reached to 20
	public static void checkFirstLevelCache(int rowNbr, Session session)
	{
		if(rowNbr%20==0)
		{
			session.flush();
			session.clear();
		}
	}
	

}
