package wocketXML;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;

import java.io.IOException;
import java.io.PrintWriter;

import org.xmlpull.v1.XmlPullParserException;
import org.xmlpull.v1.XmlPullParserFactory;
import org.xmlpull.v1.XmlSerializer;

import wockets.data.AxesCalibration;
import wockets.data.CalibValues;


public class XMLWriter {
	
	//private static SensorDataInfo[] sensors;
    private static String fileName = "wocketCalibration.xml";

    public static void write (CalibValues cValues) throws XmlPullParserException, IOException {
    	
    	CalibValues calibrationValues = cValues;
    	int[] batteryCal= calibrationValues.getBattery_calibration(); 
		AxesCalibration[]axisCalibration = calibrationValues.getAxisCalibration();
    	File wocketFile = new File(fileName);
		
		if(!wocketFile.exists()){
			wocketFile.createNewFile();
		}
		BufferedWriter writer = new BufferedWriter(new FileWriter(wocketFile));
		
    	XmlPullParserFactory factory = XmlPullParserFactory.newInstance(
            System.getProperty(XmlPullParserFactory.PROPERTY_NAME), null);
        XmlSerializer xmlSerializer = factory.newSerializer();
        System.out.println("serializer implementation class is "+xmlSerializer.getClass());
        
        xmlSerializer.setOutput(writer);
		xmlSerializer.startDocument("UTF-8",true);
		
		xmlSerializer.startTag(null, "SENSORDATA");
		xmlSerializer.attribute(null, "xmlns", "urn:mites-schema");
		xmlSerializer.attribute(null, "dataset", "house_n data");
		
		xmlSerializer.startTag(null, "SENSORS");
		//if(sensors != null && sensors.length > 0){
			//for (int i = 0; i < sensors.length; i++) {
				//SensorDataInfo sensor = sensors[i];
				xmlSerializer.startTag(null, "SENSOR");
				
					xmlSerializer.attribute(null, "class", "Wockets");
					
					xmlSerializer.startTag(null, "ID");
					xmlSerializer.attribute(null, "id", ""+calibrationValues.getSensorID());
					xmlSerializer.endTag(null, "ID");				
					
					xmlSerializer.startTag(null, "RANGE");
					xmlSerializer.attribute(null, "xMin", Integer.toString(axisCalibration[0].getMin()));
					xmlSerializer.attribute(null, "xMax", Integer.toString(axisCalibration[0].getMax()));
					xmlSerializer.attribute(null, "yMin", Integer.toString(axisCalibration[1].getMin()));
					xmlSerializer.attribute(null, "yMax", Integer.toString(axisCalibration[1].getMax()));
					xmlSerializer.attribute(null, "zMin", Integer.toString(axisCalibration[2].getMin()));
					xmlSerializer.attribute(null, "zMax", Integer.toString(axisCalibration[2].getMax()));
					xmlSerializer.endTag(null, "RANGE");
					
					xmlSerializer.startTag(null, "NOISE");
					xmlSerializer.attribute(null, "x", Integer.toString(axisCalibration[0].getNoise()));
					xmlSerializer.attribute(null, "y", Integer.toString(axisCalibration[1].getNoise()));
					xmlSerializer.attribute(null, "z", Integer.toString(axisCalibration[2].getNoise()));
					xmlSerializer.endTag(null, "NOISE");
					
					xmlSerializer.startTag(null, "ACCELEROMETERCALIBRATION");
					xmlSerializer.attribute(null, "x1g",  Integer.toString(axisCalibration[0].getMid()));
					xmlSerializer.attribute(null, "xn1g", Integer.toString(axisCalibration[0].getNegativeMid()));
					xmlSerializer.attribute(null, "y1g",  Integer.toString(axisCalibration[1].getMid()));
					xmlSerializer.attribute(null, "yn1g", Integer.toString(axisCalibration[1].getNegativeMid()));
					xmlSerializer.attribute(null, "z1g",  Integer.toString(axisCalibration[2].getMid()));
					xmlSerializer.attribute(null, "zn1g", Integer.toString(axisCalibration[2].getNegativeMid()));						
					xmlSerializer.endTag(null, "ACCELEROMETERCALIBRATION");
					
					xmlSerializer.startTag(null, "BATTERYCALIBRATION");
					xmlSerializer.attribute(null, "battery100value", Integer.toString(batteryCal[0]));
					xmlSerializer.attribute(null, "battery80value",  Integer.toString(batteryCal[1]));
					xmlSerializer.attribute(null, "battery60value",  Integer.toString(batteryCal[2]));
					xmlSerializer.attribute(null, "battery40value",  Integer.toString(batteryCal[3]));
					xmlSerializer.attribute(null, "battery20value",  Integer.toString(batteryCal[4]));
					xmlSerializer.attribute(null, "battery10value",  Integer.toString(batteryCal[5]));
					xmlSerializer.endTag(null, "BATTERYCALIBRATION");
					
					xmlSerializer.startTag(null, "SAMPLINGRATE");
					xmlSerializer.attribute(null, "SR",  Integer.toString(calibrationValues.getSamplingRate()));
					xmlSerializer.endTag(null, "SAMPLINGRATE");
				
				xmlSerializer.endTag(null, "SENSOR");
		//	}
		//}
			
		xmlSerializer.endTag(null, "SENSORDATA");
		xmlSerializer.endDocument();
		
		xmlSerializer.flush();
		writer.flush();
		writer.close();        
    }
		
}
	
