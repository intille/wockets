using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.Xml.Schema;
using System.Collections;
using System.Text.RegularExpressions;


namespace AXML
{
    public class Reader
    {

        public const string DEFAULT_XSD_FILE = "ActivityLabelsRealtime.xsd";    
        public const string DEFAULT_XML_FILE = "ActivityLabelsRealtime.xml";

        private string xmlFile;
        private string xsdFile;
        //private System.Windows.Forms.Form caller;

        //do not validate
        //public Reader(string fileName)
        //{
         //   this.xmlFile = fileName;
        //}
        public Reader(string masterDirectory, string dataDirectory)//, System.Windows.Forms.Form caller)
        {
            this.xmlFile = dataDirectory +"\\"+ DEFAULT_XML_FILE;
            this.xsdFile = masterDirectory + DEFAULT_XSD_FILE;
            //this.caller = caller;
        }


        public Reader(string masterDirectory, string dataDirectory, string filename)//, System.Windows.Forms.Form caller)
        {
            this.xmlFile = dataDirectory + "\\" + filename;
            this.xsdFile = null;
            //this.caller = caller;
        }

        public Annotation parse()
        {
            Annotation annotation = new Annotation();
            XmlDocument dom = new XmlDocument();
            dom.Load(this.xmlFile);
            XmlNode xNode=dom.DocumentElement;

            if ( (xNode.Name == Constants.ANNOTATION_ELEMENT) && (xNode.HasChildNodes))
            {
                
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    //Console.WriteLine(iNode.Name);

                    //parsing file information
                    if (iNode.Name == Constants.FILE_INFO_ELEMENT)
                    {                        
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            //Console.WriteLine(jNode.Name);

                            foreach (XmlAttribute jAttribute in jNode.Attributes)
                            {
                                if (jAttribute.Name == Constants.NAME_ATTRIBUTE)
                                {
                                    if (jNode.Name == Constants.SUBJECT_ELEMENT)
                                    {
                                        annotation.FileInfo.Subject = jAttribute.Value;
                                    }
                                    else if (jNode.Name == Constants.OBSERVER_ELEMENT)
                                    {                                        
                                        annotation.FileInfo.Observer = jAttribute.Value;
                                    }
                                    else if (jNode.Name == Constants.LOCATION_ELEMENT)
                                    {
                                        annotation.FileInfo.Location = jAttribute.Value;
                                    }
                                    else if (jNode.Name == Constants.NOTES_ELEMENT)
                                    {
                                        annotation.FileInfo.Notes = jAttribute.Value;
                                    }                                    
                                }
                            }


                          
                        }
                    }
                        //parsing labels
                    else if (iNode.Name == Constants.LABELS_ELEMENT)
                    {

                        //parsing the categories
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            //double frequency = 1500;
                            if (jNode.Name == Constants.CATEGORY_ELEMENT)
                            {
                                Category category = new Category();

                                //parsing category attributes
                                foreach (XmlAttribute jAttribute in jNode.Attributes)
                                {
                                   if (jAttribute.Name == Constants.NAME_ATTRIBUTE)
                                   {
                                       category.Name = jAttribute.Value.Replace("A - ", "").Replace("A- ", "").Replace(' ', '-').Replace(',', '_').ToLower();
                                   }else if (jAttribute.Name == Constants.PROPERTY_ATTRIBUTE)
                                   {
                                            category.Property=jAttribute.Value;
                                   }
                                }
          
                                //parsing category labels
                                foreach (XmlNode kNode in jNode.ChildNodes)
                                {
                                    foreach (XmlAttribute kAttribute in kNode.Attributes)
                                    {
                                        
                                        if (kAttribute.Name == Constants.NAME_ATTRIBUTE)
                                        {
                                            Label newlabel = new Label(kAttribute.Value.Replace("A - ","").Replace("A- ","").Replace(' ', '-').Replace(',', '_').ToLower(), category.Name);
                                            //newlabel.InitializeTone(this.caller.Handle.ToInt32(),frequency);
                                            category.Labels.Add(newlabel);
                                            //frequency += 200;
                                        }
                                         

                                 
                                    }
                                }

                                annotation.Categories.Add(category);
                            }
                        }

                    }
                    else if (iNode.Name == Constants.DATA_ELEMENT)
                    {
                        int startYear = 0, startMonth = 0, startDay = 0, startHour = 0,startMinute = 0,startSecond = 0, startMillisecond=0;
                        int endYear = 0, endMonth = 0, endDay = 0, endHour = 0, endMinute = 0, endSecond = 0, endMillisecond = 0;

                        //parsing Annotated Records
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            //double frequency = 1500;
                            if (jNode.Name == Constants.LABEL_ELEMENT)
                            {                                                                                       

                                //parsing category attributes
                                foreach (XmlAttribute jAttribute in jNode.Attributes)
                                {                                  
                                    if (jAttribute.Name == Constants.DATE_ATTRIBUTE)
                                    {
                                        //parse date
                                        string p =@"(\d+)/(\d+)/(\d+)";
                                        Match m = Regex.Match(jAttribute.Value, p);
                                        if (m.Groups.Count == 4)
                                        {
                                            startMonth = endMonth = Convert.ToInt32(m.Groups[1].Value);
                                            startDay = endDay = Convert.ToInt32(m.Groups[2].Value);
                                            startYear = endYear = Convert.ToInt32(m.Groups[3].Value);

                                        }
                                        else
                                            throw new Exception("Error parsing " + Constants.DATE_ATTRIBUTE + ". " + jAttribute.Value);
                                    }

                                    else if (jAttribute.Name == Constants.STARTTIME_ATTRIBUTE)
                                    {
                                        //parse date   
                                        string p = @"(\d+):(\d+):(\d+)([.](\d+))?";
                                        Match m = Regex.Match(jAttribute.Value, p);
                                        startHour = Convert.ToInt32(m.Groups[1].Value);
                                        startMinute = Convert.ToInt32(m.Groups[2].Value);
                                        startSecond = Convert.ToInt32(m.Groups[3].Value);
                                        startMillisecond = 0;
                                        if (m.Groups[5].Value.Length>0)                                                                   
                                            startMillisecond = Convert.ToInt32(m.Groups[5].Value);                                                                              
                                            
                                    }

                                    else if (jAttribute.Name == Constants.ENDTIME_ATTRIBUTE)
                                    {
                                        //parse date
                                        string p = @"(\d+):(\d+):(\d+)([.](\d+))?";
                                        Match m = Regex.Match(jAttribute.Value, p);
                                        endHour = Convert.ToInt32(m.Groups[1].Value);
                                        endMinute = Convert.ToInt32(m.Groups[2].Value);
                                        endSecond = Convert.ToInt32(m.Groups[3].Value);
                                        endMillisecond = 0;
                                        if (m.Groups[5].Value.Length > 0)
                                            endMillisecond = Convert.ToInt32(m.Groups[5].Value);
                                    }
                                    else if (jAttribute.Name == Constants.STARTDATE_ATTRIBUTE)
                                    {
                                        //parse date
                                        //2008-06-17 14:03:42-07:00
                                        string p = @"^(\d+)-(\d+)-(\d+)\s+(\d+):(\d+):(\d+)";
                                        Match m = Regex.Match(jAttribute.Value, p);
                                        if ((m.Groups.Count == 7) || (m.Groups.Count == 6))
                                        {
                                            startMonth = Convert.ToInt32(m.Groups[2].Value);
                                            startDay =  Convert.ToInt32(m.Groups[3].Value);
                                            startYear = Convert.ToInt32(m.Groups[1].Value);
                                            startHour = Convert.ToInt32(m.Groups[4].Value);
                                            startMinute = Convert.ToInt32(m.Groups[5].Value);
                                            startSecond = Convert.ToInt32(m.Groups[6].Value);
                                            startMillisecond = 0; 

                                        }
                                        else
                                            throw new Exception("Error parsing " + Constants.STARTDATE_ATTRIBUTE + ". " + jAttribute.Value);
                                    }
                                    else if (jAttribute.Name == Constants.ENDDATE_ATTRIBUTE)
                                    {
                                        //parse date
                                        string p = @"^(\d+)-(\d+)-(\d+)\s+(\d+):(\d+):(\d+)";
                                        Match m = Regex.Match(jAttribute.Value, p);
                                        if ((m.Groups.Count == 7) || (m.Groups.Count == 6)) 
                                        {
                                            endMonth = Convert.ToInt32(m.Groups[2].Value);
                                            endDay = Convert.ToInt32(m.Groups[3].Value);
                                            endYear = Convert.ToInt32(m.Groups[1].Value);
                                            endHour = Convert.ToInt32(m.Groups[4].Value);
                                            endMinute = Convert.ToInt32(m.Groups[5].Value);
                                            endSecond = Convert.ToInt32(m.Groups[6].Value);
                                            endMillisecond = 0; 

                                        }
                                        else
                                            throw new Exception("Error parsing " + Constants.ENDDATE_ATTRIBUTE + ". " + jAttribute.Value);
                                    }
                                    
                                }
                                DateTime startDT = new DateTime(startYear, startMonth, startDay, startHour, startMinute,
                                    startSecond, startMillisecond);
                                DateTime endDT = new DateTime(endYear, endMonth, endDay, endHour, endMinute, endSecond,
                                    endMillisecond);
                                AnnotatedRecord annotatedRecord = new AnnotatedRecord();
                                
                                annotatedRecord.StartDate = startDT.ToString("MM-dd-yyyy");
                                annotatedRecord.StartHour = startDT.Hour;
                                annotatedRecord.StartMinute = startDT.Minute;
                                annotatedRecord.StartSecond = startDT.Second;
                                annotatedRecord.StartMillisecond = startDT.Millisecond;
                                TimeSpan ts = startDT.Subtract(new DateTime(1970, 1, 1, 0, 0, 0,0));
                                //TimeSpan ts = startDT - new DateTime(1970, 1, 1, 0, 0, 0, 0);
                                annotatedRecord.StartUnix = ts.TotalMilliseconds;
                                //for some data might require day light savings adjustment
                                //annotatedRecord.StartUnix -= 1 * 60 * 60 * 1000;
                             
                                annotatedRecord.EndDate = endDT.ToString("MM-dd-yyyy");
                                annotatedRecord.EndHour = endDT.Hour;
                                annotatedRecord.EndMinute = endDT.Minute;
                                annotatedRecord.EndSecond = endDT.Second;
                                annotatedRecord.EndMillisecond = endDT.Millisecond;
                                ts = endDT.Subtract(new DateTime(1970, 1, 1, 0, 0, 0, 0,0));
                                //ts = endDT - new DateTime(1970, 1, 1, 0, 0, 0, 0, 0);
                                annotatedRecord.EndUnix = ts.TotalMilliseconds;    
                                //annotatedRecord.EndUnix -= 1 * 60 * 60 * 1000;


                                //parsing values
                                foreach (XmlNode kNode in jNode.ChildNodes)
                                {
                                    string label = "", category = "";

                                    foreach (XmlAttribute kAttribute in kNode.Attributes)
                                    {
                                        if (kAttribute.Name == Constants.LABEL_ATTRIBUTE)
                                        {
                                            label = kAttribute.Value.Replace("A - ","").Replace("A- ","").Replace(' ', '-').Replace(',', '_').ToLower();
                                        }
                                        else if (kAttribute.Name == Constants.CATEGORY_ATTRIBUTE)
                                        {
                                            category= kAttribute.Value;
                                        }
                                    }

                                    Label newlabel = new Label(label, category);
                                    annotatedRecord.Labels.Add(newlabel);
                                }

                                annotation.Data.Add(annotatedRecord);
                            }
                        }

                    }
                }
            }

            return annotation;            
        }

        public bool validate()
        {

            XmlSchemaSet sc = new XmlSchemaSet();
            // Add the schema to the collection.

            sc.Add("urn:mites-schema", this.xsdFile);
            // Set the validation settings.    
            XmlReaderSettings settings = new XmlReaderSettings();
            settings.ValidationType = ValidationType.Schema;
            settings.Schemas = sc;
            settings.ValidationEventHandler += new ValidationEventHandler(ValidationCallBack);
            // Create the XmlReader object.
            XmlReader reader = XmlReader.Create(this.xmlFile, settings);
            // Parse the file. 
            while (reader.Read())
            {
                ;
            }
            return true;


        }

        private void ValidationCallBack(object sender, ValidationEventArgs e)
        {
            throw new Exception(e.Message);
        }
    }


}
