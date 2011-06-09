using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;
using System.IO;


namespace AXML
{
    public class Annotation
    {

        public const string DEFAULT_OUTPUT_FILE = "AnnotationIntervals";
        public const string DEFAULT_OUTPUT_CSV_FILE = "AnnotationIntervals";
        private string output_file;
        private string output_csv_file;
        private FileInformation fileInfo;
        private ArrayList categories;
        private ArrayList data;
        private string dataDirectory;
        private string fileSuffix;

        public Annotation()
        {

            this.fileInfo = new FileInformation();
            this.categories = new ArrayList();
            this.data = new ArrayList();
            fileSuffix = DateTime.Now.ToString("-yyyy-MM-dd-HH-mm-ss");
            this.output_file = DEFAULT_OUTPUT_FILE + ".xml";
            this.output_csv_file = DEFAULT_OUTPUT_CSV_FILE + ".csv";
        }

        public Annotation(string output_file,string output_csv_file){
               
            this.fileInfo=new FileInformation();
            this.categories = new ArrayList();
            this.data = new ArrayList();
            this.output_file = output_file;
            this.output_csv_file = output_csv_file;
        }

        public string DataDirectory
        {
            get
            {
                return this.dataDirectory;
            }
            set
            {
                this.dataDirectory = value;
            }
        }
        public string OutputFile
        {
            get
            {
                return this.output_file;
            }
        }

        public string OutputCSVFile
        {
            get
            {
                return this.output_csv_file;
            }
        }
        public FileInformation FileInfo
        {
            get
            {
                return this.fileInfo;
            }
        }

        public ArrayList Categories
        {
            get
            {
                return this.categories;
            }
        }

        public ArrayList Data
        {
            get
            {
                return this.data;
            }
        }

#if (!PocketPC)
        public void RemoveData(string[] labels)
        {
            for (int i = 0; (i < labels.Length); i++)
            {
                for (int j = this.data.Count-1; (j >=0 ); j--)
                {
                    if (((Label)((AnnotatedRecord)this.data[j]).Labels[0]).Name.Contains(labels[i]))
                        this.data.RemoveAt(j);
                }
            }
        }
#endif
        public string ToXML()
        {
            string xml = "";

            xml += "<?xml version='1.0'?>\n";
            xml += "<" + Constants.ANNOTATION_ELEMENT + " xmlns=\"urn:mites-schema\">\n";
            xml += this.fileInfo.ToXML();
            xml += "<" + Constants.LABELS_ELEMENT + ">\n";
            foreach (Category category in this.categories)
            {
                xml += category.ToXML();
            }
            xml += "</" + Constants.LABELS_ELEMENT + ">\n";
            xml += "<" + Constants.DATA_ELEMENT + ">\n";
            foreach (AnnotatedRecord annotatedRecord in this.data)
            {
                xml += annotatedRecord.ToXML();
            }
            xml += "</" + Constants.DATA_ELEMENT + ">\n";
            xml += "</"+Constants.ANNOTATION_ELEMENT+">\n";
            return xml;
        }

        public void ToXMLFile()
        {
            // create a writer and open the file
            TextWriter tw = new StreamWriter(this.dataDirectory+"\\"+this.output_file);

            // write a line of text to the file
            tw.WriteLine(ToXML());

            // close the stream
            tw.Close();
        }

        public void ToCSVFile()
        {
            string csv = "";

            csv += Constants.STARTTIME_ATTRIBUTE + "," + Constants.ENDTIME_ATTRIBUTE + "," + Constants.COLOR_ATTRIBUTE;
            foreach (Category category in this.categories)
            {
                csv += "," + category.Name;
            }
            csv += "\n";
            foreach (AnnotatedRecord annotatedRecord in this.data)
            {
                csv += annotatedRecord.ToCSV()+"\n";
            }

            // create a writer and open the file
            TextWriter tw = new StreamWriter(this.dataDirectory + "\\" + this.output_csv_file);

            // write a line of text to the file
            tw.WriteLine(csv);

            // close the stream
            tw.Close();
        }

        public Annotation Intersect(Annotation a)
        {
            int z = 0;
            a = a.copy();
            Annotation output = this.copy();
            ArrayList aData = a.Data;
            ArrayList myData = output.Data;
            ArrayList outputData = new ArrayList();

            foreach (AXML.AnnotatedRecord record1 in aData)
            {
                String label1 = ((AXML.Label)record1.Labels[0]).Name;
                if (label1 == "GoodData") //ignore gooddata fields
                    continue;

                foreach (AXML.AnnotatedRecord record2 in myData)
                {
                    String label2 = ((AXML.Label)record2.Labels[0]).Name;

                  //  if ((record2.StartMillisecond == 13) && (record2.StartSecond == 3) &&
                   //     (record1.StartMillisecond == 107) && (record1.StartSecond == 0))
                   //    z++;
                    if (label1 == label2)   //if the field name matches, process data entry
                    {
                        //move on to next iteration since there will never be intersection
                        if ((record1.EndUnix < record2.StartUnix) || (record2.EndUnix < record1.StartUnix))
                            continue;
                        //if intersection exists
                        else
                        {
                            AXML.AnnotatedRecord newrecord = record1.copy();

                            //pick the highest start time and lowest end time out of the pair
                            if (record1.StartUnix < record2.StartUnix)
                            {
                               
                                newrecord.StartHour = record2.StartHour;
                                newrecord.StartMinute = record2.StartMinute;
                                newrecord.StartSecond = record2.StartSecond;
                                newrecord.StartMillisecond = record2.StartMillisecond;
                                newrecord.StartUnix = record2.StartUnix;
                              
                            }
                           
                           
                            if (record1.EndUnix > record2.EndUnix)
                            {
                                newrecord.EndHour = record2.EndHour;
                                newrecord.EndMinute = record2.EndMinute;
                                newrecord.EndSecond = record2.EndSecond;
                                newrecord.EndMillisecond = record2.EndMillisecond;
                                newrecord.EndUnix = record2.EndUnix;
                            }
                            outputData.Add(newrecord);
                        }
                    }
                }
            }
            output.Data.Clear();
            //copy results back to hte data field of the output Annotation object
            foreach (AXML.AnnotatedRecord obj in outputData)
                output.Data.Add(obj);

            return output;
            //testing purposes, datadirectory can be anything
            //TextWriter writer = new StreamWriter("intersection.xml");
            //writer.WriteLine(output.ToXML());
            //writer.Close();
        }



        public Annotation Difference(Annotation b)
        {
            Annotation a = this.copy();
            ArrayList intersection = b.Data; //Intersect(a).Data;
            Annotation output = this.copy();
            ArrayList tempOutput = new ArrayList();
            ArrayList aData = a.Data;
            int intersectCounter = 0;
            int originalCounter = 1;

            while (intersectCounter < intersection.Count && originalCounter < aData.Count)
            {
                AXML.AnnotatedRecord temp = ((AXML.AnnotatedRecord)intersection[intersectCounter]).copy();
                AXML.AnnotatedRecord original = ((AXML.AnnotatedRecord)aData[originalCounter]).copy();

                //no intersection so add original data
                if (original.EndUnix < temp.StartUnix || temp.EndUnix < original.StartUnix)
                {
                    tempOutput.Add(original);
                    originalCounter++;
                }
                //else there is intersection, add areas outside of intersection
                else
                {
                    double start1 = original.StartUnix;
                    double end1 = temp.StartUnix;
                    double start2 = temp.EndUnix;
                    double end2 = original.EndUnix;
                    if (start1 == end1 && start2 != end2) //use start2 and end2 as constraints
                    {
                        AXML.AnnotatedRecord ann = original.copy();
                        ann.StartHour = temp.EndHour;
                        ann.StartMinute = temp.EndMinute;
                        ann.StartSecond = temp.EndSecond;
                        ann.StartMillisecond = temp.EndMillisecond;
                        ann.StartUnix = temp.EndUnix;
                        tempOutput.Add(ann);
                    }
                    else if (start1 != end1 && start2 == end2)  //use start1 and end1 as constraints
                    {
                        AXML.AnnotatedRecord ann = original.copy();
                        ann.EndHour = temp.StartHour;
                        ann.EndMinute = temp.StartMinute;
                        ann.EndSecond = temp.StartSecond;
                        ann.EndMillisecond = temp.StartMillisecond;
                        ann.EndUnix = temp.StartUnix;
                        tempOutput.Add(ann);
                    }
                    else if (start1 != end1 && start2 != end2)//use both start1 & end1, start2 & end2
                    {
                        AXML.AnnotatedRecord ann1 = original.copy();

                        int oriHour = original.EndHour;
                        int oriMinute = original.EndMinute;
                        int oriSecond = original.EndSecond;
                        int oriMillisecond = original.EndMillisecond;
                        double oriUnix = original.EndUnix;

                        ann1.EndHour = temp.StartHour;
                        ann1.EndMinute = temp.StartMinute;
                        ann1.EndSecond = temp.StartSecond;
                        ann1.EndMillisecond = temp.StartMillisecond;
                        ann1.EndUnix = temp.StartUnix;
                        tempOutput.Add(ann1);

                        AXML.AnnotatedRecord ann2 = new AXML.AnnotatedRecord();
                        foreach (AXML.Label label in ann1.Labels)
                            ann2.Labels.Add(label);
                        ann2.Quality = ann1.Quality;
                        ann2.StartDate = ann1.StartDate;
                        ann2.EndDate = ann1.EndDate;
                        ann2.EndHour = oriHour;
                        ann2.EndMinute = oriMinute;
                        ann2.EndSecond = oriSecond;
                        ann2.EndMillisecond = oriMillisecond;
                        ann2.EndUnix = oriUnix;
                        ann2.StartHour = temp.EndHour;
                        ann2.StartMinute = temp.EndMinute;
                        ann2.StartSecond = temp.EndSecond;
                        ann2.StartMillisecond = temp.EndMillisecond;
                        ann2.StartUnix = temp.EndUnix;
                        tempOutput.Add(ann2);
                    }
                    intersectCounter++;
                    originalCounter++;
                }
            }

            output.Data.Clear();
            //copy results back to hte data field of the output Annotation object
            foreach (AXML.AnnotatedRecord obj in tempOutput)
                output.Data.Add(obj);

            return output;
            //testing purposes, datadirectory can be anything
            //output.DataDirectory = dataDir;
            //TextWriter writer = new StreamWriter(outputDir + fileName);
            //writer.WriteLine(output.ToXML());
           // writer.Close();
        }

        public Annotation copy()
        {
            Annotation ann = new Annotation(output_file, output_csv_file);
            foreach (Category cat in categories)
                ann.Categories.Add(cat);
            foreach (AnnotatedRecord annRecord in data)
                ann.Data.Add(annRecord.copy());
            ann.DataDirectory = dataDirectory;
            ann.FileInfo.Subject = fileInfo.Subject;
            ann.FileInfo.Observer = fileInfo.Observer;
            ann.FileInfo.Notes = fileInfo.Notes;
            ann.FileInfo.Location = fileInfo.Location;
            return ann;
        }

    }
}
