using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using Wockets.Utils;


using System.Collections;
using System.IO;



namespace Wockets.Data.Annotation
{
    public class Session: XMLSerializable
    {
        private const string ANNOTATION_ELEMENT="ANNOTATION";
        private const string FILEINFO_ELEMENT = "FILEINFO";
        private const string SUBJECT_ELEMENT="SUBJECT";
        private const string LOCATION_ELEMENT="LOCATION";
        private const string OBSERVER_ELEMENT="OBSERVER";
        private const string NOTES_ELEMENT="NOTES";
        private const string NAME_ATTRIBUTE = "NAME";

        private const string ENDDATE_ATTRIBUTE = "ENDDATE";
        private const string STARTTIME_ATTRIBUTE = "STARTTIME";
        private const string ENDTIME_ATTRIBUTE = "ENDTIME";
        private const string COLOR_ATTRIBUTE = "COLOR";

        private string subject;
        private string location;
        private string observer;
        private string notes;

        private ConcurrentActivityLists activityLists;
        private AnnotationList annotations;


        //private string output_file;
        //private string output_csv_file;
        private string dataDirectory;






        public Session()
        {
            this.activityLists = new ConcurrentActivityLists();
            this.annotations = new AnnotationList();


            //check this part
            //this.output_file = FILEINFO_ELEMENT +"_copy"+ ".xml";
            //this.output_csv_file = FILEINFO_ELEMENT + "_copy" + ".csv";

        }


        #region Access Properties
        
        
        public string _Subject
        {
            get
            {
                return this.subject;
            }
            set
            {
                this.subject = value;
            }
        }

        public string _Location
        {
            get
            {
                return this.location;
            }

            set
            {
                this.location = value;
            }
        }

        public string _Observer
        {
            get
            {
                return this.observer;
            }

            set
            {
                this.observer = value;
            }
        }

        public string _Notes
        {
            get
            {
                return this.notes;
            }
            set
            {
                this.notes = value;
            }
        }


        public string _DataDirectory
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



        public ConcurrentActivityLists OverlappingActivityLists
        {
            get
            {
                return this.activityLists;
            }
        }

        public AnnotationList Annotations
        {
            get
            {
                return this.annotations;
            }
        }
        

        #endregion Access Properties



        #region XML fuctions

        public string ToXML()
        {
            string xml = "";
            xml += "<?xml version='1.0'?>\n";
            xml += "<" + ANNOTATION_ELEMENT + " xmlns=\"urn:mites-schema\">\n";
            xml += "<" + FILEINFO_ELEMENT + ">\n";
            xml += "<" + SUBJECT_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.subject + "\" />\n";
            xml += "<" + LOCATION_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.location + "\" />\n";
            xml += "<" + OBSERVER_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.observer + "\" />\n";
            xml += "<" + NOTES_ELEMENT + " " + NAME_ATTRIBUTE + "=\"" + this.notes + "\" />\n";
            xml += "</" + FILEINFO_ELEMENT + ">\n";
            xml += this.activityLists.ToXML();
            xml += this.annotations.ToXML();
            xml += "</" + ANNOTATION_ELEMENT + ">\n";
            return xml;
        }

        public string ToCSV()
        {
            string csv = "";

            csv += STARTTIME_ATTRIBUTE + "," + ENDTIME_ATTRIBUTE + "," + COLOR_ATTRIBUTE + ",";
            csv += this.OverlappingActivityLists.ToCSV();
            csv += "\n";
            csv += this.annotations.ToCSV();
            return csv;
        }
        
        public void FromXML(string xml)
        {
            XmlDocument dom = new XmlDocument();
            dom.Load(xml);
            XmlNode xNode = dom.DocumentElement;

            if ((xNode.Name == ANNOTATION_ELEMENT) && (xNode.HasChildNodes))
            {
                foreach (XmlNode iNode in xNode.ChildNodes)
                {
                    if (iNode.Name == ConcurrentActivityLists.ConcurrentActivityList_ELEMENT)
                        this.activityLists.FromXML(iNode.OuterXml);
                    else if (iNode.Name == AnnotationList.ANNOTATIONLIST_ELEMENT)
                        this.annotations.FromXML(iNode.OuterXml);
                    else if (iNode.Name == FILEINFO_ELEMENT)
                    {
                        foreach (XmlNode jNode in iNode.ChildNodes)
                        {
                            foreach (XmlAttribute jAttribute in jNode.Attributes)
                            {
                                if (jAttribute.Name == NAME_ATTRIBUTE)
                                {
                                    if (jNode.Name == SUBJECT_ELEMENT)
                                        this.subject = jAttribute.Value;
                                    else if (jNode.Name == OBSERVER_ELEMENT)
                                        this.observer = jAttribute.Value;
                                    else if (jNode.Name == LOCATION_ELEMENT)
                                        this.location = jAttribute.Value;
                                    else if (jNode.Name == NOTES_ELEMENT)
                                        this.notes = jAttribute.Value;
                                }
                            }
                        }
                    }
                }

            }
        }
        
        #endregion


        #region Annotation Operations

#region annotators operations

        
        /*
         
        public Session AnnotatorsIntersect(Session a)
        {
            //int z = 0;
            a = a.copy();

            Session output = this.copy();

            //ArrayList aData = a.Data;
            //ArrayList myData = output.Data;
            //ArrayList outputData = new ArrayList();

            AnnotationList aData = this.annotations;
            AnnotationList myData = output.annotations;
            AnnotationList outputData = new AnnotationList();

            //foreach (AXML.AnnotatedRecord record1 in aData)
            foreach (Annotation record1 in aData)
            {
                //String label1 = ((AXML.Label)record1.Labels[0]).Name;
                String label1 = record1.Activities[0]._Name;
 
                //if (label1 == "GoodData") //ignore gooddata fields
                //    continue;

                //foreach (AXML.AnnotatedRecord record2 in myData)
                foreach (Annotation record2 in myData)
                {
                    //String label2 = ((AXML.Label)record2.Labels[0]).Name;
                    String label2 = record2.Activities[0]._Name;


                    // ----  if ((record2.StartMillisecond == 13) && (record2.StartSecond == 3) &&
                    // ----    (record1.StartMillisecond == 107) && (record1.StartSecond == 0))
                    // ----   z++;


                    if (label1 == label2)   //if the field name matches, process data entry
                    {
                        //move on to next iteration since there will never be intersection
                        if ((record1._EndUnix < record2._StartUnix) || (record2._EndUnix < record1._StartUnix))
                            continue;
                        //if intersection exists
                        else
                        {
                            //Annotation newrecord = record1.copy();
                            Annotation newrecord = record1.copy();


                            //pick the highest start time and lowest end time out of the pair
                            if (record1._StartUnix < record2._StartUnix)
                            {

                                newrecord._StartHour = record2._StartHour;
                                newrecord._StartMinute = record2._StartMinute;
                                newrecord._StartSecond = record2._StartSecond;
                                newrecord._StartMillisecond = record2._StartMillisecond;
                                newrecord._StartUnix = record2._StartUnix;

                            }


                            if (record1._EndUnix > record2._EndUnix)
                            {
                                newrecord._EndHour = record2._EndHour;
                                newrecord._EndMinute = record2._EndMinute;
                                newrecord._EndSecond = record2._EndSecond;
                                newrecord._EndMillisecond = record2._EndMillisecond;
                                newrecord._EndUnix = record2._EndUnix;
                            }

                            outputData.Add(newrecord);
                        }
                    }
                }
            }

            //output.Data.Clear();
            output.annotations.Clear();

            //copy results back to hte data field of the output Annotation object
           // foreach (AXML.AnnotatedRecord obj in outputData)
           //     output.Data.Add(obj);
            foreach (Annotation obj in outputData)
                output.annotations.Add(obj);


            return output;

            //testing purposes, datadirectory can be anything
            //TextWriter writer = new StreamWriter("intersection.xml");
            //writer.WriteLine(output.ToXML());
            //writer.Close();
        }

        public Session AnnotatorsDifference(Session b)
       {
           Session a = this.copy();

           //ArrayList intersection = b.Data; //Intersect(a).Data;
           //Annotation output = this.copy();
           //ArrayList tempOutput = new ArrayList();
           //ArrayList aData = a.Data;

           AnnotationList intersection = b.annotations;
           Session output = this.copy();
           
           AnnotationList tempOutput = new AnnotationList();
           AnnotationList aData = a.annotations;
           
           
           int intersectCounter = 0;
           int originalCounter = 1;

           while (intersectCounter < intersection.Count && originalCounter < aData.Count)
           {

               Annotation temp = ((Annotation)intersection[intersectCounter]).copy();
               Annotation original = ((Annotation)aData[originalCounter]).copy();

               //no intersection so add original data
               if (original._EndUnix < temp._StartUnix || temp._EndUnix < original._StartUnix)
               {
                   tempOutput.Add(original);
                   originalCounter++;
               }

               //else there is intersection, add areas outside of intersection
               else
               {
                   double start1 = original._StartUnix;
                   double end1 = temp._StartUnix;

                   double start2 = temp._EndUnix;
                   double end2 = original._EndUnix;


                   if (start1 == end1 && start2 != end2) //use start2 and end2 as constraints
                   {
                       Annotation ann = original.copy();
                       ann._StartHour = temp._EndHour;
                       ann._StartMinute = temp._EndMinute;
                       ann._StartSecond = temp._EndSecond;
                       ann._StartMillisecond = temp._EndMillisecond;
                       ann._StartUnix = temp._EndUnix;
                       tempOutput.Add(ann);
                   }
                   else if (start1 != end1 && start2 == end2)  //use start1 and end1 as constraints
                   {
                       Annotation ann = original.copy();
                       ann._EndHour = temp._StartHour;
                       ann._EndMinute = temp._StartMinute;
                       ann._EndSecond = temp._StartSecond;
                       ann._EndMillisecond = temp._StartMillisecond;
                       ann._EndUnix = temp._StartUnix;
                       tempOutput.Add(ann);
                   }
                   else if (start1 != end1 && start2 != end2)//use both start1 & end1, start2 & end2
                   {
                       Annotation ann1 = original.copy();

                       int oriHour = original._EndHour;
                       int oriMinute = original._EndMinute;
                       int oriSecond = original._EndSecond;
                       int oriMillisecond = original._EndMillisecond;
                       double oriUnix = original._EndUnix;

                       ann1._EndHour = temp._StartHour;
                       ann1._EndMinute = temp._StartMinute;
                       ann1._EndSecond = temp._StartSecond;
                       ann1._EndMillisecond = temp._StartMillisecond;
                       ann1._EndUnix = temp._StartUnix;
                       tempOutput.Add(ann1);

                       Annotation ann2 = new Annotation();

                       //foreach (AXML.Label label in ann1.Labels)
                       //    ann2.Labels.Add(label);
                       
                       
                       foreach (Activity act in ann1.Activities)
                           ann2.Activities.Add(act);
                                                     
                      // ann2.Quality = ann1.Quality;
                       ann2._StartDate = ann1._StartDate;
                       ann2._EndDate = ann1._EndDate;

                       ann2._EndHour = oriHour;
                       ann2._EndMinute = oriMinute;
                       ann2._EndSecond = oriSecond;
                       ann2._EndMillisecond = oriMillisecond;
                       ann2._EndUnix = oriUnix;
                       
                       ann2._StartHour = temp._EndHour;
                       ann2._StartMinute = temp._EndMinute;
                       ann2._StartSecond = temp._EndSecond;
                       ann2._StartMillisecond = temp._EndMillisecond;
                       ann2._StartUnix = temp._EndUnix;
                       
                       tempOutput.Add(ann2);
                   }

                   intersectCounter++;
                   originalCounter++;
               }
           }

           output.annotations.Clear();

           //copy results back to hte data field of the output Annotation object
           //foreach (AXML.AnnotatedRecord obj in tempOutput)
           //    output.Data.Add(obj);

           foreach (Annotation obj in tempOutput)
               output.annotations.Add(obj); 


           return output;
           //testing purposes, datadirectory can be anything
           //output.DataDirectory = dataDir;
           //TextWriter writer = new StreamWriter(outputDir + fileName);
           //writer.WriteLine(output.ToXML());
           // writer.Close();
       }

      
       
        */


#endregion



        #region Old Merge Code
        /*
        public Session Merge(Session session_input)
        {
            Session a = this.copy();
            Session b = session_input.copy();

            AnnotationList aData = a.annotations;
            AnnotationList bData = b.annotations; 

            Session output = this.copy();
            AnnotationList tempOutput = new AnnotationList();


            int aCounter = 0; 
            int bCounter = 0;

            string unknown_label = "unknown";


            #region initialize previous annotations
            
            Annotation prev_a_ann = (Annotation)aData[0].copy();
            prev_a_ann._StartUnix = 0;
            prev_a_ann._EndUnix   = 0;

            Annotation prev_b_ann = (Annotation)bData[0].copy();
            prev_b_ann._StartUnix = 0;
            prev_b_ann._EndUnix   = 0;

            #endregion



            while (aCounter < aData.Count  &&  bCounter < bData.Count )
            {

               
                Annotation a_ann = ((Annotation)aData[aCounter]).copy();
                Annotation b_ann = ((Annotation)bData[bCounter]).copy();

                double start1 = a_ann._StartUnix;
                double start2 = b_ann._StartUnix;

                double end1 = a_ann._EndUnix;
                double end2 = b_ann._EndUnix;




                //no intersection so add the first annotation
                if ( end1 <= start2 ||  end2 <= start1  )
                {

                    #region code

                    if (a_ann._StartUnix < b_ann._StartUnix)
                    {

  
                        #region add record 1 ==> start1 < start2, Case 1
                        //------------ add record one ------------------
                        
                        // the label overlaps since the begining
                       if (start1 >= prev_b_ann._StartUnix)
                        {

                            #region

                            Annotation rec1 = a_ann.copy();

                            // add the intersection with the previous label
                            if (start1 < prev_b_ann._EndUnix)
                            {
                                // add the itersection with the previous label
                                foreach (Activity act in prev_b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                if (prev_b_ann._EndUnix < end1)
                                {
                                    rec1._EndDate = prev_b_ann._EndDate;
                                    rec1._EndHour = prev_b_ann._EndHour;
                                    rec1._EndMinute = prev_b_ann._EndMinute;
                                    rec1._EndSecond = prev_b_ann._EndSecond;
                                    rec1._EndMillisecond = prev_b_ann._EndMillisecond;
                                    rec1._EndUnix = prev_b_ann._EndUnix;
                                }


                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                //if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                if (prev_b_ann._EndUnix < end1)
                                {
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;


                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    aData[aCounter]._StartDate = prev_b_ann._EndDate;
                                    aData[aCounter]._StartHour = prev_b_ann._EndHour;
                                    aData[aCounter]._StartMinute = prev_b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = prev_b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = prev_b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = prev_b_ann._EndUnix;

                                    #endregion

                                }

                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                tempOutput.Add(rec1);

                            }


                            #endregion


                        }
                        else   //(start1 < prev_b_ann._StartUnix)
                        {

                            #region

                            // case starts are different 
                            Annotation rec1 = a_ann.copy();

                            //the segment is not overlapping with the first part of the prev_label, add unknown_label
                            //*** I need to check if it is not necessary to come back another register back
                            //*** to check for overlaps 
                            rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                            if (end1 > prev_b_ann._StartUnix)
                            {
                                rec1._EndDate = prev_b_ann._StartDate;
                                rec1._EndHour = prev_b_ann._StartHour;
                                rec1._EndMinute = prev_b_ann._StartMinute;
                                rec1._EndSecond = prev_b_ann._StartSecond;
                                rec1._EndMillisecond = prev_b_ann._StartMillisecond;
                                rec1._EndUnix = prev_b_ann._StartUnix;
                            }

                            tempOutput.Add(rec1);


                            if (end1 > prev_b_ann._StartUnix)
                            {
                                // Now add the segment intersecting with previous_b_label
                                Annotation rec2 = a_ann.copy();

                                // add the intersection with the previous label
                                if (end1 <= prev_b_ann._EndUnix)
                                {

                                    rec2._StartDate = prev_b_ann._StartDate;
                                    rec2._StartHour = prev_b_ann._StartHour;
                                    rec2._StartMinute = prev_b_ann._StartMinute;
                                    rec2._StartSecond = prev_b_ann._StartSecond;
                                    rec2._StartMillisecond = prev_b_ann._StartMillisecond;
                                    rec2._StartUnix = prev_b_ann._StartUnix;


                                    // add the itersection with the previous label
                                    foreach (Activity act in prev_b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    tempOutput.Add(rec2);

                                    #region update last record

                                    aData[aCounter]._StartDate = prev_b_ann._StartDate;
                                    aData[aCounter]._StartHour = prev_b_ann._StartHour;
                                    aData[aCounter]._StartMinute = prev_b_ann._StartMinute;
                                    aData[aCounter]._StartSecond = prev_b_ann._StartSecond;
                                    aData[aCounter]._StartMillisecond = prev_b_ann._StartMillisecond;
                                    aData[aCounter]._StartUnix = prev_b_ann._StartUnix;

                                    #endregion


                                }
                                else if (end1 > prev_b_ann._EndUnix)
                                {
                                    rec2._StartDate = prev_b_ann._StartDate;
                                    rec2._StartHour = prev_b_ann._StartHour;
                                    rec2._StartMinute = prev_b_ann._StartMinute;
                                    rec2._StartSecond = prev_b_ann._StartSecond;
                                    rec2._StartMillisecond = prev_b_ann._StartMillisecond;
                                    rec2._StartUnix = prev_b_ann._StartUnix;

                                    rec2._EndDate = prev_b_ann._EndDate;
                                    rec2._EndHour = prev_b_ann._EndHour;
                                    rec2._EndMinute = prev_b_ann._EndMinute;
                                    rec2._EndSecond = prev_b_ann._EndSecond;
                                    rec2._EndMillisecond = prev_b_ann._EndMillisecond;
                                    rec2._EndUnix = prev_b_ann._EndUnix;


                                    // add the itersection with the previous label
                                    foreach (Activity act in prev_b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    tempOutput.Add(rec2);


                                    // add the remaining from a_label
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;


                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    aData[aCounter]._StartDate = prev_b_ann._EndDate;
                                    aData[aCounter]._StartHour = prev_b_ann._EndHour;
                                    aData[aCounter]._StartMinute = prev_b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = prev_b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = prev_b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = prev_b_ann._EndUnix;

                                    #endregion

                                }
                            }

                            #endregion


                        }

                        #endregion


                        //prev_a_ann = a_ann; 
                        prev_a_ann = (Annotation)aData[aCounter];
                        aCounter++;

                    }
                    else
                    {
                      
                  


                        #region add record 1 ==> start2 < start1, Case 1
                        //------------ add record one ------------------

                        // the label overlaps since the begining
                        if (start2 >= prev_a_ann._StartUnix)
                        {

                            #region

                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            // add the intersection with the previous label
                            if (start2 < prev_a_ann._EndUnix)
                            {
                                // add the itersection with the previous label
                                foreach (Activity act in prev_a_ann.Activities)
                                { rec1.Activities.Add(act); }

                                // add the label activities
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                if (prev_a_ann._EndUnix < end2)
                                {
                                    rec1._EndDate = prev_a_ann._EndDate;
                                    rec1._EndHour = prev_a_ann._EndHour;
                                    rec1._EndMinute = prev_a_ann._EndMinute;
                                    rec1._EndSecond = prev_a_ann._EndSecond;
                                    rec1._EndMillisecond = prev_a_ann._EndMillisecond;
                                    rec1._EndUnix = prev_a_ann._EndUnix;
                                }


                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                //if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                if (prev_a_ann._EndUnix < end2)
                                {
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    // indicate no intersection with previous label
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }


                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    bData[bCounter]._StartDate = prev_a_ann._EndDate;
                                    bData[bCounter]._StartHour = prev_a_ann._EndHour;
                                    bData[bCounter]._StartMinute = prev_a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = prev_a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = prev_a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = prev_a_ann._EndUnix;

                                    #endregion

                                }

                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                // indicate no intersection with previous label
                                rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                // add the label activities
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                tempOutput.Add(rec1);

                            }


                            #endregion


                        }
                        else   //(start2 < prev_a_ann._StartUnix)
                        {

                            #region

                            // case starts are different 
                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            //the segment is not overlapping with the first part of the prev_label, add unknown_label
                            //*** I need to check if it is not necessary to come back another register back
                            //*** to check for overlaps 
                            rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                            // add the label activities
                            foreach (Activity act in b_ann.Activities)
                            { rec1.Activities.Add(act); }

                            if (end2 > prev_a_ann._StartUnix)
                            {
                                rec1._EndDate = prev_a_ann._StartDate;
                                rec1._EndHour = prev_a_ann._StartHour;
                                rec1._EndMinute = prev_a_ann._StartMinute;
                                rec1._EndSecond = prev_a_ann._StartSecond;
                                rec1._EndMillisecond = prev_a_ann._StartMillisecond;
                                rec1._EndUnix = prev_a_ann._StartUnix;
                            }


                            tempOutput.Add(rec1);



                            if (end2 > prev_a_ann._StartUnix)
                            {

                                // Add the segment intersecting with previous_b_label
                                Annotation rec2 = b_ann.copy();
                                rec2.Activities.Clear();


                                // add the intersection with the previous label
                                if (end2 <= prev_a_ann._EndUnix)
                                {

                                    rec2._StartDate = prev_a_ann._StartDate;
                                    rec2._StartHour = prev_a_ann._StartHour;
                                    rec2._StartMinute = prev_a_ann._StartMinute;
                                    rec2._StartSecond = prev_a_ann._StartSecond;
                                    rec2._StartMillisecond = prev_a_ann._StartMillisecond;
                                    rec2._StartUnix = prev_a_ann._StartUnix;


                                    // add the intersection with the previous label
                                    foreach (Activity act in prev_a_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }


                                    tempOutput.Add(rec2);


                                    #region update last record

                                    bData[bCounter]._StartDate = prev_a_ann._StartDate;
                                    bData[bCounter]._StartHour = prev_a_ann._StartHour;
                                    bData[bCounter]._StartMinute = prev_a_ann._StartMinute;
                                    bData[bCounter]._StartSecond = prev_a_ann._StartSecond;
                                    bData[bCounter]._StartMillisecond = prev_a_ann._StartMillisecond;
                                    bData[bCounter]._StartUnix = prev_a_ann._StartUnix;

                                    #endregion


                                }
                                else //(end2 > prev_a_ann._EndUnix)
                                {
                                    rec2._StartDate = prev_a_ann._StartDate;
                                    rec2._StartHour = prev_a_ann._StartHour;
                                    rec2._StartMinute = prev_a_ann._StartMinute;
                                    rec2._StartSecond = prev_a_ann._StartSecond;
                                    rec2._StartMillisecond = prev_a_ann._StartMillisecond;
                                    rec2._StartUnix = prev_a_ann._StartUnix;

                                    rec2._EndDate = prev_a_ann._EndDate;
                                    rec2._EndHour = prev_a_ann._EndHour;
                                    rec2._EndMinute = prev_a_ann._EndMinute;
                                    rec2._EndSecond = prev_a_ann._EndSecond;
                                    rec2._EndMillisecond = prev_a_ann._EndMillisecond;
                                    rec2._EndUnix = prev_a_ann._EndUnix;


                                    // add the intersection with the previous label
                                    foreach (Activity act in prev_a_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }


                                    tempOutput.Add(rec2);


                                    // add the remaining from a_label
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    // indicate no intersection with previous label
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }

                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    bData[bCounter]._StartDate = prev_a_ann._EndDate;
                                    bData[bCounter]._StartHour = prev_a_ann._EndHour;
                                    bData[bCounter]._StartMinute = prev_a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = prev_a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = prev_a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = prev_a_ann._EndUnix;

                                    #endregion

                                }

                            }

                            #endregion


                        }

                        #endregion
                       
                      //  prev_b_ann = b_ann;  
                       prev_b_ann = (Annotation)bData[bCounter];
                       bCounter++;

                        
                        
                    }

                    #endregion


                }
                //else there is intersection
                else
                {
                  


                    // perfect alignment
                    if (start1 == start2 && end1 == end2)
                    {
                        #region code

                        Annotation rec1 = a_ann.copy();
                        
                        // add the itersection with the b_ann label
                        foreach (Activity act in b_ann.Activities)
                        { rec1.Activities.Add(act); }
                        
                        tempOutput.Add(rec1);

                        //prev_a_ann = a_ann; //   prev_a_ann=(Annotation)aData[aCounter]
                        //prev_b_ann = b_ann; //   prev_b_ann=(Annotation)bData[bCounter]

                        prev_a_ann = (Annotation)aData[aCounter];
                        prev_b_ann = (Annotation)bData[bCounter];

                        aCounter++;
                        bCounter++;


                        #endregion

                    }
                    //if (start1 == end1 && start2 != end2) //use start2 and end2 as constraints
                    else if (start1 == start2 && end1 != end2)
                    {

                        #region code 

                       


                        if (end1 < end2)
                        {
                            //------------ add record one ------------------
                            Annotation rec1 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec1.Activities.Add(act); }

                            tempOutput.Add(rec1);



                            bData[bCounter]._StartDate        = a_ann._EndDate;

                            bData[bCounter]._StartHour        = a_ann._EndHour;
                            bData[bCounter]._StartMinute      = a_ann._EndMinute;
                            bData[bCounter]._StartSecond      = a_ann._EndSecond;
                            bData[bCounter]._StartMillisecond = a_ann._EndMillisecond;
                            bData[bCounter]._StartUnix        = a_ann._EndUnix;

                           
                            //------- increase counters -----------------
                             //prev_a_ann = a_ann; 
                            prev_a_ann = (Annotation)aData[aCounter];

                            aCounter++;
                          

                        }
                        else if (end1 > end2)
                        {
                            //------------ add record one ------------------


                            Annotation rec1 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec1.Activities.Add(act); }

                            rec1._EndDate   = b_ann._EndDate;
                            rec1._EndHour   = b_ann._EndHour;
                            rec1._EndMinute = b_ann._EndMinute;
                            rec1._EndSecond = b_ann._EndSecond;
                            rec1._EndMillisecond = b_ann._EndMillisecond;
                            rec1._EndUnix        = b_ann._EndUnix;
                            

                            tempOutput.Add(rec1);

                         
                            //----------- create "last" record -> open label -------------------

                            aData[aCounter]._StartDate   = b_ann._EndDate;
                            aData[aCounter]._StartHour   = b_ann._EndHour;
                            aData[aCounter]._StartMinute = b_ann._EndMinute;
                            aData[aCounter]._StartSecond = b_ann._EndSecond;
                            aData[aCounter]._StartMillisecond = b_ann._EndMillisecond;
                            aData[aCounter]._StartUnix = b_ann._EndUnix;


                            //------- increase counters -----------------
                          
                            //prev_b_ann = b_ann;   
                            prev_b_ann = (Annotation)bData[bCounter];

                            
                            bCounter++;
                        }

                        #endregion


                    }
                   // else if (start1 != end1 && start2 == end2)  //use start1 and end1 as constraints
                   else if (start1 != start2 && end1 == end2)  //use start1 and end1 as constraints
                    {

                        #region Code


                        if (start1 < start2)
                        {

                            #region add record 1 ==> start1< start2, Case 1

                            //------------ add record one ------------------
                            Annotation rec1 = a_ann.copy();

                            // add the intersection with the prevoius label
                            if (start1 < prev_b_ann._EndUnix)
                            {

                                rec1._EndDate = prev_b_ann._EndDate;

                                rec1._EndHour   = prev_b_ann._EndHour;
                                rec1._EndMinute = prev_b_ann._EndMinute;
                                rec1._EndSecond = prev_b_ann._EndSecond;
                                rec1._EndMillisecond = prev_b_ann._EndMillisecond;
                                rec1._EndUnix        = prev_b_ann._EndUnix;


                                // add the itersection with the previous label
                                foreach (Activity act in prev_b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                {
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour   = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix        = prev_b_ann._EndUnix;

                                    rec1_rm._EndDate   = b_ann._StartDate;
                                    rec1_rm._EndHour   = b_ann._StartHour;
                                    rec1_rm._EndMinute = b_ann._StartMinute;
                                    rec1_rm._EndSecond = b_ann._StartSecond;
                                    rec1_rm._EndMillisecond = b_ann._StartMillisecond;
                                    rec1_rm._EndUnix        = b_ann._StartUnix;

                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                rec1._EndDate = b_ann._StartDate;
                                rec1._EndHour = b_ann._StartHour;
                                rec1._EndMinute = b_ann._StartMinute;
                                rec1._EndSecond = b_ann._StartSecond;
                                rec1._EndMillisecond = b_ann._StartMillisecond;
                                rec1._EndUnix = b_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion


                            #region  add record two

                            //----------- add record 2 -------------------
                            
                            Annotation rec2 = a_ann.copy();
                            
                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec2.Activities.Add(act); }

                            rec2._StartDate   = b_ann._StartDate;
                            rec2._StartHour   = b_ann._StartHour;
                            rec2._StartMinute = b_ann._StartMinute;
                            rec2._StartSecond = b_ann._StartSecond;
                            rec2._StartMillisecond = b_ann._StartMillisecond;
                            rec2._StartUnix        = b_ann._StartUnix;

                            tempOutput.Add(rec2);

                            #endregion


                            #region update changes

                            aData[aCounter]._StartDate = b_ann._StartDate;
                            aData[aCounter]._StartHour = b_ann._StartHour;
                            aData[aCounter]._StartMinute = b_ann._StartMinute;
                            aData[aCounter]._StartSecond = b_ann._StartSecond;
                            aData[aCounter]._StartMillisecond = b_ann._StartMillisecond;
                            aData[aCounter]._StartUnix = b_ann._StartUnix;

                            #endregion

                        }
                        else if (start1 > start2)
                        {
                            #region add record 1 ==> start2 < start1, Case 1

                            //------------ add record one ------------------
                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            // add the intersection with the prevoius label
                            if (start2 < prev_a_ann._EndUnix)
                            {
                                rec1._EndDate   = prev_a_ann._EndDate;
                                rec1._EndHour   = prev_a_ann._EndHour;
                                rec1._EndMinute = prev_a_ann._EndMinute;
                                rec1._EndSecond = prev_a_ann._EndSecond;
                                rec1._EndMillisecond = prev_a_ann._EndMillisecond;
                                rec1._EndUnix        = prev_a_ann._EndUnix;


                                // add the intersection with the previous label
                                foreach (Activity act in prev_a_ann.Activities)
                                { rec1.Activities.Add(act); }

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                tempOutput.Add(rec1);



                                //check if there is a segment remaining to be synchronized
                                if (prev_a_ann._EndUnix < a_ann._StartUnix)
                                {
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate   = prev_a_ann._EndDate;
                                    rec1_rm._StartHour   = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix        = prev_a_ann._EndUnix;

                                    rec1_rm._EndDate   = a_ann._StartDate;
                                    rec1_rm._EndHour   = a_ann._StartHour;
                                    rec1_rm._EndMinute = a_ann._StartMinute;
                                    rec1_rm._EndSecond = a_ann._StartSecond;
                                    rec1_rm._EndMillisecond = a_ann._StartMillisecond;
                                    rec1_rm._EndUnix = a_ann._StartUnix;

                                    // add none, check order
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the b labels in order
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }


                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                // add none, check order
                                rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                rec1._EndDate   = a_ann._StartDate;
                                rec1._EndHour   = a_ann._StartHour;
                                rec1._EndMinute = a_ann._StartMinute;
                                rec1._EndSecond = a_ann._StartSecond;
                                rec1._EndMillisecond = a_ann._StartMillisecond;
                                rec1._EndUnix = a_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion


                            #region  add record two

                            //----------- add record 2 -------------------
                            
                            Annotation rec2 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec2.Activities.Add(act); }

                            tempOutput.Add(rec2);

                            #endregion


                            #region update changes

                            bData[bCounter]._StartDate = a_ann._StartDate;
                            bData[bCounter]._StartHour = a_ann._StartHour;
                            bData[bCounter]._StartMinute = a_ann._StartMinute;
                            bData[bCounter]._StartSecond = a_ann._StartSecond;
                            bData[bCounter]._StartMillisecond = a_ann._StartMillisecond;
                            bData[bCounter]._StartUnix = a_ann._StartUnix;

                            #endregion
                        }

                            //------- increase counters -----------------
                            
                            //prev_a_ann = a_ann;     
                            //prev_b_ann = b_ann;    

                            prev_a_ann = (Annotation)aData[aCounter];
                            prev_b_ann = (Annotation)bData[bCounter];

                            aCounter++;
                            bCounter++;


                        #endregion


                        }
                    else if (start1 != start2 && end1 != end2)//use both start1 & end1, start2 & end2
                    {


                        #region code

                        if (start1 < start2)
                        {



                            #region add record 1

                            //------------ add record one ------------------
                            Annotation rec1 = a_ann.copy();

                            // add the intersection with the prevoius label
                            if (start1 < prev_b_ann._EndUnix)
                            {

                                rec1._EndDate = prev_b_ann._EndDate;

                                rec1._EndHour = prev_b_ann._EndHour;
                                rec1._EndMinute = prev_b_ann._EndMinute;
                                rec1._EndSecond = prev_b_ann._EndSecond;
                                rec1._EndMillisecond = prev_b_ann._EndMillisecond;
                                rec1._EndUnix = prev_b_ann._EndUnix;


                                // add the itersection with the previous label
                                foreach (Activity act in prev_b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                {
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;

                                    rec1_rm._EndDate = b_ann._StartDate;
                                    rec1_rm._EndHour = b_ann._StartHour;
                                    rec1_rm._EndMinute = b_ann._StartMinute;
                                    rec1_rm._EndSecond = b_ann._StartSecond;
                                    rec1_rm._EndMillisecond = b_ann._StartMillisecond;
                                    rec1_rm._EndUnix = b_ann._StartUnix;

                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                rec1._EndDate = b_ann._StartDate;
                                rec1._EndHour = b_ann._StartHour;
                                rec1._EndMinute = b_ann._StartMinute;
                                rec1._EndSecond = b_ann._StartSecond;
                                rec1._EndMillisecond = b_ann._StartMillisecond;
                                rec1._EndUnix = b_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                                  #endregion

                            #region add record 2

                            //----------- add record 2 -------------------
                            if (end1 < end2)
                            {

                                if (end1 > start2)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    rec2._StartDate = b_ann._StartDate;
                                    rec2._StartHour = b_ann._StartHour;
                                    rec2._StartMinute = b_ann._StartMinute;
                                    rec2._StartSecond = b_ann._StartSecond;
                                    rec2._StartMillisecond = b_ann._StartMillisecond;
                                    rec2._StartUnix = b_ann._StartUnix;

                                    tempOutput.Add(rec2);


                                    //----------- create "last" record -> open label -------------------
                                    //last_ann = b_ann.copy();

                                    //b_ann._StartHour = a_ann._EndHour;
                                    //b_ann._StartMinute = a_ann._EndMinute;
                                    //b_ann._StartSecond = a_ann._EndSecond;
                                    //b_ann._StartMillisecond = a_ann._EndMillisecond;
                                    //b_ann._StartUnix = a_ann._EndUnix;

                                    bData[bCounter]._StartDate = a_ann._EndDate;
                                    bData[bCounter]._StartHour = a_ann._EndHour;
                                    bData[bCounter]._StartMinute = a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = a_ann._EndUnix;
                                }

                                //------- increase counters -----------------
                                //prev_a_ann = a_ann;    //prev_a_ann=(Annotation)aData[aCounter]
                                prev_a_ann = (Annotation)aData[aCounter];
                                
                                aCounter++;
                                //bCounter++;

                               

                            }
                            else if (end1 > end2)
                            {
                                //Annotation rec2 = b_ann.copy();
                                // add the itersection with the a_ann label
                                //rec2.Activities.Clear();
                                //rec2.Activities.Add(new Activity(a_ann.Activities[0]._Name, a_ann.Activities[0]._Category));
                                //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                if (end2 > start1)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    rec2._StartDate = b_ann._StartDate;
                                    rec2._StartHour = b_ann._StartHour;
                                    rec2._StartMinute = b_ann._StartMinute;
                                    rec2._StartSecond = b_ann._StartSecond;
                                    rec2._StartMillisecond = b_ann._StartMillisecond;
                                    rec2._StartUnix = b_ann._StartUnix;

                                    rec2._EndDate = b_ann._EndDate;
                                    rec2._EndHour = b_ann._EndHour;
                                    rec2._EndMinute = b_ann._EndMinute;
                                    rec2._EndSecond = b_ann._EndSecond;
                                    rec2._EndMillisecond = b_ann._EndMillisecond;
                                    rec2._EndUnix = b_ann._EndUnix;


                                    tempOutput.Add(rec2);


                                    //----------- create "last" record -> open label -------------------
                                    // a_ann._StartHour = b_ann._EndHour;
                                    // a_ann._StartMinute = b_ann._EndMinute;
                                    // a_ann._StartSecond = b_ann._EndSecond;
                                    // a_ann._StartMillisecond = b_ann._EndMillisecond;
                                    // a_ann._StartUnix = b_ann._EndUnix;

                                    aData[aCounter]._StartDate = b_ann._EndDate;
                                    aData[aCounter]._StartHour = b_ann._EndHour;
                                    aData[aCounter]._StartMinute = b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = b_ann._EndUnix;
                                }

                                //------- increase counters -----------------
                                //prev_b_ann = b_ann; 
                                prev_b_ann = (Annotation)bData[bCounter];
                                
                                //aCounter++;
                                bCounter++;

                                
                               

                            }

                            #endregion


                        }
                        else if (start1 > start2)
                        {


                            #region add record 1

                            //------------ add record one ------------------
                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            // add the intersection with the prevoius label
                            if (start2 < prev_a_ann._EndUnix)
                            {
                                rec1._EndDate = prev_a_ann._EndDate;
                                rec1._EndHour = prev_a_ann._EndHour;
                                rec1._EndMinute = prev_a_ann._EndMinute;
                                rec1._EndSecond = prev_a_ann._EndSecond;
                                rec1._EndMillisecond = prev_a_ann._EndMillisecond;
                                rec1._EndUnix = prev_a_ann._EndUnix;

                                
                                // add the intersection with the previous label
                                foreach (Activity act in prev_a_ann.Activities)
                                { rec1.Activities.Add(act); }

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                tempOutput.Add(rec1);



                                //check if there is a segment remaining to be synchronized
                                if (prev_a_ann._EndUnix < a_ann._StartUnix)
                                {
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    rec1_rm._EndDate = a_ann._StartDate;
                                    rec1_rm._EndHour = a_ann._StartHour;
                                    rec1_rm._EndMinute = a_ann._StartMinute;
                                    rec1_rm._EndSecond = a_ann._StartSecond;
                                    rec1_rm._EndMillisecond = a_ann._StartMillisecond;
                                    rec1_rm._EndUnix = a_ann._StartUnix;

                                    // add none, in order
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the b labels in order
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }


                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                // add none, check order
                                rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                rec1._EndDate = a_ann._StartDate;
                                rec1._EndHour = a_ann._StartHour;
                                rec1._EndMinute = a_ann._StartMinute;
                                rec1._EndSecond = a_ann._StartSecond;
                                rec1._EndMillisecond = a_ann._StartMillisecond;
                                rec1._EndUnix = a_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion


                            #region add record 2

                            //----------- add record 2 -------------------
                            if (end1 < end2)
                            {

                                if (end1 > start2)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    tempOutput.Add(rec2);


                                    //----------- create "last" record -> open label -------------------
                                    //last_ann = b_ann.copy();

                                    //b_ann._StartHour = a_ann._EndHour;
                                    //b_ann._StartMinute = a_ann._EndMinute;
                                    //b_ann._StartSecond = a_ann._EndSecond;
                                    //b_ann._StartMillisecond = a_ann._EndMillisecond;
                                    //b_ann._StartUnix = a_ann._EndUnix;

                                    bData[bCounter]._StartDate = a_ann._EndDate;
                                    bData[bCounter]._StartHour = a_ann._EndHour;
                                    bData[bCounter]._StartMinute = a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = a_ann._EndUnix;
                                }

                                //------- increase counters -----------------
                                //prev_a_ann = a_ann;    //prev_a_ann=(Annotation)aData[aCounter]
                                prev_a_ann = (Annotation)aData[aCounter];

                                aCounter++;
                                //bCounter++;

                               

                            }
                            else if (end1 > end2)
                            {
                                //Annotation rec2 = b_ann.copy();
                                // add the itersection with the a_ann label
                                //rec2.Activities.Clear();
                                //rec2.Activities.Add(new Activity(a_ann.Activities[0]._Name, a_ann.Activities[0]._Category));
                                //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                if (end2 > start1)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    rec2._EndDate = b_ann._EndDate;
                                    rec2._EndHour = b_ann._EndHour;
                                    rec2._EndMinute = b_ann._EndMinute;
                                    rec2._EndSecond = b_ann._EndSecond;
                                    rec2._EndMillisecond = b_ann._EndMillisecond;
                                    rec2._EndUnix = b_ann._EndUnix;


                                    tempOutput.Add(rec2);



                                    //----------- create "last" record -> open label -------------------
                                    // a_ann._StartHour = b_ann._EndHour;
                                    // a_ann._StartMinute = b_ann._EndMinute;
                                    // a_ann._StartSecond = b_ann._EndSecond;
                                    // a_ann._StartMillisecond = b_ann._EndMillisecond;
                                    // a_ann._StartUnix = b_ann._EndUnix;

                                    aData[aCounter]._StartDate = b_ann._EndDate;
                                    aData[aCounter]._StartHour = b_ann._EndHour;
                                    aData[aCounter]._StartMinute = b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = b_ann._EndUnix;

                                }


                                //------- increase counters -----------------
                                //prev_b_ann = b_ann; //prev_b_ann=(Annotation)bData[bCounter]
                                prev_b_ann = (Annotation)bData[bCounter];

                                //aCounter++;
                                bCounter++;


                            }

                            #endregion


                        }


                        #endregion


                    }

                   
                }
            }

            output.annotations.Clear();

            //copy results back to hte data field of the output Annotation object
            foreach (Annotation obj in tempOutput)
            { output.annotations.Add(obj); }


            return output;
            
        }
       */
        #endregion old merge code



        public Session Merge(Session session_input)
        {
            Session a = this.copy();
            Session b = session_input.copy();

            AnnotationList aData = a.annotations;
            AnnotationList bData = b.annotations;

            Session output = this.copy();
            AnnotationList tempOutput = new AnnotationList();


            int aCounter = 0;
            int bCounter = 0;

            string unknown_label = "unknown";


            Annotation a_ann = null;
            Annotation b_ann = null;

            Annotation prev_a_ann = null;
            Annotation prev_b_ann = null;


            #region initialize previous annotations



            if (aData.Count > 0)
            {
                prev_a_ann = (Annotation)aData[0].copy();
                prev_a_ann._StartUnix = 0;
                prev_a_ann._EndUnix = 0;
            }

            if (bData.Count > 0)
            {
                prev_b_ann = (Annotation)bData[0].copy();
                prev_b_ann._StartUnix = 0;
                prev_b_ann._EndUnix = 0;
            }

            #endregion



            #region loop all the annotations until the shortest list finishes

            while ((aCounter < aData.Count && bCounter < bData.Count) &&
                    (aData.Count > 0 && bData.Count > 0))
            {
                a_ann = ((Annotation)aData[aCounter]).copy();
                b_ann = ((Annotation)bData[bCounter]).copy();


                double start1 = a_ann._StartUnix;
                double start2 = b_ann._StartUnix;

                double end1 = a_ann._EndUnix;
                double end2 = b_ann._EndUnix;




                //no intersection so add the first annotation
                if (end1 <= start2 || end2 <= start1)
                {

                    #region code
                    //check if annotation a happens first
                    if (a_ann._StartUnix < b_ann._StartUnix)
                    {


                        #region add record 1 ==> start1 < start2, Case 1
                        //------------ add record one ------------------

                        // the label overlaps since the begining
                        if (start1 >= prev_b_ann._StartUnix)
                        {

                            #region

                            Annotation rec1 = a_ann.copy();

                            // add the intersection with the previous label
                            if (start1 < prev_b_ann._EndUnix)
                            {
                                // add the itersection with the previous label
                                foreach (Activity act in prev_b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                if (prev_b_ann._EndUnix < end1)
                                {
                                    rec1._EndDate = prev_b_ann._EndDate;
                                    rec1._EndHour = prev_b_ann._EndHour;
                                    rec1._EndMinute = prev_b_ann._EndMinute;
                                    rec1._EndSecond = prev_b_ann._EndSecond;
                                    rec1._EndMillisecond = prev_b_ann._EndMillisecond;
                                    rec1._EndUnix = prev_b_ann._EndUnix;
                                }


                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                //if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                if (prev_b_ann._EndUnix < end1)
                                {
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;


                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    aData[aCounter]._StartDate = prev_b_ann._EndDate;
                                    aData[aCounter]._StartHour = prev_b_ann._EndHour;
                                    aData[aCounter]._StartMinute = prev_b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = prev_b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = prev_b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = prev_b_ann._EndUnix;

                                    #endregion

                                }

                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                tempOutput.Add(rec1);

                            }


                            #endregion


                        }
                        else   //(start1 < prev_b_ann._StartUnix)
                        {

                            #region

                            // case starts are different 
                            Annotation rec1 = a_ann.copy();

                            //the segment is not overlapping with the first part of the prev_label, add unknown_label
                            //*** I need to check if it is not necessary to come back another register back
                            //*** to check for overlaps 
                            rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                            if (end1 > prev_b_ann._StartUnix)
                            {
                                rec1._EndDate = prev_b_ann._StartDate;
                                rec1._EndHour = prev_b_ann._StartHour;
                                rec1._EndMinute = prev_b_ann._StartMinute;
                                rec1._EndSecond = prev_b_ann._StartSecond;
                                rec1._EndMillisecond = prev_b_ann._StartMillisecond;
                                rec1._EndUnix = prev_b_ann._StartUnix;
                            }

                            tempOutput.Add(rec1);


                            if (end1 > prev_b_ann._StartUnix)
                            {
                                // Now add the segment intersecting with previous_b_label
                                Annotation rec2 = a_ann.copy();

                                // add the intersection with the previous label
                                if (end1 <= prev_b_ann._EndUnix)
                                {

                                    rec2._StartDate = prev_b_ann._StartDate;
                                    rec2._StartHour = prev_b_ann._StartHour;
                                    rec2._StartMinute = prev_b_ann._StartMinute;
                                    rec2._StartSecond = prev_b_ann._StartSecond;
                                    rec2._StartMillisecond = prev_b_ann._StartMillisecond;
                                    rec2._StartUnix = prev_b_ann._StartUnix;


                                    // add the itersection with the previous label
                                    foreach (Activity act in prev_b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    tempOutput.Add(rec2);

                                    #region update last record

                                    aData[aCounter]._StartDate = prev_b_ann._StartDate;
                                    aData[aCounter]._StartHour = prev_b_ann._StartHour;
                                    aData[aCounter]._StartMinute = prev_b_ann._StartMinute;
                                    aData[aCounter]._StartSecond = prev_b_ann._StartSecond;
                                    aData[aCounter]._StartMillisecond = prev_b_ann._StartMillisecond;
                                    aData[aCounter]._StartUnix = prev_b_ann._StartUnix;

                                    #endregion


                                }
                                else if (end1 > prev_b_ann._EndUnix)
                                {
                                    rec2._StartDate = prev_b_ann._StartDate;
                                    rec2._StartHour = prev_b_ann._StartHour;
                                    rec2._StartMinute = prev_b_ann._StartMinute;
                                    rec2._StartSecond = prev_b_ann._StartSecond;
                                    rec2._StartMillisecond = prev_b_ann._StartMillisecond;
                                    rec2._StartUnix = prev_b_ann._StartUnix;

                                    rec2._EndDate = prev_b_ann._EndDate;
                                    rec2._EndHour = prev_b_ann._EndHour;
                                    rec2._EndMinute = prev_b_ann._EndMinute;
                                    rec2._EndSecond = prev_b_ann._EndSecond;
                                    rec2._EndMillisecond = prev_b_ann._EndMillisecond;
                                    rec2._EndUnix = prev_b_ann._EndUnix;


                                    // add the itersection with the previous label
                                    foreach (Activity act in prev_b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    tempOutput.Add(rec2);


                                    // add the remaining from a_label
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;


                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    aData[aCounter]._StartDate = prev_b_ann._EndDate;
                                    aData[aCounter]._StartHour = prev_b_ann._EndHour;
                                    aData[aCounter]._StartMinute = prev_b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = prev_b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = prev_b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = prev_b_ann._EndUnix;

                                    #endregion

                                }
                            }

                            #endregion


                        }

                        #endregion


                        //prev_a_ann = a_ann; 
                        prev_a_ann = (Annotation)aData[aCounter];
                        aCounter++;

                    }
                    else
                    {




                        #region add record 1 ==> start2 < start1, Case 1
                        //------------ add record one ------------------

                        // the label overlaps since the begining
                        if (start2 >= prev_a_ann._StartUnix)
                        {

                            #region

                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            // add the intersection with the previous label
                            if (start2 < prev_a_ann._EndUnix)
                            {
                                // add the itersection with the previous label
                                foreach (Activity act in prev_a_ann.Activities)
                                { rec1.Activities.Add(act); }

                                // add the label activities
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                if (prev_a_ann._EndUnix < end2)
                                {
                                    rec1._EndDate = prev_a_ann._EndDate;
                                    rec1._EndHour = prev_a_ann._EndHour;
                                    rec1._EndMinute = prev_a_ann._EndMinute;
                                    rec1._EndSecond = prev_a_ann._EndSecond;
                                    rec1._EndMillisecond = prev_a_ann._EndMillisecond;
                                    rec1._EndUnix = prev_a_ann._EndUnix;
                                }


                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                //if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                if (prev_a_ann._EndUnix < end2)
                                {
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    // indicate no intersection with previous label
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }


                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    bData[bCounter]._StartDate = prev_a_ann._EndDate;
                                    bData[bCounter]._StartHour = prev_a_ann._EndHour;
                                    bData[bCounter]._StartMinute = prev_a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = prev_a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = prev_a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = prev_a_ann._EndUnix;

                                    #endregion

                                }

                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                // indicate no intersection with previous label
                                rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                // add the label activities
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                tempOutput.Add(rec1);

                            }


                            #endregion


                        }
                        else   //(start2 < prev_a_ann._StartUnix)
                        {

                            #region

                            // case starts are different 
                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            //the segment is not overlapping with the first part of the prev_label, add unknown_label
                            //*** I need to check if it is not necessary to come back another register back
                            //*** to check for overlaps 
                            rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                            // add the label activities
                            foreach (Activity act in b_ann.Activities)
                            { rec1.Activities.Add(act); }

                            if (end2 > prev_a_ann._StartUnix)
                            {
                                rec1._EndDate = prev_a_ann._StartDate;
                                rec1._EndHour = prev_a_ann._StartHour;
                                rec1._EndMinute = prev_a_ann._StartMinute;
                                rec1._EndSecond = prev_a_ann._StartSecond;
                                rec1._EndMillisecond = prev_a_ann._StartMillisecond;
                                rec1._EndUnix = prev_a_ann._StartUnix;
                            }


                            tempOutput.Add(rec1);



                            if (end2 > prev_a_ann._StartUnix)
                            {

                                // Add the segment intersecting with previous_b_label
                                Annotation rec2 = b_ann.copy();
                                rec2.Activities.Clear();


                                // add the intersection with the previous label
                                if (end2 <= prev_a_ann._EndUnix)
                                {

                                    rec2._StartDate = prev_a_ann._StartDate;
                                    rec2._StartHour = prev_a_ann._StartHour;
                                    rec2._StartMinute = prev_a_ann._StartMinute;
                                    rec2._StartSecond = prev_a_ann._StartSecond;
                                    rec2._StartMillisecond = prev_a_ann._StartMillisecond;
                                    rec2._StartUnix = prev_a_ann._StartUnix;


                                    // add the intersection with the previous label
                                    foreach (Activity act in prev_a_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }


                                    tempOutput.Add(rec2);


                                    #region update last record

                                    bData[bCounter]._StartDate = prev_a_ann._StartDate;
                                    bData[bCounter]._StartHour = prev_a_ann._StartHour;
                                    bData[bCounter]._StartMinute = prev_a_ann._StartMinute;
                                    bData[bCounter]._StartSecond = prev_a_ann._StartSecond;
                                    bData[bCounter]._StartMillisecond = prev_a_ann._StartMillisecond;
                                    bData[bCounter]._StartUnix = prev_a_ann._StartUnix;

                                    #endregion


                                }
                                else //(end2 > prev_a_ann._EndUnix)
                                {
                                    rec2._StartDate = prev_a_ann._StartDate;
                                    rec2._StartHour = prev_a_ann._StartHour;
                                    rec2._StartMinute = prev_a_ann._StartMinute;
                                    rec2._StartSecond = prev_a_ann._StartSecond;
                                    rec2._StartMillisecond = prev_a_ann._StartMillisecond;
                                    rec2._StartUnix = prev_a_ann._StartUnix;

                                    rec2._EndDate = prev_a_ann._EndDate;
                                    rec2._EndHour = prev_a_ann._EndHour;
                                    rec2._EndMinute = prev_a_ann._EndMinute;
                                    rec2._EndSecond = prev_a_ann._EndSecond;
                                    rec2._EndMillisecond = prev_a_ann._EndMillisecond;
                                    rec2._EndUnix = prev_a_ann._EndUnix;


                                    // add the intersection with the previous label
                                    foreach (Activity act in prev_a_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }


                                    tempOutput.Add(rec2);


                                    // add the remaining from a_label
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    // indicate no intersection with previous label
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the label activities
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }

                                    tempOutput.Add(rec1_rm);


                                    #region update last record

                                    bData[bCounter]._StartDate = prev_a_ann._EndDate;
                                    bData[bCounter]._StartHour = prev_a_ann._EndHour;
                                    bData[bCounter]._StartMinute = prev_a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = prev_a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = prev_a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = prev_a_ann._EndUnix;

                                    #endregion

                                }

                            }

                            #endregion


                        }

                        #endregion

                        //  prev_b_ann = b_ann;  
                        prev_b_ann = (Annotation)bData[bCounter];
                        bCounter++;



                    }

                    #endregion


                }
                //else there is intersection
                else
                {



                    // perfect alignment
                    if (start1 == start2 && end1 == end2)
                    {
                        #region code

                        Annotation rec1 = a_ann.copy();

                        // add the itersection with the b_ann label
                        foreach (Activity act in b_ann.Activities)
                        { rec1.Activities.Add(act); }

                        tempOutput.Add(rec1);

                        //prev_a_ann = a_ann; //   prev_a_ann=(Annotation)aData[aCounter]
                        //prev_b_ann = b_ann; //   prev_b_ann=(Annotation)bData[bCounter]

                        prev_a_ann = (Annotation)aData[aCounter];
                        prev_b_ann = (Annotation)bData[bCounter];

                        aCounter++;
                        bCounter++;


                        #endregion

                    }
                    //if (start1 == end1 && start2 != end2) //use start2 and end2 as constraints
                    else if (start1 == start2 && end1 != end2)
                    {

                        #region code




                        if (end1 < end2)
                        {
                            //------------ add record one ------------------
                            Annotation rec1 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec1.Activities.Add(act); }

                            tempOutput.Add(rec1);



                            bData[bCounter]._StartDate = a_ann._EndDate;

                            bData[bCounter]._StartHour = a_ann._EndHour;
                            bData[bCounter]._StartMinute = a_ann._EndMinute;
                            bData[bCounter]._StartSecond = a_ann._EndSecond;
                            bData[bCounter]._StartMillisecond = a_ann._EndMillisecond;
                            bData[bCounter]._StartUnix = a_ann._EndUnix;


                            //------- increase counters -----------------
                            //prev_a_ann = a_ann; 
                            prev_a_ann = (Annotation)aData[aCounter];

                            aCounter++;


                        }
                        else if (end1 > end2)
                        {
                            //------------ add record one ------------------


                            Annotation rec1 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec1.Activities.Add(act); }

                            rec1._EndDate = b_ann._EndDate;
                            rec1._EndHour = b_ann._EndHour;
                            rec1._EndMinute = b_ann._EndMinute;
                            rec1._EndSecond = b_ann._EndSecond;
                            rec1._EndMillisecond = b_ann._EndMillisecond;
                            rec1._EndUnix = b_ann._EndUnix;


                            tempOutput.Add(rec1);


                            //----------- create "last" record -> open label -------------------

                            aData[aCounter]._StartDate = b_ann._EndDate;
                            aData[aCounter]._StartHour = b_ann._EndHour;
                            aData[aCounter]._StartMinute = b_ann._EndMinute;
                            aData[aCounter]._StartSecond = b_ann._EndSecond;
                            aData[aCounter]._StartMillisecond = b_ann._EndMillisecond;
                            aData[aCounter]._StartUnix = b_ann._EndUnix;


                            //------- increase counters -----------------

                            //prev_b_ann = b_ann;   
                            prev_b_ann = (Annotation)bData[bCounter];


                            bCounter++;
                        }

                        #endregion


                    }
                    // else if (start1 != end1 && start2 == end2)  //use start1 and end1 as constraints
                    else if (start1 != start2 && end1 == end2)  //use start1 and end1 as constraints
                    {

                        #region Code


                        if (start1 < start2)
                        {

                            #region add record 1 ==> start1< start2, Case 1

                            //------------ add record one ------------------
                            Annotation rec1 = a_ann.copy();

                            // add the intersection with the prevoius label
                            if (start1 < prev_b_ann._EndUnix)
                            {

                                rec1._EndDate = prev_b_ann._EndDate;

                                rec1._EndHour = prev_b_ann._EndHour;
                                rec1._EndMinute = prev_b_ann._EndMinute;
                                rec1._EndSecond = prev_b_ann._EndSecond;
                                rec1._EndMillisecond = prev_b_ann._EndMillisecond;
                                rec1._EndUnix = prev_b_ann._EndUnix;


                                // add the itersection with the previous label
                                foreach (Activity act in prev_b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                {
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;

                                    rec1_rm._EndDate = b_ann._StartDate;
                                    rec1_rm._EndHour = b_ann._StartHour;
                                    rec1_rm._EndMinute = b_ann._StartMinute;
                                    rec1_rm._EndSecond = b_ann._StartSecond;
                                    rec1_rm._EndMillisecond = b_ann._StartMillisecond;
                                    rec1_rm._EndUnix = b_ann._StartUnix;

                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                rec1._EndDate = b_ann._StartDate;
                                rec1._EndHour = b_ann._StartHour;
                                rec1._EndMinute = b_ann._StartMinute;
                                rec1._EndSecond = b_ann._StartSecond;
                                rec1._EndMillisecond = b_ann._StartMillisecond;
                                rec1._EndUnix = b_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion


                            #region  add record two

                            //----------- add record 2 -------------------

                            Annotation rec2 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec2.Activities.Add(act); }

                            rec2._StartDate = b_ann._StartDate;
                            rec2._StartHour = b_ann._StartHour;
                            rec2._StartMinute = b_ann._StartMinute;
                            rec2._StartSecond = b_ann._StartSecond;
                            rec2._StartMillisecond = b_ann._StartMillisecond;
                            rec2._StartUnix = b_ann._StartUnix;

                            tempOutput.Add(rec2);

                            #endregion


                            #region update changes

                            aData[aCounter]._StartDate = b_ann._StartDate;
                            aData[aCounter]._StartHour = b_ann._StartHour;
                            aData[aCounter]._StartMinute = b_ann._StartMinute;
                            aData[aCounter]._StartSecond = b_ann._StartSecond;
                            aData[aCounter]._StartMillisecond = b_ann._StartMillisecond;
                            aData[aCounter]._StartUnix = b_ann._StartUnix;

                            #endregion

                        }
                        else if (start1 > start2)
                        {
                            #region add record 1 ==> start2 < start1, Case 1

                            //------------ add record one ------------------
                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            // add the intersection with the prevoius label
                            if (start2 < prev_a_ann._EndUnix)
                            {
                                rec1._EndDate = prev_a_ann._EndDate;
                                rec1._EndHour = prev_a_ann._EndHour;
                                rec1._EndMinute = prev_a_ann._EndMinute;
                                rec1._EndSecond = prev_a_ann._EndSecond;
                                rec1._EndMillisecond = prev_a_ann._EndMillisecond;
                                rec1._EndUnix = prev_a_ann._EndUnix;


                                // add the intersection with the previous label
                                foreach (Activity act in prev_a_ann.Activities)
                                { rec1.Activities.Add(act); }

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                tempOutput.Add(rec1);



                                //check if there is a segment remaining to be synchronized
                                if (prev_a_ann._EndUnix < a_ann._StartUnix)
                                {
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    rec1_rm._EndDate = a_ann._StartDate;
                                    rec1_rm._EndHour = a_ann._StartHour;
                                    rec1_rm._EndMinute = a_ann._StartMinute;
                                    rec1_rm._EndSecond = a_ann._StartSecond;
                                    rec1_rm._EndMillisecond = a_ann._StartMillisecond;
                                    rec1_rm._EndUnix = a_ann._StartUnix;

                                    // add none, check order
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the b labels in order
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }


                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                // add none, check order
                                rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                rec1._EndDate = a_ann._StartDate;
                                rec1._EndHour = a_ann._StartHour;
                                rec1._EndMinute = a_ann._StartMinute;
                                rec1._EndSecond = a_ann._StartSecond;
                                rec1._EndMillisecond = a_ann._StartMillisecond;
                                rec1._EndUnix = a_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion


                            #region  add record two

                            //----------- add record 2 -------------------

                            Annotation rec2 = a_ann.copy();

                            // add the itersection with the b_ann label
                            foreach (Activity act in b_ann.Activities)
                            { rec2.Activities.Add(act); }

                            tempOutput.Add(rec2);

                            #endregion


                            #region update changes

                            bData[bCounter]._StartDate = a_ann._StartDate;
                            bData[bCounter]._StartHour = a_ann._StartHour;
                            bData[bCounter]._StartMinute = a_ann._StartMinute;
                            bData[bCounter]._StartSecond = a_ann._StartSecond;
                            bData[bCounter]._StartMillisecond = a_ann._StartMillisecond;
                            bData[bCounter]._StartUnix = a_ann._StartUnix;

                            #endregion
                        }

                        //------- increase counters -----------------

                        //prev_a_ann = a_ann;     
                        //prev_b_ann = b_ann;    

                        prev_a_ann = (Annotation)aData[aCounter];
                        prev_b_ann = (Annotation)bData[bCounter];

                        aCounter++;
                        bCounter++;


                        #endregion


                    }
                    else if (start1 != start2 && end1 != end2)//use both start1 & end1, start2 & end2
                    {


                        #region code

                        if (start1 < start2)
                        {



                            #region add record 1

                            //------------ add record one ------------------
                            Annotation rec1 = a_ann.copy();

                            // add the intersection with the prevoius label
                            if (start1 < prev_b_ann._EndUnix)
                            {

                                rec1._EndDate = prev_b_ann._EndDate;

                                rec1._EndHour = prev_b_ann._EndHour;
                                rec1._EndMinute = prev_b_ann._EndMinute;
                                rec1._EndSecond = prev_b_ann._EndSecond;
                                rec1._EndMillisecond = prev_b_ann._EndMillisecond;
                                rec1._EndUnix = prev_b_ann._EndUnix;


                                // add the itersection with the previous label
                                foreach (Activity act in prev_b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                tempOutput.Add(rec1);


                                //check if there is a segment remaining to be synchronized
                                if (prev_b_ann._EndUnix < b_ann._StartUnix)
                                {
                                    Annotation rec1_rm = a_ann.copy();

                                    rec1_rm._StartDate = prev_b_ann._EndDate;
                                    rec1_rm._StartHour = prev_b_ann._EndHour;
                                    rec1_rm._StartMinute = prev_b_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_b_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_b_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_b_ann._EndUnix;

                                    rec1_rm._EndDate = b_ann._StartDate;
                                    rec1_rm._EndHour = b_ann._StartHour;
                                    rec1_rm._EndMinute = b_ann._StartMinute;
                                    rec1_rm._EndSecond = b_ann._StartSecond;
                                    rec1_rm._EndMillisecond = b_ann._StartMillisecond;
                                    rec1_rm._EndUnix = b_ann._StartUnix;

                                    rec1_rm.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                rec1.Activities.Add(new Activity(unknown_label, b_ann.Activities[0]._Category));

                                rec1._EndDate = b_ann._StartDate;
                                rec1._EndHour = b_ann._StartHour;
                                rec1._EndMinute = b_ann._StartMinute;
                                rec1._EndSecond = b_ann._StartSecond;
                                rec1._EndMillisecond = b_ann._StartMillisecond;
                                rec1._EndUnix = b_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion

                            #region add record 2

                            //----------- add record 2 -------------------
                            if (end1 < end2)
                            {

                                if (end1 > start2)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    rec2._StartDate = b_ann._StartDate;
                                    rec2._StartHour = b_ann._StartHour;
                                    rec2._StartMinute = b_ann._StartMinute;
                                    rec2._StartSecond = b_ann._StartSecond;
                                    rec2._StartMillisecond = b_ann._StartMillisecond;
                                    rec2._StartUnix = b_ann._StartUnix;

                                    tempOutput.Add(rec2);


                                    //----------- create "last" record -> open label -------------------
                                    //last_ann = b_ann.copy();

                                    //b_ann._StartHour = a_ann._EndHour;
                                    //b_ann._StartMinute = a_ann._EndMinute;
                                    //b_ann._StartSecond = a_ann._EndSecond;
                                    //b_ann._StartMillisecond = a_ann._EndMillisecond;
                                    //b_ann._StartUnix = a_ann._EndUnix;

                                    bData[bCounter]._StartDate = a_ann._EndDate;
                                    bData[bCounter]._StartHour = a_ann._EndHour;
                                    bData[bCounter]._StartMinute = a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = a_ann._EndUnix;
                                }

                                //------- increase counters -----------------
                                //prev_a_ann = a_ann;    //prev_a_ann=(Annotation)aData[aCounter]
                                prev_a_ann = (Annotation)aData[aCounter];

                                aCounter++;
                                //bCounter++;



                            }
                            else if (end1 > end2)
                            {
                                //Annotation rec2 = b_ann.copy();
                                // add the itersection with the a_ann label
                                //rec2.Activities.Clear();
                                //rec2.Activities.Add(new Activity(a_ann.Activities[0]._Name, a_ann.Activities[0]._Category));
                                //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                if (end2 > start1)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    rec2._StartDate = b_ann._StartDate;
                                    rec2._StartHour = b_ann._StartHour;
                                    rec2._StartMinute = b_ann._StartMinute;
                                    rec2._StartSecond = b_ann._StartSecond;
                                    rec2._StartMillisecond = b_ann._StartMillisecond;
                                    rec2._StartUnix = b_ann._StartUnix;

                                    rec2._EndDate = b_ann._EndDate;
                                    rec2._EndHour = b_ann._EndHour;
                                    rec2._EndMinute = b_ann._EndMinute;
                                    rec2._EndSecond = b_ann._EndSecond;
                                    rec2._EndMillisecond = b_ann._EndMillisecond;
                                    rec2._EndUnix = b_ann._EndUnix;


                                    tempOutput.Add(rec2);


                                    //----------- create "last" record -> open label -------------------
                                    // a_ann._StartHour = b_ann._EndHour;
                                    // a_ann._StartMinute = b_ann._EndMinute;
                                    // a_ann._StartSecond = b_ann._EndSecond;
                                    // a_ann._StartMillisecond = b_ann._EndMillisecond;
                                    // a_ann._StartUnix = b_ann._EndUnix;

                                    aData[aCounter]._StartDate = b_ann._EndDate;
                                    aData[aCounter]._StartHour = b_ann._EndHour;
                                    aData[aCounter]._StartMinute = b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = b_ann._EndUnix;
                                }

                                //------- increase counters -----------------
                                //prev_b_ann = b_ann; 
                                prev_b_ann = (Annotation)bData[bCounter];

                                //aCounter++;
                                bCounter++;




                            }

                            #endregion


                        }
                        else if (start1 > start2)
                        {


                            #region add record 1

                            //------------ add record one ------------------
                            Annotation rec1 = b_ann.copy();
                            rec1.Activities.Clear();

                            // add the intersection with the prevoius label
                            if (start2 < prev_a_ann._EndUnix)
                            {
                                rec1._EndDate = prev_a_ann._EndDate;
                                rec1._EndHour = prev_a_ann._EndHour;
                                rec1._EndMinute = prev_a_ann._EndMinute;
                                rec1._EndSecond = prev_a_ann._EndSecond;
                                rec1._EndMillisecond = prev_a_ann._EndMillisecond;
                                rec1._EndUnix = prev_a_ann._EndUnix;


                                // add the intersection with the previous label
                                foreach (Activity act in prev_a_ann.Activities)
                                { rec1.Activities.Add(act); }

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }


                                tempOutput.Add(rec1);



                                //check if there is a segment remaining to be synchronized
                                if (prev_a_ann._EndUnix < a_ann._StartUnix)
                                {
                                    Annotation rec1_rm = b_ann.copy();
                                    rec1_rm.Activities.Clear();

                                    rec1_rm._StartDate = prev_a_ann._EndDate;
                                    rec1_rm._StartHour = prev_a_ann._EndHour;
                                    rec1_rm._StartMinute = prev_a_ann._EndMinute;
                                    rec1_rm._StartSecond = prev_a_ann._EndSecond;
                                    rec1_rm._StartMillisecond = prev_a_ann._EndMillisecond;
                                    rec1_rm._StartUnix = prev_a_ann._EndUnix;

                                    rec1_rm._EndDate = a_ann._StartDate;
                                    rec1_rm._EndHour = a_ann._StartHour;
                                    rec1_rm._EndMinute = a_ann._StartMinute;
                                    rec1_rm._EndSecond = a_ann._StartSecond;
                                    rec1_rm._EndMillisecond = a_ann._StartMillisecond;
                                    rec1_rm._EndUnix = a_ann._StartUnix;

                                    // add none, in order
                                    rec1_rm.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                    // add the b labels in order
                                    foreach (Activity act in b_ann.Activities)
                                    { rec1_rm.Activities.Add(act); }


                                    tempOutput.Add(rec1_rm);

                                }


                            }
                            else // the segment is not overlapping with prev_label, add unknown_label
                            {
                                // add none, check order
                                rec1.Activities.Add(new Activity(unknown_label, a_ann.Activities[0]._Category));

                                // add the b labels in order
                                foreach (Activity act in b_ann.Activities)
                                { rec1.Activities.Add(act); }

                                rec1._EndDate = a_ann._StartDate;
                                rec1._EndHour = a_ann._StartHour;
                                rec1._EndMinute = a_ann._StartMinute;
                                rec1._EndSecond = a_ann._StartSecond;
                                rec1._EndMillisecond = a_ann._StartMillisecond;
                                rec1._EndUnix = a_ann._StartUnix;

                                tempOutput.Add(rec1);
                            }

                            #endregion


                            #region add record 2

                            //----------- add record 2 -------------------
                            if (end1 < end2)
                            {

                                if (end1 > start2)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    tempOutput.Add(rec2);


                                    //----------- create "last" record -> open label -------------------
                                    //last_ann = b_ann.copy();

                                    //b_ann._StartHour = a_ann._EndHour;
                                    //b_ann._StartMinute = a_ann._EndMinute;
                                    //b_ann._StartSecond = a_ann._EndSecond;
                                    //b_ann._StartMillisecond = a_ann._EndMillisecond;
                                    //b_ann._StartUnix = a_ann._EndUnix;

                                    bData[bCounter]._StartDate = a_ann._EndDate;
                                    bData[bCounter]._StartHour = a_ann._EndHour;
                                    bData[bCounter]._StartMinute = a_ann._EndMinute;
                                    bData[bCounter]._StartSecond = a_ann._EndSecond;
                                    bData[bCounter]._StartMillisecond = a_ann._EndMillisecond;
                                    bData[bCounter]._StartUnix = a_ann._EndUnix;
                                }

                                //------- increase counters -----------------
                                //prev_a_ann = a_ann;    //prev_a_ann=(Annotation)aData[aCounter]
                                prev_a_ann = (Annotation)aData[aCounter];

                                aCounter++;
                                //bCounter++;



                            }
                            else if (end1 > end2)
                            {
                                //Annotation rec2 = b_ann.copy();
                                // add the itersection with the a_ann label
                                //rec2.Activities.Clear();
                                //rec2.Activities.Add(new Activity(a_ann.Activities[0]._Name, a_ann.Activities[0]._Category));
                                //rec2.Activities.Add(new Activity(b_ann.Activities[0]._Name, b_ann.Activities[0]._Category));

                                if (end2 > start1)
                                {
                                    Annotation rec2 = a_ann.copy();

                                    // add the itersection with the b_ann label
                                    foreach (Activity act in b_ann.Activities)
                                    { rec2.Activities.Add(act); }

                                    rec2._EndDate = b_ann._EndDate;
                                    rec2._EndHour = b_ann._EndHour;
                                    rec2._EndMinute = b_ann._EndMinute;
                                    rec2._EndSecond = b_ann._EndSecond;
                                    rec2._EndMillisecond = b_ann._EndMillisecond;
                                    rec2._EndUnix = b_ann._EndUnix;


                                    tempOutput.Add(rec2);



                                    //----------- create "last" record -> open label -------------------
                                    // a_ann._StartHour = b_ann._EndHour;
                                    // a_ann._StartMinute = b_ann._EndMinute;
                                    // a_ann._StartSecond = b_ann._EndSecond;
                                    // a_ann._StartMillisecond = b_ann._EndMillisecond;
                                    // a_ann._StartUnix = b_ann._EndUnix;

                                    aData[aCounter]._StartDate = b_ann._EndDate;
                                    aData[aCounter]._StartHour = b_ann._EndHour;
                                    aData[aCounter]._StartMinute = b_ann._EndMinute;
                                    aData[aCounter]._StartSecond = b_ann._EndSecond;
                                    aData[aCounter]._StartMillisecond = b_ann._EndMillisecond;
                                    aData[aCounter]._StartUnix = b_ann._EndUnix;

                                }


                                //------- increase counters -----------------
                                //prev_b_ann = b_ann; //prev_b_ann=(Annotation)bData[bCounter]
                                prev_b_ann = (Annotation)bData[bCounter];

                                //aCounter++;
                                bCounter++;


                            }

                            #endregion


                        }


                        #endregion


                    }


                }
            }

            #endregion loop all the annotations until one of the list finishes

            #region loop all the remaining annotations


            if (aCounter >= aData.Count && bCounter < bData.Count)
            {

                for (int b_elem = bCounter; b_elem < bData.Count; b_elem++)
                {
                    Annotation temp_rec = bData[b_elem].copy();
                    temp_rec.Activities.Clear();

                    temp_rec.Activities.Add(new Activity(unknown_label, aData[0].Activities[0]._Category));
                    temp_rec.Activities.Add(bData[b_elem].Activities[0]);

                    tempOutput.Add(temp_rec);

                }
            }
            else if (aCounter < aData.Count && bCounter >= bData.Count)
            {
                for (int a_elem = aCounter; a_elem < aData.Count; a_elem++)
                {
                    tempOutput.Add(aData[a_elem]);
                    tempOutput[tempOutput.Count - 1].Activities.Add(new Activity(unknown_label, bData[0].Activities[0]._Category));

                }
            }


            #endregion


            output.annotations.Clear();

            //copy results back to hte data field of the output Annotation object
            foreach (Annotation obj in tempOutput)
            { output.annotations.Add(obj); }


            return output;

        }
       

        #endregion


        // performs a deep copy
        public Session copy()
        {

            Session s = new Session();
          
            // copy all the categories          
             foreach (ActivityList cat in activityLists)
              s.activityLists.Add(cat);

            // copy all the annotations
            foreach( Annotation ann in annotations)
             s.annotations.Add(ann);
            
            s._Subject = subject;
            s._Observer = observer;
            s._Location = location;
            s._Notes = notes;
            s._DataDirectory = dataDirectory;

            
            return s;


        }

       


    }
}
