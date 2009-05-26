using System;
using System.Collections.Generic;
using System.Collections;
using System.Text;
using System.IO;
using System.Text.RegularExpressions;

namespace WocketsWeka.Utils.DTs
{
    public class FilterList
    {
        ArrayList attributes = new ArrayList();
        ArrayList activities = new ArrayList();
        ArrayList wantedAttrs = new ArrayList();
        ArrayList wantedIndices = new ArrayList();
        StreamReader reader;
        StreamWriter writer;
        static String patternAttr = @"(RELATION|ATTRIBUTE)\s+(?<name>\b(\w+)\b)";
        static String patternActs = @"@ATTRIBUTE\s+activity\s+{";
        //construct regular expressions
        Regex mAttr = new Regex(patternAttr, RegexOptions.IgnoreCase);
        Regex mActs = new Regex(patternActs, RegexOptions.IgnoreCase);
        String temp;

        /*Filters a given list by activity and attributes
         * @input: the file to be read from
         * @activities: the activities (rows) wanted in the final file
         * @attributes: the attributes (columns) wanted in the final file
         * @output: creates filtered text file with crossection of activities
         *          and attributes described in input
         * */
        public void filter(String input,String output, String[] attrs, String[] acts)
        {
            reader = new StreamReader(input);
            writer = new StreamWriter(output);
            //cycle through wanted activities and add to string collection
            foreach (String i in acts)
            {
                activities.Add(i);
            }
            foreach (String i in attrs)
            {
                wantedAttrs.Add(i);
            }
            //read lines, adding all attrs to attr collection
            while ((temp = reader.ReadLine()) != null)
            {
                Match m1 = mAttr.Match(temp);
                Match m2 = mActs.Match(temp);
                //if the line is empty, write an empty line
                if (temp.Length == 0 ||
                        m1.Groups[1].ToString().Equals("RELATION", StringComparison.OrdinalIgnoreCase))
                {
                    writer.WriteLine(temp);
                }
                //if line is an attribute, but not an activity, add then write
                else if (m1.Success && !m2.Success)
                {
                    String tempString = m1.Groups["name"].ToString();
                    attributes.Add(tempString);
                    if (wantedAttrs.Contains(tempString))
                    {
                        writer.WriteLine(temp);
                        wantedIndices.Add(attributes.IndexOf(tempString));
                    }
                }
                //if this line is activities, only add activities wanted
                else if (m2.Success)
                {
                    String want = m2.Groups[0].ToString();
                    foreach (String str in acts)
                    {
                        if (str == acts[acts.Length - 1])
                        {
                            want = want + str + "}";
                        }
                        else
                        {
                            want = want + str + ",";
                        }
                    }
                    writer.Write(want);
                }
                //if this line is none of above, must be @DATA label or 
                //the actual data itself
                else
                {
                    //parse string up with comma as delimiter
                    char[] delim = { ',' };
                    String[] dataSet = temp.Split(delim);
                    if (dataSet.Length == 1) //means it's just @DATA
                    {
                        writer.Write(temp);
                    }
                    //means line is a series of numeric data, with label at end
                    //so check to see if label belongs to wanted activities
                    else if (activities.Contains(dataSet[dataSet.Length - 1]))
                    {
                        this.parseData(dataSet);
                    }
                }   //finished parsing data lines

            }   //finished reading file

            writer.Close();
            reader.Close();
        }

        private void parseData(String[] data)
        {
            foreach (int index in wantedIndices)
            {
                writer.Write(data[index] + ",");
            }
            writer.Write(data[data.Length - 1]);
            writer.WriteLine();
        }

        /* Takes as inputs an attribute name and (optionally) an array
         * of activity names. Returns a double array of the column of numeric values
         * for that attribute and (optionally) with that activity.
         * @input: name of file to be read from
         * @attr: name of attribute column wanted
         * @act: the activities wanted in the column (can be null if want all)
         * @output: double array of values for attribute column
         * */
        public double[] getAttrColumn(String input, String attr, String[] act)
        {
            String patternAttr = @"ATTRIBUTE\s+(?<name>\b(\w+)\b)";
            Regex mAttr = new Regex(patternAttr, RegexOptions.IgnoreCase);
            StreamReader reader = new StreamReader(input);
            char[] delim = { ',' };
            ArrayList actions;
            ArrayList result = new ArrayList();

            if (act != null)
            {
                actions = new ArrayList();
                foreach (String i in act)
                {
                    actions.Add(i);
                }
            }
            int counter = 0;
            Boolean matched = false;
            while ((temp = reader.ReadLine()) != null)
            {
                Match m = mAttr.Match(temp);
                String[] a = temp.Split(delim);
                if (m.Groups["name"].ToString() != attr && !matched)
                {
                    counter++;
                    continue;
                }
                else if (m.Success && !m.Groups["name"].ToString().Equals("activity", StringComparison.OrdinalIgnoreCase))
                {
                    matched = true;
                }
                else if (a.Length > 1 && !m.Groups["name"].ToString().Equals("activity", StringComparison.OrdinalIgnoreCase))
                {
                    result.Add(Double.Parse(a[counter - 1]));
                }
            }
            return (double[])result.ToArray(typeof(double));
        }


       public void replaceString(String file, String outfile, String output, String[] targets)
        {
            reader = new StreamReader(file);
            writer = new StreamWriter(outfile); //arbitrary output file

            while ((temp = reader.ReadLine()) != null)
            {
                Match m1 = mActs.Match(temp);
                Match m2 = mAttr.Match(temp);
                if (m1.Success) //activity line
                {
                    String result = temp;;   //already replaced one target if true
                    Boolean replaced = false;
                    foreach (String str in targets)
                    {
                        String pat = "[,{]" +str+ "[,}]";
                        Regex reg = new Regex(pat);
                        if (!replaced)  //first time replacing
                        {
                            String oldString = reg.Match(temp).ToString();
                            String newString = oldString.Replace(str,
output);
                            result = result.Replace(oldString, newString);
                            replaced = true;
                        }
                        else //already replaced
                        {
                            String oldString = reg.Match(temp).ToString();
                            String newString = oldString.Replace(str, "");
                            result = result.Replace(oldString, newString);
                        }
                    }
                    result = result.Replace(",,", ",");
                    result = result.Replace(",}", "}");
                    result = result.Replace("{,", "{");
                    writer.WriteLine(result);
                }
                else if ((temp.IndexOf("@")>=0) || temp.Length == 0) //just attr, no need to replace
                {
                    writer.WriteLine(temp);
                }
                else //data lines, need to replace
                {
                    String result = temp;
                    foreach (String str in targets)
                    {
                        String patt = "," + str;
                        Regex rege = new Regex(patt);
                        if (rege.Match(temp).Success)
                        {
                            String oldString = rege.Match(temp).ToString();
                            String newString = oldString.Replace(str,
output);
                            result = result.Replace(oldString, newString);
                        }
                    }
                    writer.WriteLine(result);
                }
            }
            writer.Close();
            reader.Close();
        }

    }
}
