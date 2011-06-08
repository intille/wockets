using System;
using System.Data;
using System.Linq;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace WocketsQuestionsAnswers
{
    public class CSVParser
    {
        public static void WriteCSV(DataTable dt, string filePath)
        {
            if (File.Exists(filePath))
            {
                try { File.Delete(filePath); }
                catch { Console.WriteLine("\nThe existing output file could not be deleted. It appears to be in use by another application."); }
            }
            StreamWriter sw = File.CreateText(filePath);
            try
            {
                StringBuilder rowToWrite = new StringBuilder();
                foreach (DataColumn dc in dt.Columns)
                {
                    if (dc.ColumnName.Contains(","))
                        rowToWrite.Append("'\"" + dc.ColumnName + "\"'");
                    else
                        rowToWrite.Append("'" + dc.ColumnName + "'");
                }
                rowToWrite.Replace("''", ",");
                rowToWrite.Replace("'", "");
                rowToWrite.Append("\r\n");
                if (rowToWrite.ToString().StartsWith("ID"))         // if first column label is "ID" Excel will give you an error
                    rowToWrite.Replace("ID", "id", 0, 2);           // changes "ID" to "id" to fix Excel bug
                sw.Write(rowToWrite);
                foreach (DataRow row in dt.Rows)
                {
                    rowToWrite = new StringBuilder();
                    for (int counter = 0; counter <= dt.Columns.Count - 1; counter++)
                    {
                        if (row[counter].ToString().Contains(","))
                            rowToWrite.Append("'\"" + row[counter] + "\"'");
                        else
                            rowToWrite.Append("'" + row[counter] + "'");
                    }
                    rowToWrite.Replace("''", ",");
                    rowToWrite.Replace("'", "");
                    rowToWrite.Append("\r\n");
                    sw.Write(rowToWrite);
                }
            }
            catch { }
            finally
            {
                sw.Close();
            }
        }

        public static DataTable LoadCSV(string fileName)
        {
            FileReader fr;
            String line;
            DataTable dt = new DataTable();
            if (File.Exists(fileName))
            {
                try
                {
                    fr = new FileReader(fileName);
                    fr.OpenFile();
                    line = fr.ReadLine();
                    if (line != null)
                    {
                        string[] lineParts = line.Split(new char[] { '\t', ',' });
                        foreach (string s in lineParts)
                            dt.Columns.Add(s);
                        line = fr.ReadLine();
                        while (line != null)
                        {
                            dt.Rows.Add();
                            int rowIndex = dt.Rows.Count - 1;
                            lineParts = line.Split(new char[] { '\t', ',' });
                            for (int i = 0; i < lineParts.Length; i++)
                                dt.Rows[rowIndex][i] = lineParts[i];
                            line = fr.ReadLine();
                        }
                    }
                    fr.CloseFile();
                }
                catch {  }
            }
            return dt;
        }
    }
}
