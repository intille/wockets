using System;
using System.Collections.Generic;
using System.Text;

namespace WocketsWeka.Utils
{
    public class Tokenizer
    {


        private string myString;
        private string[] myTokens;
        private int cToken;

        public Tokenizer(string str)
        {
            // Initialize the class.
            Tokenize(str);
        }

        public Tokenizer(string str, char delimiter)
        {
            // Initialize the class with a specified delimeter.
            Tokenize(str, delimiter);
        }

        public void Tokenize(string str)
        {
            char[] c = new char[1];			// This is the delimeter.

            myString = str;					// We setup the class' string.

            c[0] = ' ';						// Set the delimeter.
            myTokens = myString.Split(c);	// Split the string and put it
            // in myTokens.

            cToken = -1;					// Set the current token to -1.
        }

        public void Tokenize(string str, char delimiter)
        {
            char[] c = new char[1];			// This is the delimeter.

            myString = str;					// Setup the string...

            c[0] = delimiter;				// Set the delimeter (user specified).
            myTokens = myString.Split(c);	// Split the array into myTokens.

            cToken = -1;					// Set the current token to -1.
        }

        public string NextToken()
        {
            /*
             *	Basically if we still have more tokens, increase the index
             * and return the next token. Simple really. Otherwise return
             * an error code.
             */
            if (HasMoreTokens())
            {
                cToken++;
                return myTokens[cToken];
            }
            else
                return "-1";
        }

        public bool HasMoreTokens()
        {
            // Check to see if the current index is less than
            //		one less than final index.
            return (cToken < myTokens.Length - 1);
        }

        public int Count
        {
            get
            {
                // Return the number of tokens.
                return myTokens.Length;
            }
        }


    }
}
