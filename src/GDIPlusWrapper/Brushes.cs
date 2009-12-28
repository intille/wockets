
    //
    // System.Windows.Drawing.BrushPluses.cs
    //
    // Authors:
    //   Dennis Hayes (dennish@Raytek.com)
    //	Suesan Chaney
    //	  Peter Bartok (pbartok@novell.com)
    //
    // (C) Ximian, Inc., 2002 http://www.ximian.com
    // (C) Novell, Inc., 2004 http://www.novell.com
    //

    //
    // Copyright (C) 2004 Novell, Inc (http://www.novell.com)
    //
    // Permission is hereby granted, free of charge, to any person obtaining
    // a copy of this software and associated documentation files (the
    // "Software"), to deal in the Software without restriction, including
    // without limitation the rights to use, copy, modify, merge, publish,
    // distribute, sublicense, and/or sell copies of the Software, and to
    // permit persons to whom the Software is furnished to do so, subject to
    // the following conditions:
    // 
    // The above copyright notice and this permission notice shall be
    // included in all copies or substantial portions of the Software.
    // 
    // THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    // EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    // MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    // NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
    // LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
    // OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
    // WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
    //

using System;
using System.Drawing;


namespace  OpenNETCF.GDIPlus
{
    public sealed class Brushes
    {
        static SolidBrushPlus aliceBlue;
        static SolidBrushPlus antiqueWhite;
        static SolidBrushPlus aqua;
        static SolidBrushPlus aquamarine;
        static SolidBrushPlus azure;
        static SolidBrushPlus beige;
        static SolidBrushPlus bisque;
        static SolidBrushPlus black;
        static SolidBrushPlus blanchedAlmond;
        static SolidBrushPlus blue;
        static SolidBrushPlus blueViolet;
        static SolidBrushPlus brown;
        static SolidBrushPlus burlyWood;
        static SolidBrushPlus cadetBlue;
        static SolidBrushPlus chartreuse;
        static SolidBrushPlus chocolate;
        static SolidBrushPlus coral;
        static SolidBrushPlus cornflowerBlue;
        static SolidBrushPlus cornsilk;
        static SolidBrushPlus crimson;
        static SolidBrushPlus cyan;
        static SolidBrushPlus darkBlue;
        static SolidBrushPlus darkCyan;
        static SolidBrushPlus darkGoldenrod;
        static SolidBrushPlus darkGray;
        static SolidBrushPlus darkGreen;
        static SolidBrushPlus darkKhaki;
        static SolidBrushPlus darkMagenta;
        static SolidBrushPlus darkOliveGreen;
        static SolidBrushPlus darkOrange;
        static SolidBrushPlus darkOrchid;
        static SolidBrushPlus darkRed;
        static SolidBrushPlus darkSalmon;
        static SolidBrushPlus darkSeaGreen;
        static SolidBrushPlus darkSlateBlue;
        static SolidBrushPlus darkSlateGray;
        static SolidBrushPlus darkTurquoise;
        static SolidBrushPlus darkViolet;
        static SolidBrushPlus deepPink;
        static SolidBrushPlus deepSkyBlue;
        static SolidBrushPlus dimGray;
        static SolidBrushPlus dodgerBlue;
        static SolidBrushPlus firebrick;
        static SolidBrushPlus floralWhite;
        static SolidBrushPlus forestGreen;
        static SolidBrushPlus fuchsia;
        static SolidBrushPlus gainsboro;
        static SolidBrushPlus ghostWhite;
        static SolidBrushPlus gold;
        static SolidBrushPlus goldenrod;
        static SolidBrushPlus gray;
        static SolidBrushPlus green;
        static SolidBrushPlus greenYellow;
        static SolidBrushPlus honeydew;
        static SolidBrushPlus hotPink;
        static SolidBrushPlus indianRed;
        static SolidBrushPlus indigo;
        static SolidBrushPlus ivory;
        static SolidBrushPlus khaki;
        static SolidBrushPlus lavender;
        static SolidBrushPlus lavenderBlush;
        static SolidBrushPlus lawnGreen;
        static SolidBrushPlus lemonChiffon;
        static SolidBrushPlus lightBlue;
        static SolidBrushPlus lightCoral;
        static SolidBrushPlus lightCyan;
        static SolidBrushPlus lightGoldenrodYellow;
        static SolidBrushPlus lightGray;
        static SolidBrushPlus lightGreen;
        static SolidBrushPlus lightPink;
        static SolidBrushPlus lightSalmon;
        static SolidBrushPlus lightSeaGreen;
        static SolidBrushPlus lightSkyBlue;
        static SolidBrushPlus lightSlateGray;
        static SolidBrushPlus lightSteelBlue;
        static SolidBrushPlus lightYellow;
        static SolidBrushPlus lime;
        static SolidBrushPlus limeGreen;
        static SolidBrushPlus linen;
        static SolidBrushPlus magenta;
        static SolidBrushPlus maroon;
        static SolidBrushPlus mediumAquamarine;
        static SolidBrushPlus mediumBlue;
        static SolidBrushPlus mediumOrchid;
        static SolidBrushPlus mediumPurple;
        static SolidBrushPlus mediumSeaGreen;
        static SolidBrushPlus mediumSlateBlue;
        static SolidBrushPlus mediumSpringGreen;
        static SolidBrushPlus mediumTurquoise;
        static SolidBrushPlus mediumVioletRed;
        static SolidBrushPlus midnightBlue;
        static SolidBrushPlus mintCream;
        static SolidBrushPlus mistyRose;
        static SolidBrushPlus moccasin;
        static SolidBrushPlus navajoWhite;
        static SolidBrushPlus navy;
        static SolidBrushPlus oldLace;
        static SolidBrushPlus olive;
        static SolidBrushPlus oliveDrab;
        static SolidBrushPlus orange;
        static SolidBrushPlus orangeRed;
        static SolidBrushPlus orchid;
        static SolidBrushPlus paleGoldenrod;
        static SolidBrushPlus paleGreen;
        static SolidBrushPlus paleTurquoise;
        static SolidBrushPlus paleVioletRed;
        static SolidBrushPlus papayaWhip;
        static SolidBrushPlus peachPuff;
        static SolidBrushPlus peru;
        static SolidBrushPlus pink;
        static SolidBrushPlus plum;
        static SolidBrushPlus powderBlue;
        static SolidBrushPlus purple;
        static SolidBrushPlus red;
        static SolidBrushPlus rosyBrown;
        static SolidBrushPlus royalBlue;
        static SolidBrushPlus saddleBrown;
        static SolidBrushPlus salmon;
        static SolidBrushPlus sandyBrown;
        static SolidBrushPlus seaGreen;
        static SolidBrushPlus seaShell;
        static SolidBrushPlus sienna;
        static SolidBrushPlus silver;
        static SolidBrushPlus skyBlue;
        static SolidBrushPlus slateBlue;
        static SolidBrushPlus slateGray;
        static SolidBrushPlus snow;
        static SolidBrushPlus springGreen;
        static SolidBrushPlus steelBlue;
        static SolidBrushPlus tan;
        static SolidBrushPlus teal;
        static SolidBrushPlus thistle;
        static SolidBrushPlus tomato;
        static SolidBrushPlus transparent;
        static SolidBrushPlus turquoise;
        static SolidBrushPlus violet;
        static SolidBrushPlus wheat;
        static SolidBrushPlus white;
        static SolidBrushPlus whiteSmoke;
        static SolidBrushPlus yellow;
        static SolidBrushPlus yellowGreen;

        // We intentionally do not set the is_modifiable=false flag on
        // the BrushPluses, to stay Microsoft compatible

        private Brushes() { }

        public static BrushPlus AliceBlue
        {
            get
            {
                if (aliceBlue == null)
                {
                    aliceBlue = new SolidBrushPlus(Color.AliceBlue);
                }
                return (aliceBlue);
            }
        }

        public static BrushPlus AntiqueWhite
        {
            get
            {
                if (antiqueWhite == null)
                {
                    antiqueWhite = new SolidBrushPlus(Color.AntiqueWhite);
                }
                return (antiqueWhite);
            }
        }

        public static BrushPlus Aqua
        {
            get
            {
                if (aqua == null)
                {
                    aqua = new SolidBrushPlus(Color.Aqua);
                }
                return (aqua);
            }
        }

        public static BrushPlus Aquamarine
        {
            get
            {
                if (aquamarine == null)
                {
                    aquamarine = new SolidBrushPlus(Color.Aquamarine);
                }
                return (aquamarine);
            }
        }

        public static BrushPlus Azure
        {
            get
            {
                if (azure == null)
                {
                    azure = new SolidBrushPlus(Color.Azure);
                }
                return (azure);
            }
        }

        public static BrushPlus Beige
        {
            get
            {
                if (beige == null)
                {
                    beige = new SolidBrushPlus(Color.Beige);
                }
                return (beige);
            }
        }

        public static BrushPlus Bisque
        {
            get
            {
                if (bisque == null)
                {
                    bisque = new SolidBrushPlus(Color.Bisque);
                }
                return (bisque);
            }
        }

        public static BrushPlus Black
        {
            get
            {
                if (black == null)
                {
                    black = new SolidBrushPlus(Color.Black);
                }
                return (black);
            }
        }

        public static BrushPlus BlanchedAlmond
        {
            get
            {
                if (blanchedAlmond == null)
                {
                    blanchedAlmond = new SolidBrushPlus(Color.BlanchedAlmond);
                }
                return (blanchedAlmond);
            }
        }

        public static BrushPlus Blue
        {
            get
            {
                if (blue == null)
                {
                    blue = new SolidBrushPlus(Color.Blue);
                }
                return (blue);
            }
        }

        public static BrushPlus BlueViolet
        {
            get
            {
                if (blueViolet == null)
                {
                    blueViolet = new SolidBrushPlus(Color.BlueViolet);
                }
                return (blueViolet);
            }
        }

        public static BrushPlus Brown
        {
            get
            {
                if (brown == null)
                {
                    brown = new SolidBrushPlus(Color.Brown);
                }
                return (brown);
            }
        }

        public static BrushPlus BurlyWood
        {
            get
            {
                if (burlyWood == null)
                {
                    burlyWood = new SolidBrushPlus(Color.BurlyWood);
                }
                return (burlyWood);
            }
        }

        public static BrushPlus CadetBlue
        {
            get
            {
                if (cadetBlue == null)
                {
                    cadetBlue = new SolidBrushPlus(Color.CadetBlue);
                }
                return (cadetBlue);
            }
        }

        public static BrushPlus Chartreuse
        {
            get
            {
                if (chartreuse == null)
                {
                    chartreuse = new SolidBrushPlus(Color.Chartreuse);
                }
                return (chartreuse);
            }
        }

        public static BrushPlus Chocolate
        {
            get
            {
                if (chocolate == null)
                {
                    chocolate = new SolidBrushPlus(Color.Chocolate);
                }
                return (chocolate);
            }
        }

        public static BrushPlus Coral
        {
            get
            {
                if (coral == null)
                {
                    coral = new SolidBrushPlus(Color.Coral);
                }
                return (coral);
            }
        }

        public static BrushPlus CornflowerBlue
        {
            get
            {
                if (cornflowerBlue == null)
                {
                    cornflowerBlue = new SolidBrushPlus(Color.CornflowerBlue);
                }
                return (cornflowerBlue);
            }
        }

        public static BrushPlus Cornsilk
        {
            get
            {
                if (cornsilk == null)
                {
                    cornsilk = new SolidBrushPlus(Color.Cornsilk);
                }
                return (cornsilk);
            }
        }

        public static BrushPlus Crimson
        {
            get
            {
                if (crimson == null)
                {
                    crimson = new SolidBrushPlus(Color.Crimson);
                }
                return (crimson);
            }
        }

        public static BrushPlus Cyan
        {
            get
            {
                if (cyan == null)
                {
                    cyan = new SolidBrushPlus(Color.Cyan);
                }
                return (cyan);
            }
        }

        public static BrushPlus DarkBlue
        {
            get
            {
                if (darkBlue == null)
                {
                    darkBlue = new SolidBrushPlus(Color.DarkBlue);
                }
                return (darkBlue);
            }
        }

        public static BrushPlus DarkCyan
        {
            get
            {
                if (darkCyan == null)
                {
                    darkCyan = new SolidBrushPlus(Color.DarkCyan);
                }
                return (darkCyan);
            }
        }

        public static BrushPlus DarkGoldenrod
        {
            get
            {
                if (darkGoldenrod == null)
                {
                    darkGoldenrod = new SolidBrushPlus(Color.DarkGoldenrod);
                }
                return (darkGoldenrod);
            }
        }

        public static BrushPlus DarkGray
        {
            get
            {
                if (darkGray == null)
                {
                    darkGray = new SolidBrushPlus(Color.DarkGray);
                }
                return (darkGray);
            }
        }

        public static BrushPlus DarkGreen
        {
            get
            {
                if (darkGreen == null)
                {
                    darkGreen = new SolidBrushPlus(Color.DarkGreen);
                }
                return (darkGreen);
            }
        }

        public static BrushPlus DarkKhaki
        {
            get
            {
                if (darkKhaki == null)
                {
                    darkKhaki = new SolidBrushPlus(Color.DarkKhaki);
                }
                return (darkKhaki);
            }
        }

        public static BrushPlus DarkMagenta
        {
            get
            {
                if (darkMagenta == null)
                {
                    darkMagenta = new SolidBrushPlus(Color.DarkMagenta);
                }
                return (darkMagenta);
            }
        }

        public static BrushPlus DarkOliveGreen
        {
            get
            {
                if (darkOliveGreen == null)
                {
                    darkOliveGreen = new SolidBrushPlus(Color.DarkOliveGreen);
                }
                return (darkOliveGreen);
            }
        }

        public static BrushPlus DarkOrange
        {
            get
            {
                if (darkOrange == null)
                {
                    darkOrange = new SolidBrushPlus(Color.DarkOrange);
                }
                return (darkOrange);
            }
        }

        public static BrushPlus DarkOrchid
        {
            get
            {
                if (darkOrchid == null)
                {
                    darkOrchid = new SolidBrushPlus(Color.DarkOrchid);
                }
                return (darkOrchid);
            }
        }

        public static BrushPlus DarkRed
        {
            get
            {
                if (darkRed == null)
                {
                    darkRed = new SolidBrushPlus(Color.DarkRed);
                }
                return (darkRed);
            }
        }

        public static BrushPlus DarkSalmon
        {
            get
            {
                if (darkSalmon == null)
                {
                    darkSalmon = new SolidBrushPlus(Color.DarkSalmon);
                }
                return (darkSalmon);
            }
        }

        public static BrushPlus DarkSeaGreen
        {
            get
            {
                if (darkSeaGreen == null)
                {
                    darkSeaGreen = new SolidBrushPlus(Color.DarkSeaGreen);
                }
                return (darkSeaGreen);
            }
        }

        public static BrushPlus DarkSlateBlue
        {
            get
            {
                if (darkSlateBlue == null)
                {
                    darkSlateBlue = new SolidBrushPlus(Color.DarkSlateBlue);
                }
                return (darkSlateBlue);
            }
        }

        public static BrushPlus DarkSlateGray
        {
            get
            {
                if (darkSlateGray == null)
                {
                    darkSlateGray = new SolidBrushPlus(Color.DarkSlateGray);
                }
                return (darkSlateGray);
            }
        }

        public static BrushPlus DarkTurquoise
        {
            get
            {
                if (darkTurquoise == null)
                {
                    darkTurquoise = new SolidBrushPlus(Color.DarkTurquoise);
                }
                return (darkTurquoise);
            }
        }

        public static BrushPlus DarkViolet
        {
            get
            {
                if (darkViolet == null)
                {
                    darkViolet = new SolidBrushPlus(Color.DarkViolet);
                }
                return (darkViolet);
            }
        }

        public static BrushPlus DeepPink
        {
            get
            {
                if (deepPink == null)
                {
                    deepPink = new SolidBrushPlus(Color.DeepPink);
                }
                return (deepPink);
            }
        }

        public static BrushPlus DeepSkyBlue
        {
            get
            {
                if (deepSkyBlue == null)
                {
                    deepSkyBlue = new SolidBrushPlus(Color.DeepSkyBlue);
                }
                return (deepSkyBlue);
            }
        }

        public static BrushPlus DimGray
        {
            get
            {
                if (dimGray == null)
                {
                    dimGray = new SolidBrushPlus(Color.DimGray);
                }
                return (dimGray);
            }
        }

        public static BrushPlus DodgerBlue
        {
            get
            {
                if (dodgerBlue == null)
                {
                    dodgerBlue = new SolidBrushPlus(Color.DodgerBlue);
                }
                return (dodgerBlue);
            }
        }

        public static BrushPlus Firebrick
        {
            get
            {
                if (firebrick == null)
                {
                    firebrick = new SolidBrushPlus(Color.Firebrick);
                }
                return (firebrick);
            }
        }

        public static BrushPlus FloralWhite
        {
            get
            {
                if (floralWhite == null)
                {
                    floralWhite = new SolidBrushPlus(Color.FloralWhite);
                }
                return (floralWhite);
            }
        }

        public static BrushPlus ForestGreen
        {
            get
            {
                if (forestGreen == null)
                {
                    forestGreen = new SolidBrushPlus(Color.ForestGreen);
                }
                return (forestGreen);
            }
        }

        public static BrushPlus Fuchsia
        {
            get
            {
                if (fuchsia == null)
                {
                    fuchsia = new SolidBrushPlus(Color.Fuchsia);
                }
                return (fuchsia);
            }
        }

        public static BrushPlus Gainsboro
        {
            get
            {
                if (gainsboro == null)
                {
                    gainsboro = new SolidBrushPlus(Color.Gainsboro);
                }
                return (gainsboro);
            }
        }

        public static BrushPlus GhostWhite
        {
            get
            {
                if (ghostWhite == null)
                {
                    ghostWhite = new SolidBrushPlus(Color.GhostWhite);
                }
                return (ghostWhite);
            }
        }

        public static BrushPlus Gold
        {
            get
            {
                if (gold == null)
                {
                    gold = new SolidBrushPlus(Color.Gold);
                }
                return (gold);
            }
        }

        public static BrushPlus Goldenrod
        {
            get
            {
                if (goldenrod == null)
                {
                    goldenrod = new SolidBrushPlus(Color.Goldenrod);
                }
                return (goldenrod);
            }
        }

        public static BrushPlus Gray
        {
            get
            {
                if (gray == null)
                {
                    gray = new SolidBrushPlus(Color.Gray);
                }
                return (gray);
            }
        }

        public static BrushPlus Green
        {
            get
            {
                if (green == null)
                {
                    green = new SolidBrushPlus(Color.Green);
                }
                return (green);
            }
        }

        public static BrushPlus GreenYellow
        {
            get
            {
                if (greenYellow == null)
                {
                    greenYellow = new SolidBrushPlus(Color.GreenYellow);
                }
                return (greenYellow);
            }
        }

        public static BrushPlus Honeydew
        {
            get
            {
                if (honeydew == null)
                {
                    honeydew = new SolidBrushPlus(Color.Honeydew);
                }
                return (honeydew);
            }
        }

        public static BrushPlus HotPink
        {
            get
            {
                if (hotPink == null)
                {
                    hotPink = new SolidBrushPlus(Color.HotPink);
                }
                return (hotPink);
            }
        }

        public static BrushPlus IndianRed
        {
            get
            {
                if (indianRed == null)
                {
                    indianRed = new SolidBrushPlus(Color.IndianRed);
                }
                return (indianRed);
            }
        }

        public static BrushPlus Indigo
        {
            get
            {
                if (indigo == null)
                {
                    indigo = new SolidBrushPlus(Color.Indigo);
                }
                return (indigo);
            }
        }

        public static BrushPlus Ivory
        {
            get
            {
                if (ivory == null)
                {
                    ivory = new SolidBrushPlus(Color.Ivory);
                }
                return (ivory);
            }
        }

        public static BrushPlus Khaki
        {
            get
            {
                if (khaki == null)
                {
                    khaki = new SolidBrushPlus(Color.Khaki);
                }
                return (khaki);
            }
        }

        public static BrushPlus Lavender
        {
            get
            {
                if (lavender == null)
                {
                    lavender = new SolidBrushPlus(Color.Lavender);
                }
                return (lavender);
            }
        }

        public static BrushPlus LavenderBlush
        {
            get
            {
                if (lavenderBlush == null)
                {
                    lavenderBlush = new SolidBrushPlus(Color.LavenderBlush);
                }
                return (lavenderBlush);
            }
        }

        public static BrushPlus LawnGreen
        {
            get
            {
                if (lawnGreen == null)
                {
                    lawnGreen = new SolidBrushPlus(Color.LawnGreen);
                }
                return (lawnGreen);
            }
        }

        public static BrushPlus LemonChiffon
        {
            get
            {
                if (lemonChiffon == null)
                {
                    lemonChiffon = new SolidBrushPlus(Color.LemonChiffon);
                }
                return (lemonChiffon);
            }
        }

        public static BrushPlus LightBlue
        {
            get
            {
                if (lightBlue == null)
                {
                    lightBlue = new SolidBrushPlus(Color.LightBlue);
                }
                return (lightBlue);
            }
        }

        public static BrushPlus LightCoral
        {
            get
            {
                if (lightCoral == null)
                {
                    lightCoral = new SolidBrushPlus(Color.LightCoral);
                }
                return (lightCoral);
            }
        }

        public static BrushPlus LightCyan
        {
            get
            {
                if (lightCyan == null)
                {
                    lightCyan = new SolidBrushPlus(Color.LightCyan);
                }
                return (lightCyan);
            }
        }

        public static BrushPlus LightGoldenrodYellow
        {
            get
            {
                if (lightGoldenrodYellow == null)
                {
                    lightGoldenrodYellow = new SolidBrushPlus(Color.LightGoldenrodYellow);
                }
                return (lightGoldenrodYellow);
            }
        }

        public static BrushPlus LightGray
        {
            get
            {
                if (lightGray == null)
                {
                    lightGray = new SolidBrushPlus(Color.LightGray);
                }
                return (lightGray);
            }
        }

        public static BrushPlus LightGreen
        {
            get
            {
                if (lightGreen == null)
                {
                    lightGreen = new SolidBrushPlus(Color.LightGreen);
                }
                return (lightGreen);
            }
        }

        public static BrushPlus LightPink
        {
            get
            {
                if (lightPink == null)
                {
                    lightPink = new SolidBrushPlus(Color.LightPink);
                }
                return (lightPink);
            }
        }

        public static BrushPlus LightSalmon
        {
            get
            {
                if (lightSalmon == null)
                {
                    lightSalmon = new SolidBrushPlus(Color.LightSalmon);
                }
                return (lightSalmon);
            }
        }

        public static BrushPlus LightSeaGreen
        {
            get
            {
                if (lightSeaGreen == null)
                {
                    lightSeaGreen = new SolidBrushPlus(Color.LightSeaGreen);
                }
                return (lightSeaGreen);
            }
        }

        public static BrushPlus LightSkyBlue
        {
            get
            {
                if (lightSkyBlue == null)
                {
                    lightSkyBlue = new SolidBrushPlus(Color.LightSkyBlue);
                }
                return (lightSkyBlue);
            }
        }

        public static BrushPlus LightSlateGray
        {
            get
            {
                if (lightSlateGray == null)
                {
                    lightSlateGray = new SolidBrushPlus(Color.LightSlateGray);
                }
                return (lightSlateGray);
            }
        }

        public static BrushPlus LightSteelBlue
        {
            get
            {
                if (lightSteelBlue == null)
                {
                    lightSteelBlue = new SolidBrushPlus(Color.LightSteelBlue);
                }
                return (lightSteelBlue);
            }
        }

        public static BrushPlus LightYellow
        {
            get
            {
                if (lightYellow == null)
                {
                    lightYellow = new SolidBrushPlus(Color.LightYellow);
                }
                return (lightYellow);
            }
        }

        public static BrushPlus Lime
        {
            get
            {
                if (lime == null)
                {
                    lime = new SolidBrushPlus(Color.Lime);
                }
                return (lime);
            }
        }

        public static BrushPlus LimeGreen
        {
            get
            {
                if (limeGreen == null)
                {
                    limeGreen = new SolidBrushPlus(Color.LimeGreen);
                }
                return (limeGreen);
            }
        }

        public static BrushPlus Linen
        {
            get
            {
                if (linen == null)
                {
                    linen = new SolidBrushPlus(Color.Linen);
                }
                return (linen);
            }
        }

        public static BrushPlus Magenta
        {
            get
            {
                if (magenta == null)
                {
                    magenta = new SolidBrushPlus(Color.Magenta);
                }
                return (magenta);
            }
        }

        public static BrushPlus Maroon
        {
            get
            {
                if (maroon == null)
                {
                    maroon = new SolidBrushPlus(Color.Maroon);
                }
                return (maroon);
            }
        }

        public static BrushPlus MediumAquamarine
        {
            get
            {
                if (mediumAquamarine == null)
                {
                    mediumAquamarine = new SolidBrushPlus(Color.MediumAquamarine);
                }
                return (mediumAquamarine);
            }
        }

        public static BrushPlus MediumBlue
        {
            get
            {
                if (mediumBlue == null)
                {
                    mediumBlue = new SolidBrushPlus(Color.MediumBlue);
                }
                return (mediumBlue);
            }
        }

        public static BrushPlus MediumOrchid
        {
            get
            {
                if (mediumOrchid == null)
                {
                    mediumOrchid = new SolidBrushPlus(Color.MediumOrchid);
                }
                return (mediumOrchid);
            }
        }

        public static BrushPlus MediumPurple
        {
            get
            {
                if (mediumPurple == null)
                {
                    mediumPurple = new SolidBrushPlus(Color.MediumPurple);
                }
                return (mediumPurple);
            }
        }

        public static BrushPlus MediumSeaGreen
        {
            get
            {
                if (mediumSeaGreen == null)
                {
                    mediumSeaGreen = new SolidBrushPlus(Color.MediumSeaGreen);
                }
                return (mediumSeaGreen);
            }
        }

        public static BrushPlus MediumSlateBlue
        {
            get
            {
                if (mediumSlateBlue == null)
                {
                    mediumSlateBlue = new SolidBrushPlus(Color.MediumSlateBlue);
                }
                return (mediumSlateBlue);
            }
        }

        public static BrushPlus MediumSpringGreen
        {
            get
            {
                if (mediumSpringGreen == null)
                {
                    mediumSpringGreen = new SolidBrushPlus(Color.MediumSpringGreen);
                }
                return (mediumSpringGreen);
            }
        }

        public static BrushPlus MediumTurquoise
        {
            get
            {
                if (mediumTurquoise == null)
                {
                    mediumTurquoise = new SolidBrushPlus(Color.MediumTurquoise);
                }
                return (mediumTurquoise);
            }
        }

        public static BrushPlus MediumVioletRed
        {
            get
            {
                if (mediumVioletRed == null)
                {
                    mediumVioletRed = new SolidBrushPlus(Color.MediumVioletRed);
                }
                return (mediumVioletRed);
            }
        }

        public static BrushPlus MidnightBlue
        {
            get
            {
                if (midnightBlue == null)
                {
                    midnightBlue = new SolidBrushPlus(Color.MidnightBlue);
                }
                return (midnightBlue);
            }
        }

        public static BrushPlus MintCream
        {
            get
            {
                if (mintCream == null)
                {
                    mintCream = new SolidBrushPlus(Color.MintCream);
                }
                return (mintCream);
            }
        }

        public static BrushPlus MistyRose
        {
            get
            {
                if (mistyRose == null)
                {
                    mistyRose = new SolidBrushPlus(Color.MistyRose);
                }
                return (mistyRose);
            }
        }

        public static BrushPlus Moccasin
        {
            get
            {
                if (moccasin == null)
                {
                    moccasin = new SolidBrushPlus(Color.Moccasin);
                }
                return (moccasin);
            }
        }

        public static BrushPlus NavajoWhite
        {
            get
            {
                if (navajoWhite == null)
                {
                    navajoWhite = new SolidBrushPlus(Color.NavajoWhite);
                }
                return (navajoWhite);
            }
        }

        public static BrushPlus Navy
        {
            get
            {
                if (navy == null)
                {
                    navy = new SolidBrushPlus(Color.Navy);
                }
                return (navy);
            }
        }

        public static BrushPlus OldLace
        {
            get
            {
                if (oldLace == null)
                {
                    oldLace = new SolidBrushPlus(Color.OldLace);
                }
                return (oldLace);
            }
        }

        public static BrushPlus Olive
        {
            get
            {
                if (olive == null)
                {
                    olive = new SolidBrushPlus(Color.Olive);
                }
                return (olive);
            }
        }

        public static BrushPlus OliveDrab
        {
            get
            {
                if (oliveDrab == null)
                {
                    oliveDrab = new SolidBrushPlus(Color.OliveDrab);
                }
                return (oliveDrab);
            }
        }

        public static BrushPlus Orange
        {
            get
            {
                if (orange == null)
                {
                    orange = new SolidBrushPlus(Color.Orange);
                }
                return (orange);
            }
        }

        public static BrushPlus OrangeRed
        {
            get
            {
                if (orangeRed == null)
                {
                    orangeRed = new SolidBrushPlus(Color.OrangeRed);
                }
                return (orangeRed);
            }
        }

        public static BrushPlus Orchid
        {
            get
            {
                if (orchid == null)
                {
                    orchid = new SolidBrushPlus(Color.Orchid);
                }
                return (orchid);
            }
        }

        public static BrushPlus PaleGoldenrod
        {
            get
            {
                if (paleGoldenrod == null)
                {
                    paleGoldenrod = new SolidBrushPlus(Color.PaleGoldenrod);
                }
                return (paleGoldenrod);
            }
        }

        public static BrushPlus PaleGreen
        {
            get
            {
                if (paleGreen == null)
                {
                    paleGreen = new SolidBrushPlus(Color.PaleGreen);
                }
                return (paleGreen);
            }
        }

        public static BrushPlus PaleTurquoise
        {
            get
            {
                if (paleTurquoise == null)
                {
                    paleTurquoise = new SolidBrushPlus(Color.PaleTurquoise);
                }
                return (paleTurquoise);
            }
        }

        public static BrushPlus PaleVioletRed
        {
            get
            {
                if (paleVioletRed == null)
                {
                    paleVioletRed = new SolidBrushPlus(Color.PaleVioletRed);
                }
                return (paleVioletRed);
            }
        }

        public static BrushPlus PapayaWhip
        {
            get
            {
                if (papayaWhip == null)
                {
                    papayaWhip = new SolidBrushPlus(Color.PapayaWhip);
                }
                return (papayaWhip);
            }
        }

        public static BrushPlus PeachPuff
        {
            get
            {
                if (peachPuff == null)
                {
                    peachPuff = new SolidBrushPlus(Color.PeachPuff);
                }
                return (peachPuff);
            }
        }

        public static BrushPlus Peru
        {
            get
            {
                if (peru == null)
                {
                    peru = new SolidBrushPlus(Color.Peru);
                }
                return (peru);
            }
        }

        public static BrushPlus Pink
        {
            get
            {
                if (pink == null)
                {
                    pink = new SolidBrushPlus(Color.Pink);
                }
                return (pink);
            }
        }

        public static BrushPlus Plum
        {
            get
            {
                if (plum == null)
                {
                    plum = new SolidBrushPlus(Color.Plum);
                }
                return (plum);
            }
        }

        public static BrushPlus PowderBlue
        {
            get
            {
                if (powderBlue == null)
                {
                    powderBlue = new SolidBrushPlus(Color.PowderBlue);
                }
                return (powderBlue);
            }
        }

        public static BrushPlus Purple
        {
            get
            {
                if (purple == null)
                {
                    purple = new SolidBrushPlus(Color.Purple);
                }
                return (purple);
            }
        }

        public static BrushPlus Red
        {
            get
            {
                if (red == null)
                {
                    red = new SolidBrushPlus(Color.Red);
                }
                return (red);
            }
        }

        public static BrushPlus RosyBrown
        {
            get
            {
                if (rosyBrown == null)
                {
                    rosyBrown = new SolidBrushPlus(Color.RosyBrown);
                }
                return (rosyBrown);
            }
        }

        public static BrushPlus RoyalBlue
        {
            get
            {
                if (royalBlue == null)
                {
                    royalBlue = new SolidBrushPlus(Color.RoyalBlue);
                }
                return (royalBlue);
            }
        }

        public static BrushPlus SaddleBrown
        {
            get
            {
                if (saddleBrown == null)
                {
                    saddleBrown = new SolidBrushPlus(Color.SaddleBrown);
                }
                return (saddleBrown);
            }
        }

        public static BrushPlus Salmon
        {
            get
            {
                if (salmon == null)
                {
                    salmon = new SolidBrushPlus(Color.Salmon);
                }
                return (salmon);
            }
        }

        public static BrushPlus SandyBrown
        {
            get
            {
                if (sandyBrown == null)
                {
                    sandyBrown = new SolidBrushPlus(Color.SandyBrown);
                }
                return (sandyBrown);
            }
        }

        public static BrushPlus SeaGreen
        {
            get
            {
                if (seaGreen == null)
                {
                    seaGreen = new SolidBrushPlus(Color.SeaGreen);
                }
                return (seaGreen);
            }
        }

        public static BrushPlus SeaShell
        {
            get
            {
                if (seaShell == null)
                {
                    seaShell = new SolidBrushPlus(Color.SeaShell);
                }
                return (seaShell);
            }
        }

        public static BrushPlus Sienna
        {
            get
            {
                if (sienna == null)
                {
                    sienna = new SolidBrushPlus(Color.Sienna);
                }
                return (sienna);
            }
        }

        public static BrushPlus Silver
        {
            get
            {
                if (silver == null)
                {
                    silver = new SolidBrushPlus(Color.Silver);
                }
                return (silver);
            }
        }

        public static BrushPlus SkyBlue
        {
            get
            {
                if (skyBlue == null)
                {
                    skyBlue = new SolidBrushPlus(Color.SkyBlue);
                }
                return (skyBlue);
            }
        }

        public static BrushPlus SlateBlue
        {
            get
            {
                if (slateBlue == null)
                {
                    slateBlue = new SolidBrushPlus(Color.SlateBlue);
                }
                return (slateBlue);
            }
        }

        public static BrushPlus SlateGray
        {
            get
            {
                if (slateGray == null)
                {
                    slateGray = new SolidBrushPlus(Color.SlateGray);
                }
                return (slateGray);
            }
        }

        public static BrushPlus Snow
        {
            get
            {
                if (snow == null)
                {
                    snow = new SolidBrushPlus(Color.Snow);
                }
                return (snow);
            }
        }

        public static BrushPlus SpringGreen
        {
            get
            {
                if (springGreen == null)
                {
                    springGreen = new SolidBrushPlus(Color.SpringGreen);
                }
                return (springGreen);
            }
        }

        public static BrushPlus SteelBlue
        {
            get
            {
                if (steelBlue == null)
                {
                    steelBlue = new SolidBrushPlus(Color.SteelBlue);
                }
                return (steelBlue);
            }
        }

        public static BrushPlus Tan
        {
            get
            {
                if (tan == null)
                {
                    tan = new SolidBrushPlus(Color.Tan);
                }
                return (tan);
            }
        }

        public static BrushPlus Teal
        {
            get
            {
                if (teal == null)
                {
                    teal = new SolidBrushPlus(Color.Teal);
                }
                return (teal);
            }
        }

        public static BrushPlus Thistle
        {
            get
            {
                if (thistle == null)
                {
                    thistle = new SolidBrushPlus(Color.Thistle);
                }
                return (thistle);
            }
        }

        public static BrushPlus Tomato
        {
            get
            {
                if (tomato == null)
                {
                    tomato = new SolidBrushPlus(Color.Tomato);
                }
                return (tomato);
            }
        }

        public static BrushPlus Transparent
        {
            get
            {
                if (transparent == null)
                {
                    transparent = new SolidBrushPlus(Color.Transparent);
                }
                return (transparent);
            }
        }

        public static BrushPlus Turquoise
        {
            get
            {
                if (turquoise == null)
                {
                    turquoise = new SolidBrushPlus(Color.Turquoise);
                }
                return (turquoise);
            }
        }

        public static BrushPlus Violet
        {
            get
            {
                if (violet == null)
                {
                    violet = new SolidBrushPlus(Color.Violet);
                }
                return (violet);
            }
        }

        public static BrushPlus Wheat
        {
            get
            {
                if (wheat == null)
                {
                    wheat = new SolidBrushPlus(Color.Wheat);
                }
                return (wheat);
            }
        }

        public static BrushPlus White
        {
            get
            {
                if (white == null)
                {
                    white = new SolidBrushPlus(Color.White);
                }
                return (white);
            }
        }

        public static BrushPlus WhiteSmoke
        {
            get
            {
                if (whiteSmoke == null)
                {
                    whiteSmoke = new SolidBrushPlus(Color.WhiteSmoke);
                }
                return (whiteSmoke);
            }
        }

        public static BrushPlus Yellow
        {
            get
            {
                if (yellow == null)
                {
                    yellow = new SolidBrushPlus(Color.Yellow);
                }
                return (yellow);
            }
        }

        public static BrushPlus YellowGreen
        {
            get
            {
                if (yellowGreen == null)
                {
                    yellowGreen = new SolidBrushPlus(Color.YellowGreen);
                }
                return (yellowGreen);
            }
        }

    }
}

