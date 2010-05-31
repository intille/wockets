using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;
using Wockets;
using System.Collections; //ArrayList
using System.IO;

using ZedGraph;
using MobiRnD_RDT.Utilities;//FileReadWrite
using MobiRnD_RDT.Logging; //Logger


namespace NESPDataViewer
{
   
    public partial class Form1 : Form
    {
        #region FIELDS
        string _pathDataset = "";
        DateTime _firstDate = DateTime.MinValue;
        DateTime _lastDate = DateTime.MinValue;

        Hashtable _htPanes = new Hashtable();
        ArrayList _alCheckBoxes = new ArrayList();
        ArrayList _alLinesWithSymbols = new ArrayList();
        Hashtable _htBoxes = new Hashtable();

        bool _isFirstTime = true; //used to determine whether graphs need to be cleared on Reset
        bool _doesShowHover = true; 

        int _minutesPage = 60;

        //try setting these to false if graphing too slowly
        bool _isUsingLabels = true; //on mouse over, shows label for data point
        bool _isAdaptingPointSize = true; //as graph gets larger/smaller, changes point size to match
        bool _zoomedOut = true;

        #endregion

        #region INITIALIZE
        
        public Form1()
        {
            InitializeComponent();
            
        }
        public Form1(string pathStartDS)
        {
            Logger.LogDebug("Form1", "arguments " + pathStartDS);
            _pathDataset = pathStartDS;
            InitializeComponent();
            
        }

        private void Form1_Load(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
            SetGraphPanels();

            if (_isUsingLabels)
                zedGraphControl1.PointValueEvent += new ZedGraphControl.PointValueHandler(zedGraphControl1_PointValueEvent);

            if (_pathDataset.Length > 0) OpenDataset(_pathDataset);
        }
        
        #endregion

        #region LAYOUT and FORMATTING
        private void Form1_Resize(object sender, EventArgs e)
        {
            SetLayout();
        }

        private void SetLayout()
        {   
            int graphwidth = ClientRectangle.Width-groupBox1.Width;
            int graphheight = ClientRectangle.Height - 110;


            // Control Group dimentions
            groupBox1.Location = new Point(graphwidth, MainMenuStrip.Bottom +5);//+5
            groupBox1.Size = new Size(groupBox1.Width, graphheight -15); // added          
                       
            //Graph Dimensions
            zedGraphControl1.Location = new Point(0, MainMenuStrip.Bottom);
            zedGraphControl1.Size = new Size(graphwidth,graphheight);

            //Scroll Bar Dimentions
            hScrollBar1.Width = graphwidth-10;
            hScrollBar1.Location = new Point(5, zedGraphControl1.Bottom + 20);

            //Date and Time Labels Locations
            lbFirstDate.Location = new Point(5, hScrollBar1.Bottom);
            lbSecondDate.Location = new Point(hScrollBar1.Right - lbSecondDate.Width -100, hScrollBar1.Bottom);
            lbScrollTime.Location = new Point(hScrollBar1.Left, hScrollBar1.Top - lbScrollTime.Height);
            
            //Buttons Location
            buttonZoomOut.Location = new Point(hScrollBar1.Right + 5, hScrollBar1.Top-20); //-30
            buttonDisplayRaw.Location = new Point(hScrollBar1.Right + 5, hScrollBar1.Top+5);//+5
            button_sync.Location = new Point(hScrollBar1.Right +5, hScrollBar1.Top + 30);


            hScrollBar1.Visible = false;
        }




        private void SetGraphPanels()
        {
            MasterPane myMaster = zedGraphControl1.MasterPane;

            _firstDate = DateTime.Now;
            _lastDate = DateTime.Now.AddYears(-3);

            myMaster.PaneList.Clear();

            // Set the master pane title
            myMaster.Title.IsVisible = false;

            // Fill the pane background with a color gradient
            myMaster.Fill = new Fill(Color.White, Color.MediumSlateBlue, 45.0F);

            // Set the margins and the space between panes to 10 points
            myMaster.Margin.All = 0;
            myMaster.InnerPaneGap = 0;

            // Enable the master pane legend
            myMaster.Legend.IsVisible = false;
            //myMaster.Legend.Position = LegendPos.TopCenter;

            // Vertical pan and zoom not allowed
            zedGraphControl1.IsEnableVPan = false;
            zedGraphControl1.IsEnableVZoom = false;

            zedGraphControl1.IsShowPointValues = _isUsingLabels;
            zedGraphControl1.IsSynchronizeXAxes = true;        


        }
        private GraphPane AddPane(string name, string ytitle)
        {
            GraphPane pane = new GraphPane();
            pane.Margin.All = 5;
            pane.Legend.IsVisible = false;
            pane.Title.Text = name;
            pane.Title.IsVisible = false;
            pane.YAxis.Title.Text = ytitle;
            pane.XAxis.Title.IsVisible = false;
            pane.XAxis.Type = AxisType.Date;
            pane.XAxis.Scale.MajorUnit = DateUnit.Second;
            pane.XAxis.MajorGrid.IsVisible = true;
            //pane.YAxis.Scale.Min = 0;
            pane.Fill.Color = Color.Empty;
            zedGraphControl1.MasterPane.Add(pane);

            _htBoxes.Add(name, new BoxObj());

            #region ADD CHECKBOX
            _htPanes.Add(name, pane);
            CheckBox cBox = new CheckBox();
            cBox.Parent = groupBox1;
            if (_alCheckBoxes.Count > 0)
            {
                int y = ((CheckBox)_alCheckBoxes[_alCheckBoxes.Count - 1]).Bottom + 20;
                cBox.Location = new Point(5, y);
            }
            else cBox.Location = new Point(5, 15);
            cBox.Text = name;
            cBox.Checked = true;
            cBox.CheckedChanged += new EventHandler(checkBox_CheckedChanged);
            _alCheckBoxes.Add(cBox);
            #endregion

            //RefreshMasterPaneLayout();

            return pane;

        }
        private void RefreshMasterPaneLayout()
        {
            // Tell ZedGraph to auto layout all the panes
            using (Graphics g = CreateGraphics())
            {
                zedGraphControl1.MasterPane.SetLayout(g, PaneLayout.SingleColumn);                
            }
            if (_isAdaptingPointSize) SetPointSize();
            zedGraphControl1.AxisChange();
            zedGraphControl1.Refresh();

            #region ARRANGE CHECKBOXES
            if (_alCheckBoxes.Count > 1)
            {
                int lastcheckbox = 10;
                bool isFirstBox = true;
                for (int i = 0; i < _alCheckBoxes.Count; i++)
                {
                    string name = ((CheckBox)_alCheckBoxes[i]).Text;
                    int y = 0;
                    //Is Pane Showing? 
                    if (zedGraphControl1.MasterPane.PaneList.Contains((GraphPane)_htPanes[name]))
                    {
                        y = Convert.ToInt32(zedGraphControl1.MasterPane.PaneList[name].Rect.Y);
                        if ((y == 0) && (isFirstBox)) y = lastcheckbox;
                        else if (y < lastcheckbox) y = lastcheckbox + 2 + ((CheckBox)_alCheckBoxes[i]).Height;
                    }
                    else if (isFirstBox) y = lastcheckbox;
                    else y = lastcheckbox + 2 + ((CheckBox)_alCheckBoxes[i]).Height;
                    ((CheckBox)_alCheckBoxes[i]).Location = new Point(5, y);
                    isFirstBox = false;
                    lastcheckbox = y;
                }
                groupBox1.Visible = true;
            }
            else groupBox1.Visible = false;
            #endregion

        }

        private void SetPointSize()
        {
            if (zedGraphControl1.MasterPane.PaneList.Count > 0)
            {
                double minutes = ((TimeSpan)(_lastDate - _firstDate)).TotalMinutes;
                double ticks = (zedGraphControl1.MasterPane.PaneList[0].XAxis.Scale.Max - zedGraphControl1.MasterPane.PaneList[0].XAxis.Scale.Min)*1000;
                int charts = zedGraphControl1.MasterPane.PaneList.Count;
               //float point = (float)((10 * 7) / (ticks * charts));
                float point = 1;
                //else if (point > 10) point = 10;
                for (int i = 0; i < _alLinesWithSymbols.Count; i++)
                {
                    ((LineItem)_alLinesWithSymbols[i]).Symbol.Size = point;
                }
            }
        }
        private void SetTimes()
        {
            lbFirstDate.Text = _firstDate.ToString();
            lbSecondDate.Text = _lastDate.ToString();
            lbScrollTime.Text = _firstDate.ToString();
            TimeSpan ts = _lastDate - _firstDate;

            #region DETERMINE PAGING SIZE BASED ON TOTAL TIMESPAN OF DATA
            //if (ts.TotalHours > 1)//4 or more hours of data
            //    _minutesPage = 20;
            //else 
            if (ts.TotalMinutes > 60)//between 1-4 hours of data
                _minutesPage = 20;
            else if (ts.TotalMinutes > 15) _minutesPage = 5; //between 15-60 minutes of data
            else _minutesPage = 1;
            #endregion

            hScrollBar1.LargeChange = 1;
            hScrollBar1.SmallChange = 1;
            hScrollBar1.Maximum = (int)Math.Floor(ts.TotalMinutes / _minutesPage);


            //XDate startx = new XDate(_firstDate.AddMinutes(-padding));
            XDate startx = new XDate(_firstDate);

            //XDate endx = new XDate(_lastDate.AddMinutes(padding));
            XDate endx = new XDate(_lastDate);
            for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
            {
                zedGraphControl1.MasterPane[i].XAxis.Scale.Min = (double)startx;
                zedGraphControl1.MasterPane[i].XAxis.Scale.Max = (double)endx;
            }

            zedGraphControl1.AxisChange();
            zedGraphControl1.Refresh();
        }

        private void WidenDatesIfNeeded(PointPairList pl)
        {
            if (pl.Count > 0)
                WidenDatesIfNeeded(new XDate(pl[0].X), new XDate(pl[pl.Count - 1].X));
        }
        private void WidenDatesIfNeeded(XDate fDate, XDate lDate)
        {
            if (fDate.DateTime < _firstDate) _firstDate = fDate.DateTime;
            if (lDate.DateTime > _lastDate) _lastDate = lDate.DateTime;
        }

        private void SetEnable(bool isEnabled)
        {
            zedGraphControl1.Enabled = isEnabled;
            groupBox1.Enabled = isEnabled;
            hScrollBar1.Enabled = isEnabled;
            buttonZoomOut.Enabled = isEnabled;
            buttonDisplayRaw.Enabled = isEnabled;
            button_sync.Enabled = isEnabled;


            zedGraphControl1.Visible = isEnabled;
        }
        private void Reset()
        {
            if (!_isFirstTime)
            {
                _firstDate = DateTime.MinValue;
                _lastDate = DateTime.MinValue;

                zedGraphControl1.MasterPane.PaneList.Clear();
                zedGraphControl1.MasterPane.GraphObjList.Clear();
                _htBoxes.Clear();
                _htPanes.Clear();
                _alLinesWithSymbols.Clear();
                groupBox1.Controls.Clear();
                _alCheckBoxes.Clear();
            }
            else _isFirstTime = false;

        }
        #endregion

        #region CHART CONTENT
        #region HEART RATE
        private void AddHeartCurve(GraphPane gp, string name, PointPairList ppl,Color lineColor, PointPairList pplInvalid)
        {
            LineItem pointsCurve = gp.AddCurve("Heart rate " + name, ppl, lineColor, SymbolType.Circle);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Symbol.Fill = new Fill(lineColor);
            pointsCurve.Line.IsVisible = false;
            _alLinesWithSymbols.Add(pointsCurve);

            LineItem pointsCurveInvalid = gp.AddCurve("Heart rate " + name +", Out of Range", pplInvalid, lineColor, SymbolType.XCross);
            pointsCurveInvalid.Line.IsVisible = false;
            _alLinesWithSymbols.Add(pointsCurveInvalid);

        }
        
        private void CreateHeartRateGraph(GraphPane gp, string[] files)
        {
            string[] coloroptions = new string[] { "red", "darkred", "tomato", "crimson" };
            for (int f = 0; f < files.Length; f++)
            {
                string[] values = FileReadWrite.ReadLinesFromFile(files[f]);
                string name = Path.GetFileNameWithoutExtension(files[f]).Replace("HeartRate_", "");

                PointPairList listValid = new PointPairList();
                PointPairList listInvalid = new PointPairList();
                DateTime lastDate = new DateTime(1900, 1, 1);
                for (int i = 0; i < values.Length; i++)
                {
                    try
                    {
                        string[] split = values[i].Split(',');
                        if ((split.Length > 2) && (split[1].Length > 0) && (split[2].Length > 0))
                        {
                            DateTime dt = DateTime.Parse(split[1]);

                            double x = (double)new XDate(dt);
                            double y = Convert.ToDouble(split[2]);

                            string label = String.Format("Heart rate from {0}\n{1} {2}", name, dt.ToLongTimeString(), y);

                            if ((y >= 35) && (y <= 190))
                            {
                                if (_isUsingLabels) listValid.Add(x, y, label);
                                else listValid.Add(x, y);
                            }
                            else
                            {
                                if (_isUsingLabels) listInvalid.Add(x, y, label.Replace("Heart", "Invalid heart"));
                                else listInvalid.Add(x, y);
                            }
                        }
                    }
                    catch { }
                }

                AddHeartCurve(gp, name, listValid,Color.FromName(coloroptions[f]),listInvalid);

                WidenDatesIfNeeded(listValid);
            }

        }
        #endregion

        #region MITES
        private static DateTime ConvertUNIXDatTime(double timestamp)
        {
            // First make a System.DateTime equivalent to the UNIX Epoch.
            DateTime dateTime = new System.DateTime(1970, 1, 1, 0, 0, 0, 0);

            // Add the number of seconds in UNIX timestamp to be converted.
            dateTime = dateTime.AddSeconds(timestamp/1000);

            return dateTime;

        }


        private void AddAccelerationCurve(string name, string title, PointPairList pplX, PointPairList pplY, PointPairList pplZ, PointPairList pplActivityCount, PointPairList pplSamplingRate, PointPairList pplAUC, PointPairList pplVMag)
        {
            GraphPane pane = AddPane(name,"Acceleration - " + title);           

            LineItem pointsCurveX = pane.AddCurve("X", pplX, Color.LightBlue, SymbolType.Circle);
            LineItem pointsCurveY = pane.AddCurve("Y", pplY, Color.Blue, SymbolType.Circle);
            LineItem pointsCurveZ = pane.AddCurve("Z", pplZ, Color.DarkBlue, SymbolType.Circle);
            pointsCurveX.Symbol.Fill = new Fill(Color.LightBlue);
            pointsCurveY.Symbol.Fill = new Fill(Color.Blue);
            pointsCurveZ.Symbol.Fill = new Fill(Color.DarkBlue);
            if (!_isAdaptingPointSize)
            {
                pointsCurveX.Symbol.Size = 1F;
                pointsCurveY.Symbol.Size = 1F;
                pointsCurveZ.Symbol.Size = 1F;
            }
            _alLinesWithSymbols.Add(pointsCurveX);
            _alLinesWithSymbols.Add(pointsCurveY);
            _alLinesWithSymbols.Add(pointsCurveZ);

            pointsCurveX.Line.IsVisible = false;
            pointsCurveY.Line.IsVisible = false;
            pointsCurveZ.Line.IsVisible = false;

            LineItem pointsCurveSampling = pane.AddCurve("Sampling Rate", pplSamplingRate, Color.DarkGray, SymbolType.Circle);
      

            LineItem pointsCurveActivity = pane.AddCurve("Sum Absolute Derivative", pplActivityCount, Color.Violet, SymbolType.Circle);
            pointsCurveActivity.Symbol.Size = 1F;
            pointsCurveActivity.Symbol.Fill = new Fill(Color.Violet);
            _alLinesWithSymbols.Add(pointsCurveActivity);
            pointsCurveActivity.Line.IsVisible = false;

            LineItem pointsCurveAUC = pane.AddCurve("Area Under Curve", pplAUC, Color.Red, SymbolType.Circle);
            pointsCurveAUC.Symbol.Size = 1F;
            pointsCurveAUC.Symbol.Fill = new Fill(Color.Red);
            _alLinesWithSymbols.Add(pointsCurveAUC);
            pointsCurveAUC.Line.IsVisible = false;

              LineItem pointsCurveVMAG = pane.AddCurve("Vector Magnitude", pplVMag, Color.LimeGreen, SymbolType.Circle);
            pointsCurveVMAG.Symbol.Size = 1F;
             pointsCurveVMAG.Symbol.Fill = new Fill(Color.LimeGreen);
            _alLinesWithSymbols.Add(pointsCurveVMAG);
             pointsCurveVMAG.Line.IsVisible = false;
     
            pointsCurveActivity.IsY2Axis = true;
            

            

        }
        private void CreateAccelerationGraph(int paneOrder, string filepath, string channel, string location,string type,string mac)
        {
            #region ACCELERATION X Y Z
            string[] accel = FileReadWrite.ReadLinesFromFile(filepath);
                 
            PointPairList listX = new PointPairList();
            PointPairList listY = new PointPairList();
            PointPairList listZ = new PointPairList();                      

            for (int i = 1; i < accel.Length; i++)
            {
                try
                {
                    string[] split = accel[i].Split(',');
                    if ((split.Length > 4) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);

                        double x = (double)new XDate(dt);
                        double value = Convert.ToDouble(split[2]);
                        string label = String.Format("Channel {0}, X-axis, at {1}\n{2} {3}", channel, location, dt.ToLongTimeString(), value);

                        if (_isUsingLabels) listX.Add(x, value, label);
                        else listX.Add(x, value);

                        value = Convert.ToDouble(split[3]);
                        label = String.Format("Channel {0}, Y-axis, at {1}\n{2} {3}", channel, location, dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listY.Add(x, value, label);
                        else listY.Add(x, value);

                        value = Convert.ToDouble(split[4]);
                        label = label = String.Format("Channel {0}, Z-axis, at {1}\n{2} {3}", channel, location, dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listZ.Add(x, value, label);
                        else listZ.Add(x, value);
                    }
                }
                catch { }
            }
            #endregion

            #region SAMPLE RATES
            string[] samp = new string[0];
            string[] matches = Directory.GetFiles(Path.GetDirectoryName(filepath), String.Format(type + "_{0}_SampleRate*", channel));
            if (matches.Length == 1)
                samp = FileReadWrite.ReadLinesFromFile(matches[0]);

            PointPairList listSampleRates = new PointPairList();
            for (int i = 1; i < samp.Length; i++)
            {
                try
                {
                    string[] split = samp[i].Split(',');
                    if ((split.Length > 2) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);
                        double x = (double)new XDate(dt);
                        double value = Convert.ToDouble(split[2]);
                        string label = String.Format("{0} samples per second at {1}", value, dt.ToLongTimeString());
                        if (_isUsingLabels) listSampleRates.Add(x, value, label);
                        else listSampleRates.Add(x, value);
                    }
                }
                catch { }
            }
            #endregion

            #region ACTIVITY COUNTS
            string[] counts = new string[0];
            matches = Directory.GetFiles(Path.GetDirectoryName(filepath), String.Format(type + "_{0}_SAD*", channel));
            if (matches.Length == 1)
                counts = FileReadWrite.ReadLinesFromFile(matches[0]);
            PointPairList listActivityCounts = new PointPairList();
            for (int i = 1; i < counts.Length; i++)
            {
                try
                {
                    string[] split = counts[i].Split(',');
                    if ((split.Length > 4) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);
                        double x = (double)new XDate(dt);
                        double value = Convert.ToDouble(split[2]) + Convert.ToDouble(split[3]) + Convert.ToDouble(split[4]);
                        string label = String.Format("Sum Abs. Derivatives {0} at {1}", value, dt.ToLongTimeString());
                        if (_isUsingLabels) listActivityCounts.Add(x, value, label);
                        else listActivityCounts.Add(x, value);
                    }
                }
                catch { }
            }
            #endregion

            #region AUC
            string[] aucs = new string[0];
            matches = Directory.GetFiles(Path.GetDirectoryName(filepath), String.Format(type+"_{0}_AUC*", channel));
            if (matches.Length == 1)
                aucs = FileReadWrite.ReadLinesFromFile(matches[0]);
            PointPairList listAUCs = new PointPairList();
            for (int i = 1; i < aucs.Length; i++)
            {
                try
                {
                    string[] split = aucs[i].Split(',');
                    if ((split.Length > 4) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);
                        double x = (double)new XDate(dt);
                        double value = (Convert.ToDouble(split[2]) + Convert.ToDouble(split[3]) + Convert.ToDouble(split[4]))/20;
                        string label = String.Format("Area Under Curve {0}, {1} at {2}", location, value, dt.ToLongTimeString());
                        if (_isUsingLabels) listAUCs.Add(x, value, label);
                        else listAUCs.Add(x, value);
                    }
                }
                catch { }
            }
            #endregion

            #region VMAGS

             string[] vmags = new string[0];
             matches = Directory.GetFiles(Path.GetDirectoryName(filepath), String.Format(type+"_{0}_VMAG*", channel));
            if (matches.Length == 1)
                vmags = FileReadWrite.ReadLinesFromFile(matches[0]);

            PointPairList listVMAGs = new PointPairList();
            for (int i = 1; i < vmags.Length; i++)
            {
                try
                {
                    string[] split =vmags[i].Split(',');
                    if ((split.Length > 2) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);
                        double x = (double)new XDate(dt);
                        double value = Convert.ToDouble(split[2]);
                        string label = String.Format("Vector Magnitude {0}, {1} at {2}", location, value, dt.ToLongTimeString());
                        if (_isUsingLabels) listVMAGs.Add(x, value, label);
                        else listVMAGs.Add(x, value);
                    }
                }
                catch { }
            }
            #endregion


            if (mac.Length == 0)
            {
                AddAccelerationCurve(type + " " + channel, location, listX, listY, listZ, listActivityCounts, listSampleRates, listAUCs, listVMAGs);
                paneOrders.Add(type + " " + channel, paneOrder);
            }
            else
            {
                AddAccelerationCurve(mac, location, listX, listY, listZ, listActivityCounts, listSampleRates, listAUCs, listVMAGs);
                /* if (mac != "Internal")
                {
                    //mac = mac.Substring(mac.Length - 2, 2);
                    //mac = "Wocket " + mac;
                    //string loc = wc._Sensors[Convert.ToInt32(channel)]._Location;
                   string loc = "";
                    switch (location)
                    {
                        case "Dominant-Hip":
                            loc = "DHP";
                            break;
                        case "Dominant-Ankle":
                            loc = "DAK";
                            break;
                        case "Dominant-Upper-Arm":
                            loc = "DUA";
                            break;
                        case "Dominant-Wrist":
                            loc = "DW";
                            break;
                        case "Dominant-Thigh":
                            loc = "DT";
                            break;
                        default:
                            loc = "lOC";
                            break;
                    }
                    
                    //mac = "WKT-" + loc + "-" + mac;
                }*/
                paneOrders.Add(mac, paneOrder);
            }

          
            WidenDatesIfNeeded(listX);
        }

        #endregion




        #region Columbia Graph
        private void CreateColumbiaGraph(GraphPane gp, string filePath)
        {
            #region ACCELERATION X Y Z
            string[] accel = FileReadWrite.ReadLinesFromFile(filePath);

            PointPairList listX = new PointPairList();
            PointPairList listY = new PointPairList();
            PointPairList listZ = new PointPairList();

            for (int i = 1; i < accel.Length; i++)
            {
                try
                {
                    string[] split = accel[i].Split(',');
                    if ((split.Length > 6) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);

                        double x = (double)new XDate(dt);
                        double value = Convert.ToDouble(split[2]);
                        string label = String.Format("Columbia X-axis,\n{0} {1}", dt.ToLongTimeString(), value);

                        if (_isUsingLabels) listX.Add(x, value, label);
                        else listX.Add(x, value);

                        value = Convert.ToDouble(split[3]);
                        label = String.Format("Columbia Y-axis,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listY.Add(x, value, label);
                        else listY.Add(x, value);

                        value = Convert.ToDouble(split[4]);
                        label = label = String.Format("Columbia Z-axis,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listZ.Add(x, value, label);
                        else listZ.Add(x, value);
                    }
                }
                catch { }
            }
            #endregion


            
            LineItem pointsCurveX = gp.AddCurve("Columbia X", listX, Color.LightBlue, SymbolType.Circle);
            LineItem pointsCurveY = gp.AddCurve("Columbia Y", listY, Color.Blue, SymbolType.Circle);
            LineItem pointsCurveZ = gp.AddCurve("Columbia Z", listZ, Color.DarkBlue, SymbolType.Circle);
            pointsCurveX.Symbol.Fill = new Fill(Color.LightBlue);
            pointsCurveY.Symbol.Fill = new Fill(Color.Blue);
            pointsCurveZ.Symbol.Fill = new Fill(Color.DarkBlue);
            if (!_isAdaptingPointSize)
            {
                pointsCurveX.Symbol.Size = 1F;
                pointsCurveY.Symbol.Size = 1F;
                pointsCurveZ.Symbol.Size = 1F;
            }
            _alLinesWithSymbols.Add(pointsCurveX);
            _alLinesWithSymbols.Add(pointsCurveY);
            _alLinesWithSymbols.Add(pointsCurveZ);

            pointsCurveX.Line.IsVisible = false;
            pointsCurveY.Line.IsVisible = false;
            pointsCurveZ.Line.IsVisible = false;


            //paneOrders.Add("Columbia " + channel + " " + location, paneOrder);
            WidenDatesIfNeeded(listX);
        }

        #endregion Columbia Graph


        #region RTI Graph
        private void CreateRTIGraph(GraphPane gp, string filePath)
        {
            #region ACCELERATION X Y Z
            string[] accel = FileReadWrite.ReadLinesFromFile(filePath);

            PointPairList listX = new PointPairList();
            PointPairList listY = new PointPairList();
            PointPairList listZ = new PointPairList();

            PointPairList listAUCX = new PointPairList();
            PointPairList listAUCY = new PointPairList();
            PointPairList listAUCZ = new PointPairList();

            PointPairList listAUCXYZ = new PointPairList();

            for (int i = 1; i < accel.Length; i++)
            {
                try
                {
                    string[] split = accel[i].Split(',');
                    if ((split.Length > 8) && (split[1].Length > 0) && (split[2].Length > 0))
                    {
                        DateTime dt = DateTime.Parse(split[1]);

                        double x = (double)new XDate(dt);
                        double value = Convert.ToDouble(split[2]);
                        string label = String.Format("RTI X-axis,\n{0} {1}", dt.ToLongTimeString(), value);

                        if (_isUsingLabels) listX.Add(x, value * 1000.0, label);
                        else listX.Add(x * 1000.0, value);

                        value = Convert.ToDouble(split[3]);
                        label = String.Format("RTI Y-axis,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listY.Add(x, value * 1000.0, label);
                        else listY.Add(x, value * 1000.0);

                        value = Convert.ToDouble(split[4]);
                        label = String.Format("RTI Z-axis,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listZ.Add(x, value * 1000.0, label);
                        else listZ.Add(x, value * 1000.0);

                        value = Convert.ToDouble(split[5]) ;
                        label = String.Format("RTI X-AUC,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listAUCX.Add(x, value * 1000.0, label);
                        else listAUCX.Add(x, value * 1000.0);

                        value = Convert.ToDouble(split[6]);
                        label = String.Format("RTI Y-AUC,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listAUCY.Add(x, value * 1000.0, label);
                        else listAUCY.Add(x, value * 1000.0);

                        value = Convert.ToDouble(split[7]);
                        label = String.Format("RTI Z-AUC,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listAUCZ.Add(x, value * 1000.0, label);
                        else listAUCZ.Add(x, value * 1000.0);

                        value = Convert.ToDouble(split[8]) ;
                        label = String.Format("RTI XYZ-AUC,\n{0} {1}", dt.ToLongTimeString(), value);
                        if (_isUsingLabels) listAUCXYZ.Add(x, value * 1000.0, label);
                        else listAUCXYZ.Add(x, value * 1000.0);
                    }
                }
                catch { }
            }
            #endregion



            LineItem pointsCurveX = gp.AddCurve("RTI X", listX, Color.LightBlue, SymbolType.Circle);
            LineItem pointsCurveY = gp.AddCurve("RTI Y", listY, Color.Blue, SymbolType.Circle);
            LineItem pointsCurveZ = gp.AddCurve("RTI Z", listZ, Color.DarkBlue, SymbolType.Circle);
            LineItem pointsCurveAUCX = gp.AddCurve("RTI AUC X", listAUCX, Color.Green, SymbolType.Circle);
            LineItem pointsCurveAUCY = gp.AddCurve("RTI AUC Y", listAUCY, Color.Turquoise, SymbolType.Circle);
            LineItem pointsCurveAUCZ = gp.AddCurve("RTI AUC Z", listAUCZ, Color.Violet, SymbolType.Circle);
            LineItem pointsCurveAUCXYZ = gp.AddCurve("RTI AUC XYZ", listAUCXYZ, Color.Red, SymbolType.Circle);
            
            pointsCurveX.Symbol.Fill = new Fill(Color.LightBlue);
            pointsCurveY.Symbol.Fill = new Fill(Color.Blue);
            pointsCurveZ.Symbol.Fill = new Fill(Color.DarkBlue);
            pointsCurveAUCX.Symbol.Fill = new Fill(Color.Green);
            pointsCurveAUCY.Symbol.Fill = new Fill(Color.Turquoise);
            pointsCurveAUCZ.Symbol.Fill = new Fill(Color.Violet);
            pointsCurveAUCXYZ.Symbol.Fill = new Fill(Color.Red);
            
            if (!_isAdaptingPointSize)
            {
                pointsCurveX.Symbol.Size = 1F;
                pointsCurveY.Symbol.Size = 1F;
                pointsCurveZ.Symbol.Size = 1F;
                pointsCurveAUCX.Symbol.Size = 1F;
                pointsCurveAUCY.Symbol.Size = 1F;
                pointsCurveAUCZ.Symbol.Size = 1F;
                pointsCurveAUCXYZ.Symbol.Size = 1F;
            }
            _alLinesWithSymbols.Add(pointsCurveX);
            _alLinesWithSymbols.Add(pointsCurveY);
            _alLinesWithSymbols.Add(pointsCurveZ);
            _alLinesWithSymbols.Add(pointsCurveAUCX);
            _alLinesWithSymbols.Add(pointsCurveAUCY);
            _alLinesWithSymbols.Add(pointsCurveAUCZ);
            _alLinesWithSymbols.Add(pointsCurveAUCXYZ);

            pointsCurveX.Line.IsVisible = false;
            pointsCurveY.Line.IsVisible = false;
            pointsCurveZ.Line.IsVisible = false;
            pointsCurveAUCX.Line.IsVisible = false;
            pointsCurveAUCY.Line.IsVisible = false;
            pointsCurveAUCZ.Line.IsVisible = false;
            pointsCurveAUCXYZ.Line.IsVisible = false;



            //paneOrders.Add("Columbia " + channel + " " + location, paneOrder);
            WidenDatesIfNeeded(listX);
        }

        #endregion RTI Graph


        #region GPS Graph
        private void CreateGPSDeviceGraph(GraphPane gp, string filePath)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filePath);

            PointPairList listSpeed = new PointPairList();
            PointPairList listAltitude = new PointPairList();
  

            //for each row, add values to PointPairLists
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    //expecting values in format: UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2kg,OxyconRER
                    string[] split = values[i].Split(',');

                    if (split.Length > 4) //TimeStamp + at least one data value
                    {
                        #region TIMESTAMP - X VALUE
                        DateTime dt = ConvertUNIXDatTime(Convert.ToDouble(split[0]));//UnixTimeStamp, Column 1/A
                        //DateTime dt = DateTime.Parse(split[1]);//TimeStamp, Column 2/B
                        double x = (double)new XDate(dt);//x value is numeric representation of TimeStamp
                        #endregion

                        #region DATA VALUE - Y VALUE
                        double y = 0; string label = "";

                        #region GPSSpeed
                        if ((split.Length > 4) && (split[4].Length > 0))
                        {
                            y = Convert.ToDouble(split[4]);//Column 3/C
                            if (_isUsingLabels)
                            {
                                label = String.Format("GPS Speed\n{0} {1}", dt.ToLongTimeString(), y);
                                listSpeed.Add(x, y, label);
                            }
                            else listSpeed.Add(x, y);
                        }
                        #endregion

                        #region GPSAltitude
                        if ((split.Length > 5) && (split[5].Length > 0))
                        {
                            y = Convert.ToDouble(split[5]);//Column 4/D
                            if (_isUsingLabels)
                            {
                                label = String.Format("GPS Altitude\n{0} {1}", dt.ToLongTimeString(), y);
                                listAltitude.Add(x, y, label);
                            }
                            else listAltitude.Add(x, y);
                        }
                        #endregion                       

                        #endregion

                    }

                }
                catch { }
            }

            #region SET DISPLAY PROPERTIES FOR LINES
            LineItem pointsCurve;

            #region ON Y-AXIS
            #region Speed
            pointsCurve = gp.AddCurve("GPS Speed", listSpeed, Color.Red, SymbolType.Circle);
            pointsCurve.Symbol.Fill = new Fill(Color.Red);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "Speed";
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region Altitude
            pointsCurve = gp.AddCurve("GPS Altitude", listAltitude, Color.GreenYellow, SymbolType.Square);
            pointsCurve.Symbol.Fill = new Fill(Color.GreenYellow);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "Altitude";
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

 

            #endregion ON Y-AXIS

            #endregion SET DISPLAY PROPERTIES FOR LINES
            //if time-dates for lines include dates not previously graphed, widen range
            WidenDatesIfNeeded(listSpeed); 
        }

        #endregion GPS Graph

        #region Actigraph
        Hashtable lineSegments = new Hashtable();
        private void CreateActigraphLineSegments(GraphPane gp)
        {
            foreach (DictionaryEntry entry in lineSegments)      
            {
               
                LineSegment l = (LineSegment) entry.Value;
                if ((l.Y1 > 0) || (l.Y2 > 0))
                {
                    PointPairList listCounts = new PointPairList();
                    listCounts.Add(l.X1, l.Y1);
                    listCounts.Add(l.X2, l.Y2);

                    LineItem pointsCurve = gp.AddCurve("", listCounts, Color.GreenYellow);
                    pointsCurve.Symbol.IsVisible = false;
                    pointsCurve.Symbol.Size = 1F;
                    pointsCurve.Line.IsVisible = true;
                }
            }
            
        }
        private void CreateActigraphGraph(GraphPane gp, string filePath, int id)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filePath);
            Color[] colors = new Color[9] { Color.Red, Color.YellowGreen, Color.Beige, Color.Aqua, Color.Violet,Color.Bisque,Color.Cyan,Color.DarkOrange,Color.Khaki };
            PointPairList listCountsX = new PointPairList();
            PointPairList listCountsY = new PointPairList();
            PointPairList listCountsZ = new PointPairList();
                      //for each row, add values to PointPairLists
            int numAxes = 0;
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    //expecting values in format: UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2kg,OxyconRER
                    string[] split = values[i].Split(',');

                    if (split.Length > 2) //TimeStamp + at least one data value
                    {
                        #region TIMESTAMP - X VALUE
                        DateTime dt = ConvertUNIXDatTime(Convert.ToDouble(split[0]));//UnixTimeStamp, Column 1/A
                        //DateTime dt = DateTime.Parse(split[1]);//TimeStamp, Column 2/B
                        double x = (double)new XDate(dt);//x value is numeric representation of TimeStamp
                        #endregion

                        #region DATA VALUE - Y VALUE
                        double y = 0; string label = "";

                        #region Actigraph
                        if ((split.Length > 2) && (split[2].Length > 0))
                        {
                            y = Convert.ToDouble(split[2]);//Column 3/C
                            if (_isUsingLabels)
                            {
                                label = String.Format("Actigraph "+(id+1)+" AC_X\n{0} {1}", dt.ToLongTimeString(), y);
                                listCountsX.Add(x, y, label);
                            }
                            else listCountsX.Add(x, y);
                            numAxes = 1;
                        }

                        if ((split.Length > 3) && (split[3].Length > 0))
                        {
                            y = Convert.ToDouble(split[3]);//Column 3/C
                            if (_isUsingLabels)
                            {
                                label = String.Format("Actigraph " + (id + 1) + " AC_Y\n{0} {1}", dt.ToLongTimeString(), y);
                                listCountsY.Add(x, y, label);
                            }
                            else listCountsY.Add(x, y);
                            numAxes = 2;
                        }

                        if ((split.Length > 4) && (split[4].Length > 0))
                        {
                            y = Convert.ToDouble(split[4]);//Column 3/C
                            if (_isUsingLabels)
                            {
                                label = String.Format("Actigraph " + (id + 1) + " AC_Z\n{0} {1}", dt.ToLongTimeString(), y);
                                listCountsZ.Add(x, y, label);
                            }
                            else listCountsZ.Add(x, y);
                            numAxes = 3;
                        }

                        #endregion

                        #endregion

                    }
                    

                }
                catch { }
            }


            #region SET DISPLAY PROPERTIES FOR LINES
            LineItem pointsCurve;

            #region ON Y-AXIS
            #region 
            if (numAxes >= 1)
            {
                pointsCurve = gp.AddCurve("Actigraph " + id + " X", listCountsX, colors[id % colors.Length], SymbolType.Circle);
                pointsCurve.Symbol.Fill = new Fill(colors[(id * 3) % colors.Length]);
                if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
                pointsCurve.Line.IsVisible = false;
                pointsCurve.Tag = "AC" + (id + 1);
                _alLinesWithSymbols.Add(pointsCurve);
            }

            if (numAxes >= 2)
            {
                pointsCurve = gp.AddCurve("Actigraph " + id + " Y", listCountsY, colors[id % colors.Length], SymbolType.Circle);
                pointsCurve.Symbol.Fill = new Fill(colors[((id * 3) % colors.Length) + 1]);

                if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
                pointsCurve.Line.IsVisible = false;
                pointsCurve.Tag = "AC" + (id + 1);
                _alLinesWithSymbols.Add(pointsCurve);
            }

            if (numAxes >= 3)
            {
                pointsCurve = gp.AddCurve("Actigraph " + id + " Z", listCountsZ, colors[id % colors.Length], SymbolType.Circle);
                pointsCurve.Symbol.Fill = new Fill(colors[((id * 3) % colors.Length) + 1]);

                if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
                pointsCurve.Line.IsVisible = false;
                pointsCurve.Tag = "AC" + (id + 1);
                _alLinesWithSymbols.Add(pointsCurve);
            }

            
            #endregion
            #endregion
            #endregion
            WidenDatesIfNeeded(listCountsX);    
        }
        #endregion Actigraph

        #region Zephyr
        private void CreateZephyrGraph(GraphPane gp, string filePath)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filePath);

            PointPairList listHR = new PointPairList();
            PointPairList listRR = new PointPairList();
            PointPairList listACT = new PointPairList();

            //for each row, add values to PointPairLists
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    //expecting values in format: UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2kg,OxyconRER
                    string[] split = values[i].Split(',');

                    if (split.Length > 2) //TimeStamp + at least one data value
                    {
                        #region TIMESTAMP - X VALUE
                        DateTime dt = ConvertUNIXDatTime(Convert.ToDouble(split[0]));//UnixTimeStamp, Column 1/A
                        //DateTime dt = DateTime.Parse(split[1]);//TimeStamp, Column 2/B
                        double x = (double)new XDate(dt);//x value is numeric representation of TimeStamp
                        #endregion

                        #region DATA VALUE - Y VALUE
                        double y = 0; string label = "";

                        #region ZephyrHR
                        if ((split.Length > 2) && (split[2].Length > 0))
                        {
                            y = Convert.ToDouble(split[2]);//Column 3/C
                            if (_isUsingLabels)
                            {
                                label = String.Format("Zephyr HR\n{0} {1}", dt.ToLongTimeString(), y);
                                listHR.Add(x, y, label);
                            }
                            else listHR.Add(x, y);
                        }
                        #endregion

                        #region ZephyrRR
                        if ((split.Length > 6) && (split[6].Length > 0))
                        {
                            y = Convert.ToDouble(split[6]);//Column 4/D
                            if (_isUsingLabels)
                            {
                                label = String.Format("Zephyr RR\n{0} {1}", dt.ToLongTimeString(), y);
                                listRR.Add(x, y, label);
                            }
                            else listRR.Add(x, y);
                        }
                        #endregion

                        #region ZephyrACT
                        if ((split.Length > 10) && (split[10].Length > 0))
                        {
                            y = Convert.ToDouble(split[10]);//Column 5/E
                            if (_isUsingLabels)
                            {
                                label = String.Format("Zephyr ACT\n{0} {1}", dt.ToLongTimeString(), y);
                                listACT.Add(x, y, label);
                            }
                            else listACT.Add(x, y);
                        }
                        #endregion

                        #endregion

                    }

                }
                catch { }
            }

            #region SET DISPLAY PROPERTIES FOR LINES
            LineItem pointsCurve;

            #region ON Y-AXIS 
            #region HR
            pointsCurve = gp.AddCurve("Zephyr HR", listHR, Color.Red, SymbolType.Circle);
            pointsCurve.Symbol.Fill = new Fill(Color.Red);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "HR";
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region BF
            pointsCurve = gp.AddCurve("Zephyr RR", listRR, Color.GreenYellow, SymbolType.Square);
            pointsCurve.Symbol.Fill = new Fill(Color.GreenYellow);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "RR";
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region V02kg
            pointsCurve = gp.AddCurve("Zephyr Activity", listACT, Color.Orchid, SymbolType.TriangleDown);
            pointsCurve.Symbol.Fill = new Fill(Color.Orchid);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "Activity";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #endregion ON Y-AXIS

            #endregion SET DISPLAY PROPERTIES FOR LINES
            //if time-dates for lines include dates not previously graphed, widen range
            WidenDatesIfNeeded(listHR);    
        }
        #endregion Zephyr

        #region Sensewear
        private void CreateSensewearGraph(GraphPane gp, string filePath)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filePath);

            PointPairList listACT = new PointPairList();

            //for each row, add values to PointPairLists
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    //expecting values in format: UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2kg,OxyconRER
                    string[] split = values[i].Split(',');

                    if (split.Length > 2) //TimeStamp + at least one data value
                    {
                        #region TIMESTAMP - X VALUE
                        DateTime dt = ConvertUNIXDatTime(Convert.ToDouble(split[0]));//UnixTimeStamp, Column 1/A
                        //DateTime dt = DateTime.Parse(split[1]);//TimeStamp, Column 2/B
                        double x = (double)new XDate(dt);//x value is numeric representation of TimeStamp
                        #endregion

                        #region DATA VALUE - Y VALUE
                        double y = 0; string label = "";


                        #region ZephyrACT
                        if ((split.Length > 5) && (split[5].Length > 0))
                        {
                            y = Convert.ToDouble(split[5]);//Column 5/E
                            if (_isUsingLabels)
                            {
                                label = String.Format("Sensewear ACT\n{0} {1}", dt.ToLongTimeString(), y);
                                listACT.Add(x, y, label);
                            }
                            else listACT.Add(x, y);
                        }
                        #endregion

                        #endregion

                    }

                }
                catch { }
            }

            #region SET DISPLAY PROPERTIES FOR LINES
            LineItem pointsCurve;

            #region ON Y-AXIS

            #region ACT
            pointsCurve = gp.AddCurve("Sensewear Activity", listACT, Color.Orchid, SymbolType.TriangleDown);
            pointsCurve.Symbol.Fill = new Fill(Color.Orchid);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "Activity";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #endregion ON Y-AXIS

            #endregion SET DISPLAY PROPERTIES FOR LINES
            //if time-dates for lines include dates not previously graphed, widen range
            WidenDatesIfNeeded(listACT);
        }
        #endregion Sensewear
        //ADD_GRAPH STEP 2
        #region Oxycon
        private void CreateOxyconGraph(GraphPane gp, string filePath)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filePath);

            //One PointPairList for each data column to graph
            //Each of these represents a separate line
            PointPairList listHR = new PointPairList();
            PointPairList listBF = new PointPairList();
            PointPairList listVE = new PointPairList();
            PointPairList listVO2kg = new PointPairList();
            PointPairList listRER = new PointPairList();
            PointPairList listMET = new PointPairList();
            PointPairList listEE = new PointPairList();

            //for each row, add values to PointPairLists
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    //expecting values in format: UnixTimeStamp,TimeStamp,OxyconHR,OxyconBF,OxyconVE,OxyconVO2kg,OxyconRER
                    string[] split = values[i].Split(',');

                    if (split.Length > 2) //TimeStamp + at least one data value
                    {
                        #region TIMESTAMP - X VALUE
                        DateTime dt = ConvertUNIXDatTime(Convert.ToDouble(split[0]));//UnixTimeStamp, Column 1/A
                        //DateTime dt = DateTime.Parse(split[1]);//TimeStamp, Column 2/B
                        double x = (double)new XDate(dt);//x value is numeric representation of TimeStamp
                        #endregion

                        #region DATA VALUE - Y VALUE
                        double y = 0; string label = "";

                        #region OxyconHR
                        if ((split.Length > 2) && (split[2].Length > 0))
                        {
                            y = Convert.ToDouble(split[2]);//Column 3/C
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon HR\n{0} {1}", dt.ToLongTimeString(), y);
                                listHR.Add(x, y, label);
                            }
                            else listHR.Add(x, y);
                        }
                        #endregion

                        #region OxyconBF
                        if ((split.Length > 3) && (split[3].Length > 0))
                        {
                            y = Convert.ToDouble(split[3]);//Column 4/D
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon BF\n{0} {1}", dt.ToLongTimeString(), y);
                                listBF.Add(x, y, label);
                            }
                            else listBF.Add(x, y);
                        }
                        #endregion

                        #region OxyconVE
                        if ((split.Length > 4) && (split[4].Length > 0))
                        {
                            y = Convert.ToDouble(split[4]);//Column 5/E
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon VE\n{0} {1}", dt.ToLongTimeString(), y);
                                listVE.Add(x, y, label);
                            }
                            else listVE.Add(x, y);
                        }
                        #endregion

                        #region OxyconV02kg
                        if ((split.Length > 6) && (split[6].Length > 0))
                        {
                            y = Convert.ToDouble(split[6]);//Column 6/F
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon VO2kg\n{0} {1}", dt.ToLongTimeString(), y);
                                listVO2kg.Add(x, y, label);
                            }
                            else listVO2kg.Add(x, y);
                        }
                        #endregion



                        #region OxyconMET
                        if ((split.Length > 7) && (split[7].Length > 0))
                        {
                            y = Convert.ToDouble(split[7])*10000.0;//Column 7/G
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon MET\n{0} {1}", dt.ToLongTimeString(), Convert.ToDouble(split[7]));
                                listMET.Add(x, y, label);
                            }
                            else listMET.Add(x, y);
                        }
                        #endregion


                        #region OxyconEE
                        if ((split.Length > 8) && (split[8].Length > 0))
                        {
                            y = Convert.ToDouble(split[8]);//Column 7/G
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon EE\n{0} {1}", dt.ToLongTimeString(), Convert.ToDouble(split[8]));
                                listEE.Add(x, y, label);
                            }
                            else listEE.Add(x, y);
                        }
                        #endregion

                        #region OxyconRER
                        if ((split.Length > 9) && (split[9].Length > 0))
                        {
                            y = Convert.ToDouble(split[9]);//Column 7/G
                            if (_isUsingLabels)
                            {
                                label = String.Format("Oxycon RER\n{0} {1}", dt.ToLongTimeString(), y);
                                listRER.Add(x, y, label);
                            }
                            else listRER.Add(x, y);
                        }
                        #endregion
                        #endregion

                    }

                }
                catch { }
            }

            #region SET DISPLAY PROPERTIES FOR LINES
            LineItem pointsCurve;

            #region ON Y-AXIS 1 (left-side)
            #region HR
            pointsCurve = gp.AddCurve("Oxycon HR", listHR, Color.Red, SymbolType.Circle);
            pointsCurve.Symbol.Fill = new Fill(Color.Red);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "HR";
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region BF
            pointsCurve = gp.AddCurve("Oxycon BF", listBF, Color.GreenYellow, SymbolType.Square);
            pointsCurve.Symbol.Fill = new Fill(Color.GreenYellow);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "BF";
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion
            #endregion

            #region ON Y-AXIS 2 - right-side
            #region VE
            pointsCurve = gp.AddCurve("Oxycon VE", listVE, Color.Orange, SymbolType.Diamond);
            pointsCurve.Symbol.Fill = new Fill(Color.Orange);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "VE";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region V02kg
            pointsCurve = gp.AddCurve("Oxycon VO2kg", listVO2kg, Color.Orchid, SymbolType.TriangleDown);
            pointsCurve.Symbol.Fill = new Fill(Color.Orchid);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "V02kg";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region RER
            pointsCurve = gp.AddCurve("Oxycon RER", listRER, Color.Navy, SymbolType.Triangle);
            pointsCurve.Symbol.Fill = new Fill(Color.Navy);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "RER";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion

            #region MET
            pointsCurve = gp.AddCurve("Oxycon MET", listMET, Color.Aqua, SymbolType.Triangle);
            pointsCurve.Symbol.Fill = new Fill(Color.Aqua);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "MET";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion


            #region EE
            pointsCurve = gp.AddCurve("Oxycon EE", listEE, Color.Black, SymbolType.Triangle);
            pointsCurve.Symbol.Fill = new Fill(Color.Black);
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Tag = "EE";
            pointsCurve.IsY2Axis = true;
            _alLinesWithSymbols.Add(pointsCurve);
            #endregion
            #endregion

            #endregion

            //if time-dates for lines include dates not previously graphed, widen range
            WidenDatesIfNeeded(listHR);            

        }
        #endregion

        #region GPS
        private void CreateGPSGraph(GraphPane gp, string filepath)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filepath);
            PointPairList list_NO = new PointPairList();
            PointPairList list_HAS = new PointPairList();

            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    DateTime dt = DateTime.Parse(split[0]);
                    double x = (double)new XDate(dt);
                    if (split[1].Equals("NOT_AVAILABLE"))
                        list_NO.Add(x, 200, dt.ToLongTimeString() + " GPS NOT AVAILABLE");
                    else list_HAS.Add(x, 205, dt.ToLongTimeString() + " " + split[1] + ", " + split[2]);
                }
                catch { }
            }


            LineItem pointsCurveNo = gp.AddCurve("GPS", list_NO, Color.Gray, SymbolType.Square);
            pointsCurveNo.Line.IsVisible = false;
            if (!_isAdaptingPointSize) pointsCurveNo.Symbol.Size = 1F;
            _alLinesWithSymbols.Add(pointsCurveNo);
            LineItem pointsCurveHas = gp.AddCurve("GPS", list_HAS, Color.Magenta, SymbolType.Triangle);
            pointsCurveHas.Line.IsVisible = false;
            if (!_isAdaptingPointSize) pointsCurveHas.Symbol.Size = 1F;
            pointsCurveHas.Symbol.Fill = new Fill(Color.Magenta);
            _alLinesWithSymbols.Add(pointsCurveHas);
            WidenDatesIfNeeded(list_NO);
        }
        private void CreatePOIGraph(GraphPane gp, string filepath)
        {
            PointPairList list = new PointPairList();
            string[] values = FileReadWrite.ReadLinesFromFile(filepath);
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    double x = (double)new XDate(DateTime.Parse(split[0]));
                    string tag = "";
                    split = values[i].Split(':', '(');
                    for (int j = 5; j < split.Length; j += 2)
                    {
                        tag += split[j] + "\n";
                    }                   

                    list.Add(x, 200, tag);
                }
                catch { }
            }

            LineItem pointsCurve = gp.AddCurve("POI", list, Color.Black, SymbolType.Star);
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Symbol.Fill = new Fill(Color.Black);
            pointsCurve.Symbol.Size = 6F;
            if (!_isAdaptingPointSize) pointsCurve.Symbol.Size = 1F;
            _alLinesWithSymbols.Add(pointsCurve);
            WidenDatesIfNeeded(list);
        }
        #endregion

        #region ANNOTATION LABELS
        private void CreateDiaryGraph(GraphPane gp, string filepath, string title, int y)
        {
            gp.BarSettings.Base = BarBase.Y;
            gp.BarSettings.Type = BarType.Overlay;

            PointPairList labelList = new PointPairList();

            string[] values = FileReadWrite.ReadLinesFromFile(filepath);
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    string[] datetime = split[0].Split(' ');
                    string[] startDate = datetime[0].Split('-');
                    string[] startTime = datetime[1].Split('-')[0].Split(':');

                    DateTime dtStart = new DateTime(Convert.ToInt32(startDate[0]), Convert.ToInt32(startDate[1]), Convert.ToInt32(startDate[2]), Convert.ToInt32(startTime[0]), Convert.ToInt32(startTime[1]), Convert.ToInt32(startTime[2]));//DateTime.Parse(split[0]);
                    double startx = (double)new XDate(dtStart);
                    if (split[1].Length > 0)
                    {
                        #region END DATE
                        string[] enddatetime = split[1].Split(' ');
                        string[] endDate = enddatetime[0].Split('-');
                        string[] endTime = enddatetime[1].Split('-')[0].Split(':');

                        DateTime dtEnd = new DateTime(Convert.ToInt32(endDate[0]), Convert.ToInt32(endDate[1]), Convert.ToInt32(endDate[2]), Convert.ToInt32(endTime[0]), Convert.ToInt32(endTime[1]), Convert.ToInt32(endTime[2]));//DateTime.Parse(split[0]);
                        //DateTime dtEnd = DateTime.Parse(split[1]);
                        double endx = (double)new XDate(dtEnd);
                        #endregion

                        #region COLOR OF BAR
                        string color = "black";
                        bool isSolid = false;
                        if ((split.Length > 2) && (split[2].Length > 0))
                        {
                            color = split[2];
                            isSolid = true;
                        }
                        #endregion
                        

                        #region LABEL AND POINT
                        string label = "";
                        for (int c = 3; c < split.Length; c++)
                        {
                            label += split[c].Replace("_", ", ").Replace("-", " ").Trim(',',' ') + "\n ";
                        }
                        labelList = new PointPairList();
                        labelList.Add(endx, y, startx, String.Format("{3} {0}-{1}\n,{2}",dtStart.ToShortTimeString(),dtEnd.ToShortTimeString(),label,title));
                        #endregion

                        #region ADD BAR
                        HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, Color.FromName(color));
                        if (isSolid) myBar.Bar.Fill.Type = FillType.Solid;
                        else myBar.Bar.Fill.Type = FillType.None;
                        #endregion
                    }
                }
                catch { }
            }




        }

        #region commented
        /*
        private void CreateDiaryGraph(GraphPane gp, string filepath,string filepath_colors, string title, int y, string type)
        {
            gp.BarSettings.Base = BarBase.Y;
            gp.BarSettings.Type = BarType.Overlay;

            PointPairList labelList = new PointPairList();

            string[] values = FileReadWrite.ReadLinesFromFile(filepath);


            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    string[] datetime = split[0].Split(' ');
                    string[] startDate = datetime[0].Split('-');
                    string[] startTime = datetime[1].Split('-')[0].Split(':');

                    DateTime dtStart = new DateTime(Convert.ToInt32(startDate[0]), Convert.ToInt32(startDate[1]), Convert.ToInt32(startDate[2]), Convert.ToInt32(startTime[0]), Convert.ToInt32(startTime[1]), Convert.ToInt32(startTime[2]));//DateTime.Parse(split[0]);
                    double startx = (double)new XDate(dtStart);
                    if (split[1].Length > 0)
                    {
                        #region END DATE
                        string[] enddatetime = split[1].Split(' ');
                        string[] endDate = enddatetime[0].Split('-');
                        string[] endTime = enddatetime[1].Split('-')[0].Split(':');

                        DateTime dtEnd = new DateTime(Convert.ToInt32(endDate[0]), Convert.ToInt32(endDate[1]), Convert.ToInt32(endDate[2]), Convert.ToInt32(endTime[0]), Convert.ToInt32(endTime[1]), Convert.ToInt32(endTime[2]));//DateTime.Parse(split[0]);
                        //DateTime dtEnd = DateTime.Parse(split[1]);
                        double endx = (double)new XDate(dtEnd);
                        #endregion

                        #region COLOR OF BAR
                        string color = "black";
                        bool isSolid = false;
                        if ((split.Length > 2) && (split[2].Length > 0))
                        {
                            color = split[2];
                            isSolid = true;
                        }
                        #endregion
                        

                        #region LABEL AND POINT
                        string label = "";
                        for (int c = 3; c < split.Length; c++)
                        {
                            label += split[c].Replace("_", ", ").Replace("-", " ").Trim(',',' ') + "\n ";
                        }
                        labelList = new PointPairList();
                        labelList.Add(endx, y, startx, String.Format("{3} {0}-{1}\n,{2}",dtStart.ToShortTimeString(),dtEnd.ToShortTimeString(),label,title));
                        #endregion

                        #region ADD BAR
                        HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, Color.FromName(color));
                        if (isSolid) myBar.Bar.Fill.Type = FillType.Solid;
                        else myBar.Bar.Fill.Type = FillType.None;
                        #endregion
                    }
                }
                catch { }
            }

        }
  */
        #endregion


        #region labels colors on bar
        
        private void CreateDiaryGraph(GraphPane gp, string filepath, string dirpath_colors, 
                                      string title, int yoffset, string type)
        {
            gp.BarSettings.Base = BarBase.Y;
            gp.BarSettings.ClusterScaleWidth = 200.0;
            gp.BarSettings.Type = BarType.Overlay;

            PointPairList labelList = new PointPairList();
            string[] values = FileReadWrite.ReadLinesFromFile(filepath);

            bool is_category_1 = false;
            bool is_category_2 = false;

            string[] lines_read = null;
            string[] label_color = null;
            BindingList<string[]> labels_color_list_1 = null; 
            BindingList<string[]> labels_color_list_2 = null; 



            #region read colors files

            if (type.CompareTo("posture") == 0)
            {
                is_category_1 = true;

                if (File.Exists(dirpath_colors + "ActivityLabelsColors_1.csv"))
                {
                    labels_color_list_1 = new BindingList<string[]>();
                    lines_read = FileReadWrite.ReadLinesFromFile(dirpath_colors + "ActivityLabelsColors_1.csv");

                    foreach (string line in lines_read)
                    {
                        label_color = line.Split(',');
                        labels_color_list_1.Add(label_color);
                    }
                }
            }
            else if (type.CompareTo("activity") == 0)
            {
                is_category_2 = true;

                if (File.Exists(dirpath_colors + "ActivityLabelsColors_2.csv"))
                {
                    labels_color_list_2 = new BindingList<string[]>();
                    lines_read = FileReadWrite.ReadLinesFromFile(dirpath_colors + "ActivityLabelsColors_2.csv");

                    foreach (string line in lines_read)
                    {
                        label_color = line.Split(',');
                        labels_color_list_2.Add(label_color);
                    }
                }
            }

            #endregion


            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    string[] datetime = split[0].Split(' ');
                    string[] startDate = datetime[0].Split('-');
                    string[] startTime = datetime[1].Split('-')[0].Split(':');

                    DateTime dtStart = new DateTime(Convert.ToInt32(startDate[0]), Convert.ToInt32(startDate[1]), Convert.ToInt32(startDate[2]), Convert.ToInt32(startTime[0]), Convert.ToInt32(startTime[1]), Convert.ToInt32(startTime[2]));//DateTime.Parse(split[0]);
                    double startx = (double)new XDate(dtStart);
                    if (split[1].Length > 0)
                    {
                        #region END DATE
                        string[] enddatetime = split[1].Split(' ');
                        string[] endDate = enddatetime[0].Split('-');
                        string[] endTime = enddatetime[1].Split('-')[0].Split(':');

                        DateTime dtEnd = new DateTime(Convert.ToInt32(endDate[0]), Convert.ToInt32(endDate[1]), Convert.ToInt32(endDate[2]), Convert.ToInt32(endTime[0]), Convert.ToInt32(endTime[1]), Convert.ToInt32(endTime[2]));//DateTime.Parse(split[0]);
                        //DateTime dtEnd = DateTime.Parse(split[1]);
                        double endx = (double)new XDate(dtEnd);
                        #endregion



                        #region COLOR OF BAR
                            string color = "white";
                            bool isSolid = false;

                            string clabel = "";


                            #region Match color with label 
                            
                            //determine colors according to the graph type
                            if ( is_category_1 )
                            {
                                //if log contains postures
                                if ((split.Length > 2) && (split[3].Length > 0))
                                {
                                    clabel = split[3];

                                    for (int j = 0; j < labels_color_list_1.Count; j++)
                                    {
                                        if (labels_color_list_1[j][1].CompareTo(clabel) == 0)
                                        {
                                            color = labels_color_list_1[j][3];
                                            isSolid = true;
                                            break;
                                        }
                                    }
                                }
                            }
                            else if (is_category_2)
                            {
                                //if log contains activities
                                if ((split.Length > 2) && (split[4].Length > 0))
                                {
                                    clabel = split[4];

                                    for (int j = 0; j < labels_color_list_2.Count; j++)
                                    {
                                        if (labels_color_list_2[j][1].CompareTo(clabel) == 0)
                                        {
                                            color = labels_color_list_2[j][3];
                                            isSolid = true;
                                            break;
                                        }
                                    }
                                }

                            }
                            
                            #endregion


                            #region commented
                            /*if ((split.Length > 2) && (split[2].Length > 0))
                            {
                                color = split[2];
                                isSolid = true;
                            }
                            */
                            #endregion


                        #endregion Color of bar


                        #region LABEL AND POINT

                        string label = "";
                        for (int c = 3; c < split.Length; c++)
                        {
                            label += split[c].Replace("_", ", ").Replace("-", " ").Trim(',',' ') + "\n ";
                        }

                        labelList = new PointPairList();
                        labelList.Add(endx, yoffset, startx, String.Format("{3}: {0}  -  {1}\n {2}",dtStart.ToLongTimeString(),dtEnd.ToLongTimeString(),label,title));
 
                        #endregion

                        #region ADD BAR


                        //HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, Color.FromName(color
                        HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, Color.FromArgb(Int32.Parse(color)) );
                        

                        if (isSolid) myBar.Bar.Fill.Type = FillType.Solid;
                        else myBar.Bar.Fill.Type = FillType.None;

                        #endregion
                    }
                }
                catch { }
            }




        }
        
       #endregion


        #endregion



        #region PHOTOS and SURVEYS
        private void CreatePhotoGraph(GraphPane gp, string filepath, string imagedir)
        {
            PointPairList list_Photo = new PointPairList();
            string[] values = FileReadWrite.ReadLinesFromFile(filepath);
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    double x = (double)new XDate(DateTime.Parse(split[0]));
                    list_Photo.Add(x, 25, split[2]+","+Path.Combine(imagedir,split[1]));
                }
                catch { }
            }

            LineItem pointsCurve = gp.AddCurve("photos", list_Photo, Color.Black, SymbolType.Square);
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Symbol.Fill = new Fill(Color.LightGray);
            pointsCurve.Symbol.Size = 10F;

            WidenDatesIfNeeded(list_Photo);
        }

        private void CreateSurveyGraph(GraphPane gp, string filepath)
        {
            PointPairList list = new PointPairList();
            string[] values = FileReadWrite.ReadLinesFromFile(filepath);
            for (int i = 0; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    double x = (double)new XDate(DateTime.Parse(split[0]));
                    list.Add(x, 20, split[1].Replace(";","\n"));
                }
                catch { }
            }

            LineItem pointsCurve = gp.AddCurve("surveys", list, Color.Purple, SymbolType.Diamond);
            pointsCurve.Line.IsVisible = false;
            pointsCurve.Symbol.Fill = new Fill(Color.Plum);
            pointsCurve.Symbol.Size = 10F;

            WidenDatesIfNeeded(list);
        }

        #endregion

        #region ANNOTATOR-CLASSIFIER
        private void CreateAgreementGraph(GraphPane gp, string[] files)
        {
            DateTime dtLastDate = DateTime.Now;
            for (int f = 0; f < files.Length; f++)
            {
                DateTime dt = dtLastDate.AddMinutes(5);

                string[] values = FileReadWrite.ReadLinesFromFile(files[f]);
                string name = Path.GetFileNameWithoutExtension(files[f]).Replace("average-a_", "");

                PointPairList listAnnotator = new PointPairList();
                PointPairList listClassifier = new PointPairList();
                PointPairList listDifference = new PointPairList();
                ArrayList alAgree_lists = new ArrayList();
                ArrayList alAgree_values = new ArrayList();
                double lastDifference = 0;

                //PointPairList listAgree = new PointPairList();
                //PointPairList listDisagree = new PointPairList();
                //PointPairList listConfusion = new PointPairList();
                double yClass = 2.3, yAnnotate = 1.1;
                for (int i = 0; i < values.Length; i++)
                {
                    try
                    {
                        string[] split = values[i].Split(',');
                        if (split.Length > 2)
                        {
                            
                            int msec = Convert.ToInt32(split[0]);
                            dtLastDate = dt.AddMilliseconds(msec * 400);
                            double x = (double)new XDate(dtLastDate);

                            #region BLOCK GRAPH ANNOTATOR
                            double yA = Convert.ToDouble(split[1]) + 1.1;
                            if (yA != yAnnotate)
                            {
                                listAnnotator.Add(x, yAnnotate);
                                yAnnotate = yA;
                            }
                            listAnnotator.Add(x, yA);
                            yA -= 1.1;
                            #endregion

                            #region BLOCK GRAPH CLASSIFIER
                            double yC = Convert.ToDouble(split[2]) + 2.3;
                            if (yC != yClass)
                            {
                                listClassifier.Add(x, yClass);
                                yClass = yC;
                            }
                            listClassifier.Add(x, yC);
                            yC -= 2.3;
                            #endregion

                            double difference = yC - yA;
                            if (!alAgree_values.Contains(difference))
                            {
                                alAgree_values.Add(difference);
                                alAgree_lists.Add(new PointPairList());
                            }
                            int index = alAgree_values.IndexOf(difference);

                            if (difference != lastDifference)
                            {
                                listDifference.Add(x, lastDifference);
                                int lastindex = alAgree_values.IndexOf(lastDifference);
                                ((PointPairList)alAgree_lists[lastindex]).Add(x, 1);
                                ((PointPairList)alAgree_lists[index]).Add(x, 0);
                                lastDifference = difference;
                            }

                            
                            for (int a = 0; a < alAgree_lists.Count; a++)
                            {
                                if (a != index)
                                    ((PointPairList)alAgree_lists[a]).Add(x, 0);
                            }
                            ((PointPairList)alAgree_lists[index]).Add(x, 1);

                            listDifference.Add(x, difference);

                            //double nyA = 0, nyD = 0, nyC = 0;
                            //if (split[1] == split[2])
                            //{
                            //    if (split[2] == split[3])
                            //        nyA = 3;
                            //    else
                            //        nyD = 3;

                            //}
                            //else nyC = 3;

                            //if (yA != nyA) listAgree.Add(x, yA);
                            //if (yC != nyC) listConfusion.Add(x, yC);
                            //if (yD != nyD) listDisagree.Add(x, yD);
                            //listAgree.Add(x, nyA);
                            //listDisagree.Add(x, nyD);
                            //listConfusion.Add(x, nyC);
                            //yA = nyA; yC = nyC; yD = nyD;

                        }

                    }
                    catch { }
                }
                AddHorizontalText(gp, name, (double)new XDate(dt), Color.Black);
                LineItem lineCurve1 = gp.AddCurve("Annotator 1 " + name, listAnnotator, Color.Green, SymbolType.Default);
                lineCurve1.Symbol.IsVisible = false;
                lineCurve1.Line.IsVisible = true;
                _alLinesWithSymbols.Add(lineCurve1);

                AddVerticalText(gp, "Annotators", 1.1F, Color.Green);


                LineItem lineCurveC = gp.AddCurve("Classifier " + name, listClassifier, Color.Blue, SymbolType.Default);
                lineCurveC.Line.IsVisible = true;
                lineCurveC.Symbol.IsVisible = false;

                AddVerticalText(gp, "Classifier", 2.3F, Color.Blue);

                LineItem lineCurveD = gp.AddCurve("Difference " + name, listDifference, Color.Tomato, SymbolType.Default);
                lineCurveD.Line.IsVisible = true;
                lineCurveD.Line.Width = 0.5F;
                lineCurveD.Symbol.IsVisible = false;
                lineCurveD.Line.Fill = new Fill(Color.Tomato);

                AddVerticalText(gp, "Over\nestimate", 0, Color.Tomato);
                AddVerticalText(gp, "Under\nestimate", -1.0F, Color.Tomato);


                //for (int a = 0; a < alAgree_lists.Count; a++)
                //{
                //    Color fillColor = Color.Yellow;
                //    double diff = ((double)alAgree_values[a]);
                //    if (diff != 0)
                //    {
                //        int percent = Convert.ToInt32(Math.Round((1.1 - Math.Abs(diff)) * 255));
                //        if (diff < 0) fillColor = Color.FromArgb(percent, percent, 255);
                //        else fillColor = Color.FromArgb(255, percent, percent);
                //    }
                //    LineItem lineCurveAgree = gp.AddCurve("Agreement " + name + " " + alAgree_values[a].ToString(), ((PointPairList)alAgree_lists[a]), fillColor, SymbolType.Default);
                //    lineCurveAgree.Line.IsVisible = true;
                //    lineCurveAgree.Symbol.IsVisible = false;
                //    // Fill the area under the curve with a white-red gradient at 45 degrees
                //    lineCurveAgree.Line.Fill = new Fill(fillColor);
                //}

                //LineItem lineCurveAgree = gp.AddCurve("Agreement " + name, listAgree, Color.Green, SymbolType.Default);
                //lineCurveAgree.Line.IsVisible = true;
                //lineCurveAgree.Symbol.IsVisible = false;
                //// Fill the area under the curve with a white-red gradient at 45 degrees
                //lineCurveAgree.Line.Fill = new Fill(Color.White, Color.Green, 45F);

                //LineItem lineCurveDisagree = gp.AddCurve("Disgreement " + name, listDisagree, Color.Red, SymbolType.Default);
                //lineCurveDisagree.Line.IsVisible = true;
                //lineCurveDisagree.Symbol.IsVisible = false;
                //// Fill the area under the curve with a white-red gradient at 45 degrees
                //lineCurveDisagree.Line.Fill = new Fill(Color.White, Color.Red, 45F);

                //LineItem lineCurveConfusion = gp.AddCurve("Confusion " + name, listConfusion, Color.Yellow, SymbolType.Default);
                //lineCurveConfusion.Line.IsVisible = true;
                //lineCurveConfusion.Symbol.IsVisible = false;
                //// Fill the area under the curve with a white-red gradient at 45 degrees
                //lineCurveConfusion.Line.Fill = new Fill(Color.White, Color.Yellow, 45F);



                WidenDatesIfNeeded(listAnnotator);




            }

        }
        private void AddVerticalText(GraphPane gp, string label, double y, Color color)
        {
            TextObj text = new TextObj(label, 0, y);
            // use ChartFraction coordinates so the text is placed relative to the Chart.Rect
            text.Location.CoordinateFrame = CoordType.XChartFractionYScale;
            // rotate the text 90 degrees
            text.FontSpec.Angle = 90.0F;
            text.FontSpec.FontColor = color;
            text.FontSpec.IsBold = true;
            text.FontSpec.Size = 10;
            // Disable the border and background fill options for the text
            text.FontSpec.Border.IsVisible = false;
            text.FontSpec.Fill.IsVisible = false;
            // Align the text such the the Left-Bottom corner is at the specified coordinates
            text.Location.AlignH = AlignH.Left;
            text.Location.AlignV = AlignV.Bottom;
            gp.GraphObjList.Add(text);
        }
        private void AddHorizontalText(GraphPane gp, string label, double x, Color color)
        {
            TextObj text = new TextObj(label, x, 0.05);
            // use ChartFraction coordinates so the text is placed relative to the Chart.Rect
            text.Location.CoordinateFrame = CoordType.XScaleYChartFraction;
            // rotate the text 90 degrees
            text.FontSpec.Angle = 0.0F;
            text.FontSpec.FontColor = color;
            text.FontSpec.IsBold = true;
            text.FontSpec.Size = 10;
            // Disable the border and background fill options for the text
            text.FontSpec.Border.IsVisible = false;
            text.FontSpec.Fill.IsVisible = false;
            // Align the text such the the Left-Bottom corner is at the specified coordinates
            text.Location.AlignH = AlignH.Left;
            text.Location.AlignV = AlignV.Bottom;
            gp.GraphObjList.Add(text);
        }

        #endregion



        #endregion Chart content




        Hashtable paneOrders;
        // Build the Chart
        private void BuildCharts(string path)
        {
            SetGraphPanels();
            string[] files;
            
            paneOrders = new Hashtable();
            int paneOrdering = 1;

            #region DETERMINE WHICH GRAPHS TO DISPLAY BASED ON AVAILABLE FILES
            
            #region ACCELEROMETER GRAPHS
            files = Directory.GetFiles(path + "\\merged\\", "MITes*Raw*");
            for (int i = 0; i < files.Length; i++)
            {
                string channel = "", location = "";
                string[] sensorinfo = Path.GetFileNameWithoutExtension(files[i]).Split('_');
                if (sensorinfo.Length >= 4)
                {
                    channel = sensorinfo[1];
                    location = sensorinfo[3];
                }
                CreateAccelerationGraph(paneOrdering, files[i], channel, location,"MITes","");
                paneOrdering++;
            }
            #endregion


            #region WOCKETS ACCELEROMETER GRAPHS
            if ((Directory.Exists(path + "\\wockets\\")) && (Directory.GetFiles(path + "\\wockets\\").Length > 0))
            {
                CurrentWockets._Configuration = new Wockets.Data.Configuration.WocketsConfiguration();
                CurrentWockets._Configuration.FromXML(path + "\\wockets\\Configuration.xml");
                Wockets.WocketsController wc = new Wockets.WocketsController("", "", "");
                wc.FromXML(path + "\\wockets\\SensorData.xml");
                CurrentWockets._Controller = wc;
                
                files = Directory.GetFiles(path + "\\merged\\", "Wocket*RawMean*");
                for (int i = 0; i < files.Length; i++)
                {
                    string channel = "", location = "";
                    string[] sensorinfo = Path.GetFileNameWithoutExtension(files[i]).Split('_');
                    string mac = "";
                    if (sensorinfo.Length >= 4)
                    {
                        channel = sensorinfo[1];
                        if (wc._Receivers[Convert.ToInt32(channel)] is Wockets.Receivers.RFCOMMReceiver)
                        {
                            mac = ((Wockets.Receivers.RFCOMMReceiver)wc._Receivers[Convert.ToInt32(channel)])._Address;
                            mac = mac.Substring(mac.Length - 2, 2);
                            string loc = wc._Sensors[Convert.ToInt32(channel)]._Location;
                            switch(loc)
                            {
                                case "Dominant Hip":
                                    loc = "DHP";
                                    break;
                                case "Dominant Ankle":
                                    loc = "DAK";
                                    break;
                                case "Dominant Upper Arm":
                                    loc = "DUA";
                                    break;
                                case "Dominant Wrist":
                                    loc = "DW";
                                    break;
                                case "Dominant Thigh":
                                    loc = "DT";
                                    break;
                                default:
                                    loc = "lOC";
                                    break;
                            }

                            mac = "WKT-"+loc+"-" + mac;
                        }
                        else
                            mac = "Internal";
                        location = sensorinfo[3];
                    }
                    CreateAccelerationGraph(paneOrdering, files[i], channel, location, "Wocket", mac);
                    paneOrdering++;
                }
            }
            #endregion


            //ADD_GRAPH STEP 1
            #region OXYCON
            string oxyFile = Path.Combine(path + "\\merged\\", "Oxycon.csv"); 
            if (File.Exists(oxyFile))
            {
                string title ="Oxycon";
                GraphPane ePane = AddPane(title, "Oxycon");
                CreateOxyconGraph(ePane, oxyFile);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }
            #endregion

            #region Zephyr
            string zephyrFile = Path.Combine(path + "\\merged\\", "Zephyr.csv");
            if (File.Exists(zephyrFile))
            {
                string title = "Zephyr";
                GraphPane ePane = AddPane(title, "Zephyr");
                CreateZephyrGraph(ePane, zephyrFile);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }
            #endregion Zephyr

            #region Columbia
            string columbiaFile = Path.Combine(path + "\\merged\\", "Columbia.csv");
                  
            if (File.Exists(columbiaFile))
            {
                string title = "Columbia";
                GraphPane ePane = AddPane(title, "Columbia");
                CreateColumbiaGraph(ePane, columbiaFile);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }      
            #endregion


            #region RTI
            string rtiFile = Path.Combine(path + "\\merged\\", "RTI.csv");

            if (File.Exists(rtiFile))
            {
                string title = "RTI";
                GraphPane ePane = AddPane(title, "RTI");
                CreateRTIGraph(ePane, rtiFile);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }
            #endregion

            #region GPS
            string gpsFile = Path.Combine(path + "\\merged\\", "GPS.csv");

            if (File.Exists(gpsFile))
            {
                string title = "GPS";
                GraphPane ePane = AddPane(title, "GPS");
                CreateGPSDeviceGraph(ePane, gpsFile);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }
            #endregion


            #region Actigraphs
            string[] file = Directory.GetFileSystemEntries(path + "\\merged\\", "Actigraph*.csv");

            if (file.Length > 0)
            {
                string title = "Actigraphs";
                GraphPane ePane = AddPane(title, "Actigraphs");
                for (int i = 0; (i < file.Length); i++)
                {
                    string actigraphFile = Path.Combine(path, "merged\\Actigraph" + (i + 1) + ".csv");
                    if (File.Exists(actigraphFile))                    
                        CreateActigraphGraph(ePane, actigraphFile,i);
                }

                //CreateActigraphLineSegments(ePane);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }

            #endregion Actigraphs

            #region Sensewear
            string sensewearFile = Path.Combine(path + "\\merged\\", "Sensewear.csv");
            if (File.Exists(sensewearFile))
            {
                string title = "Sensewear";
                GraphPane ePane = AddPane(title, "Sensewear");
                CreateSensewearGraph(ePane, sensewearFile);
                paneOrders.Add(title, paneOrdering);
                paneOrdering++;
            }
            #endregion Sensewear


            GraphPane hPane = null;
            string filepath = "";

            #region COMBINED DATATYPE GRAPH - USUALLY HAS HEART RATE + 1 or more of GPS data, Annotation labels, or Survey responses
            
            files = Directory.GetFiles(path + "\\merged\\", "HeartRate*");
            if (files.Length > 0)
            {
                string title = "Heart Rate";
                hPane = AddPane(title, "Beats Per Minute");
                paneOrders.Add(title, paneOrdering);
                CreateHeartRateGraph(hPane, files);
            }
            else if (AnyMatches(path + "\\merged\\", "GPS*,POI*"))
            {
                string title = paneOrdering + " Location";
                hPane = AddPane(title, "");
            }
            else if (AnyMatches(path + "\\annotation\\phoneannotation\\", "annotat*,photos*,surveys*"))
            {
                string title = paneOrdering + " Labels";
                hPane = AddPane(title, "");
            }
            else if (AnyMatches(path + "\\annotation\\audioannotation\\", "annotat*"))
            {
                string title = paneOrdering + " Labels";
                hPane = AddPane(title, "");
            }
            else if (AnyMatches(path + "\\annotation\\phoneannotation\\", "average-*"))
            {
                string title = paneOrdering + " Annotation";
                hPane = AddPane(title, "");
                hPane.YAxis.IsVisible = false;
                _doesShowHover = false;
            }
            
            #endregion


            #region Annotations

            if (hPane != null)
            {
                paneOrdering++;
                string title = "Annotations";
                GraphPane aPane = AddPane(title, "Annotations");
                aPane.YAxis.IsVisible = true;

                //Uncomment if Heart Rate Graph is deleted
                //paneOrders.Add(title, paneOrdering);
                
                //Hack - Dummy curve that forces the scale of the Y-axis and alignment not to change
               PointPairList listACT = new PointPairList();
               listACT.Add(0, 0);
               aPane.AddCurve("annotation", listACT, Color.White, SymbolType.TriangleDown);
               
                // add GPS
                paneOrders.Add(title, paneOrdering);
                filepath = Path.Combine(path + "\\merged\\", "GPSlog.csv");
                if (File.Exists(filepath))
                    CreateGPSGraph(hPane, filepath);
                filepath = Path.Combine(path + "\\merged\\", "POIlog.csv");
                if (File.Exists(filepath))
                    CreatePOIGraph(hPane, filepath);

                //add audio annotations
                if (Directory.Exists(path + "\\annotation\\audioannotation\\"))
                {
                    #region commented 
                    /*
                    files = Directory.GetFiles(path + "\\annotation\\audioannotation\\", "AnnotationIntervals.csv");
                    for (int i = 0; i < files.Length; i++)
                    {
                        string name = Path.GetFileNameWithoutExtension(files[i]);
                        CreateDiaryGraph(aPane, files[i], name, 10 + 20 * i);
                    }
                     */
                    #endregion
 
                    // commented old path for original annotations
                    //string file_annotations = path + "\\annotation\\audioannotation\\" + "AnnotationIntervals.csv";

                    //reading the corrected annotations in the merged folder
                    string file_annotations = path + "\\merged\\" + "AnnotationIntervals.csv";
                    string path_annotations_color = path + "\\annotation\\audioannotation\\";

                    if (File.Exists(file_annotations))
                    {
                        CreateDiaryGraph(aPane, file_annotations, path_annotations_color, "Time: ", 20, "activity");
                        CreateDiaryGraph(aPane, file_annotations, path_annotations_color, "Time:", 130, "posture");
                    }
                     

                }

                //add phone annotations
                #region Phone Annotations
                if (Directory.Exists(path + "\\annotation\\phoneannotation\\"))
                {
                    filepath = Path.Combine(path + "\\annotation\\phoneannotation\\", "photos.csv");
                    if (File.Exists(filepath))
                        CreatePhotoGraph(hPane, filepath, path + "\\annotation\\phoneannotation\\");

                    filepath = Path.Combine(path + "\\annotation\\phoneannotation\\", "surveys.csv");
                    if (File.Exists(filepath))
                        CreateSurveyGraph(hPane, filepath);


                    files = Directory.GetFiles(path + "\\annotation\\phoneannotation\\", "average-*");
                    if (files.Length > 0)
                        CreateAgreementGraph(hPane, files);
                }
                #endregion


            }
            #endregion





            #endregion

            hScrollBar1.Value = 0;            
            SetTimes();
            RefreshMasterPaneLayout();
        }

        /// <summary>
        /// Determines whether there is at least one file matching one of the supplied filename patterns
        /// </summary>
        /// <param name="pathSearchDirectory">absolute path of the directory to search</param>
        /// <param name="filePatterns">comma separated list of file patterns (using wild cards such as asterisk) to match against directory file list</param>
        /// <returns>true if any files matched for one or more of the supplied patterns within the directory specified by the path</returns>
        private bool AnyMatches(string pathSearchDirectory, string filePatterns)
        {
            bool isMatch = false;
            string[] patternsToMatch = filePatterns.Split(',');
            int i = 0;

           
                while (!isMatch && (i < patternsToMatch.Length))
                {
                    if (Directory.GetFiles(pathSearchDirectory, patternsToMatch[i]).Length > 0) isMatch = true;
                    i++;
                }

                return isMatch;
            
        }
        

        #region INTERACTION

        #region OPEN DATASET
        private void openToolStripMenuItem_Click(object sender, EventArgs e)
        {
            if (folderBrowserDialog1.ShowDialog() == DialogResult.OK)
            {
                _pathDataset = folderBrowserDialog1.SelectedPath;
                OpenDataset(_pathDataset);
            }
        }
        private void OpenDataset(string path)
        {
            if (Directory.Exists(path))
            {
                this.Cursor = Cursors.WaitCursor;
                Reset();
                SetEnable(false);
                this.Refresh();

                BuildCharts(path);
                SetEnable(true);
                this.Cursor = Cursors.Default;
            }
            else Logger.LogError("OpenDataset", path + " does not exist");
        }
        #endregion

        #region ZOOM
        private void hScrollBar1_ValueChanged(object sender, EventArgs e)
        {
            this.Cursor = Cursors.WaitCursor;
            XDate startx = new XDate(_firstDate.Year, _firstDate.Month, _firstDate.Day, _firstDate.Hour, _firstDate.Minute, _firstDate.Second);
            
            XDate endx = new XDate(startx);
            startx.AddMinutes(hScrollBar1.Value*_minutesPage);
            endx.AddMinutes((hScrollBar1.Value + 1)*_minutesPage);
            for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
            {
                zedGraphControl1.MasterPane[i].XAxis.Scale.Min = (double)startx;
                zedGraphControl1.MasterPane[i].XAxis.Scale.Max = (double)endx;
            }
            int pixelunits = (int)Math.Ceiling((double)(hScrollBar1.Width - 130) / hScrollBar1.Maximum);
            lbScrollTime.Location = new Point(hScrollBar1.Left + pixelunits* hScrollBar1.Value,lbScrollTime.Location.Y);
            lbScrollTime.Text = String.Format("{0}-{1}", startx.DateTime.ToShortTimeString(), endx.DateTime.ToShortTimeString());

            if (_isAdaptingPointSize) SetPointSize();

            zedGraphControl1.AxisChange();
            zedGraphControl1.Refresh();
            
            this.Cursor = Cursors.Default;
            
        }

        private void buttonZoomOut_Click(object sender, EventArgs e)
        {
            if (_zoomedOut)
            {
                hScrollBar1.Visible = true;
                buttonZoomOut.Text = "View All";
                _zoomedOut = false;
                hScrollBar1_ValueChanged(null, null);
            }
            else
            {
                XDate startx = new XDate(_firstDate.Year, _firstDate.Month, _firstDate.Day, _firstDate.Hour, _firstDate.Minute, _firstDate.Second);

                XDate endx = new XDate(_lastDate.Year, _lastDate.Month, _lastDate.Day, _lastDate.Hour, _lastDate.Minute, _lastDate.Second);
                for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
                {
                    zedGraphControl1.MasterPane[i].XAxis.Scale.Min = (double)startx;
                    zedGraphControl1.MasterPane[i].XAxis.Scale.Max = (double)endx;
                }
                lbScrollTime.Text = "VIEWING ALL";

                zedGraphControl1.AxisChange();
                zedGraphControl1.Refresh();

                if (_isAdaptingPointSize) SetPointSize();
                hScrollBar1.Visible = false;
                _zoomedOut = true;
                buttonZoomOut.Text = "Scroll Through";
            }
        }


      
        #endregion

        #region SHOW/HIDE PANES
        private void checkBox_CheckedChanged(object sender, EventArgs e)
        {
            string item = ((CheckBox)sender).Text;
            bool show = ((CheckBox)sender).Checked;
            bool isPane = _htPanes.Contains(item);
            if (!show)
            {
                if (isPane) RemovePane(item);
            }
            else
            {
                if (isPane) ShowPane(item);
            }
           
            RefreshMasterPaneLayout();
        }

        private void ShowPane(string pane)
        {
            GraphPane gp = (GraphPane)_htPanes[pane];
            int index = 0;
            //determine placement of pane
            bool isFound = false;
     
            
            int insertedPane=(int)paneOrders[pane]-1;
            for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
            {
                if (!isFound)
                {
                    string panetitle = zedGraphControl1.MasterPane.PaneList[i].Title.Text;
                    //if (panetitle.CompareTo(pane) > 0)
                    int paneIndex=(int)paneOrders[panetitle] -1;
                    if (paneIndex > insertedPane)
                    {
                        index = i;
                        isFound = true;
                    }
                    
                }
            }
             
            if (!isFound) index = zedGraphControl1.MasterPane.PaneList.Count;

            if (gp != null)
                zedGraphControl1.MasterPane.PaneList.Insert(index, gp);
    
        }

        private void RemovePane(string pane)
        {
            GraphPane gp = zedGraphControl1.MasterPane.PaneList[pane];
            if (gp != null)
                zedGraphControl1.MasterPane.PaneList.Remove(gp);

        }
        
        #endregion       



        #region HOVER
        PointPair ppHover = null;
        private void HighlightGraphs(double x, double z)
        {
            if (_doesShowHover)
            {
                for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
                {
                    GraphPane gp = zedGraphControl1.MasterPane.PaneList[i];
                    if (_htBoxes.Contains(gp.Title.Text))
                    {
                        BoxObj boxForLabel = (BoxObj)_htBoxes[gp.Title];
                        gp.GraphObjList.Clear();

                        boxForLabel = new BoxObj(x, gp.YAxis.Scale.Max, z, gp.YAxis.Scale.Max - gp.YAxis.Scale.Min, Color.Black, Color.PapayaWhip);
                        boxForLabel.Location.CoordinateFrame = CoordType.AxisXYScale;
                        boxForLabel.Border.Style = System.Drawing.Drawing2D.DashStyle.DashDot;

                        //// place the box behind the axis items, so the grid is drawn on top of it
                        boxForLabel.ZOrder = ZOrder.F_BehindGrid;
                        _htBoxes[gp.Title] = boxForLabel;
                        gp.GraphObjList.Add(boxForLabel);
                    }
                }
                zedGraphControl1.AxisChange();
                this.Refresh();
            }
        }
        
        
        string zedGraphControl1_PointValueEvent(ZedGraphControl sender, GraphPane pane, CurveItem curve, int iPt)
        {

            if (curve[iPt] != ppHover)
            {
                ppHover = curve[iPt];
                if (pictureBox1.Visible)
                {
                    pictureBox1.Visible = false;
                }
                if (curve.Label.Text == "photos")
                {
                    PointF pf = pane.GeneralTransform(curve[iPt].X, curve[iPt].Y, CoordType.AxisXYScale);
                    string[] split = curve[iPt].Tag.ToString().Split(',');
                    pictureBox1.Image = Image.FromFile(split[1]);
                    pictureBox1.Location = new Point(Convert.ToInt32(pf.X), Convert.ToInt32(pf.Y) - pictureBox1.Height);
                    pictureBox1.BringToFront();
                    pictureBox1.Visible = true;
                    return split[0];
                }
                else if (curve.Label.Text.StartsWith("Time"))
                {
                    HighlightGraphs(curve[iPt].Z, curve[iPt].X - curve[iPt].Z);
                }

            }
            else if (curve.Label.Text == "photos")
            {
                string[] split = curve[iPt].Tag.ToString().Split(',');
                return split[0];
            }

            if (curve[iPt].Tag != null)
                return curve[iPt].Tag.ToString();
            else return curve[iPt].ToString();
        }

        #endregion

        private void hScrollBar1_Scroll(object sender, ScrollEventArgs e)
        {

        }



        #endregion

        #region Buttons & ZOOM

        Form2 rawForm = null;
        void buttonDisplayRaw_Click(object sender, System.EventArgs e)
        {
            XDate startx = (XDate)zedGraphControl1.MasterPane[0].XAxis.Scale.Min;
            XDate endx = (XDate)zedGraphControl1.MasterPane[0].XAxis.Scale.Max;

            if (((TimeSpan)(endx.DateTime.Subtract(startx.DateTime))).TotalMinutes > 20)
            {
                MessageBox.Show("Cannot display more than 20 minutes of raw data at a time. Please select a 20 minute segment or less then click Display Raw");
                return;
            }

            if ((rawForm == null) || (rawForm.IsDisposed))
                rawForm = new Form2();

            rawForm.StartX = startx;
            rawForm.EndX = endx;
            rawForm.PathDataset = _pathDataset;

            if (rawForm.Visible == false)
                rawForm.Show();

        }


        Form3 syncForm = null;
        private void button_sync_Click(object sender, EventArgs e)
        {
            XDate startx = (XDate)zedGraphControl1.MasterPane[0].XAxis.Scale.Min;
            XDate endx = (XDate)zedGraphControl1.MasterPane[0].XAxis.Scale.Max;

            /*if (((TimeSpan)(endx.DateTime.Subtract(startx.DateTime))).TotalMinutes > 20)
            {
                MessageBox.Show("Cannot display more than 20 minutes of raw data at a time. Please select a 20 minute segment or less then click Display Raw");
                return;
            }
             */


            if ((syncForm == null) || (syncForm.IsDisposed))
                syncForm = new Form3(_pathDataset);

            //syncForm.StartX = startx;
            //syncForm.EndX = endx;
            //syncForm.PathDataset = _pathDataset;

            if (syncForm.Visible == false)
                syncForm.Show();

        }



        #endregion Buttons & ZOOM


    }




    public class LineSegment
    {
        private double x1;
        private double x2;
        private double y1;
        private double y2;

        public LineSegment()
        {
            x1 = 0;
            x2 = 0;
            y1 = 0;
            y2 = 0;
        }

        public double X1
        {
            get
            {
                return this.x1;
            }
            set
            {
                this.x1 = value;
            }
        }

        public double Y1
        {
            get
            {
                return this.y1;
            }
            set
            {
                this.y1 = value;
            }
        }

        public double X2
        {
            get
            {
                return this.x2;
            }
            set
            {
                this.x2 = value;
            }
        }

        public double Y2
        {
            get
            {
                return this.y2;
            }
            set
            {
                this.y2 = value;
            }
        }
    }


}