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
using System.Xml;

using ZedGraph;
using DataViewer.Utilities;//FileReadWrite
using DataViewer.Logging; //Logger
namespace DataViewer
{


    public partial class RawDataViewForm : Form
    {
        //DONE
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

        private const string ANNOTATION_EXTENSION_CSV = @"*annotation.csv";
        private const string ANNOTATION_EXTENSION_XML = @"*annotation.xml";
        private const string SUMMARY_DATA_EXTENSION = @"*.csv";
        private const string RAW_DATA_EXTENSION = @"*.csv";
        private const string RAW_DATA_FLAG = @"RAW_DATA";
        private const string ANNOTATION_FLAG = @"annotation";
        private const string ANNOTATION_AXIS_TITLE = @"Annotation";

        XDate startX;
        XDate endX;

        Hashtable paneOrders;

        #endregion

        //DONE
        #region ENCAPSULATED FIELDS

        public XDate StartX
        {
            get
            {
                return this.startX;
            }
            set
            {
                this.startX = value;
            }
        }

        public XDate EndX
        {
            get
            {
                return this.endX;
            }

            set
            {
                this.endX = value;
            }
        }



        public string PathDataset
        {
            get
            {
                return this._pathDataset;
            }
            set
            {
                this._pathDataset = value;
            }
        }

        #endregion ENCAPSULATED FIELDS

        //DONE
        #region INITIALIZE

        public RawDataViewForm()
        {
            InitializeComponent();

        }
        public RawDataViewForm(string pathStartDS)
        {
            Logger.LogDebug("RawDataViewForm", "arguments " + pathStartDS);
            _pathDataset = pathStartDS;
            InitializeComponent();

        }

        private void RawDataViewForm_Load(object sender, EventArgs e)
        {
            this.WindowState = FormWindowState.Maximized;
            SetGraphPanels();

            if (_isUsingLabels)
                zedGraphControl1.PointValueEvent += new ZedGraphControl.PointValueHandler(zedGraphControl1_PointValueEvent);

            if (_pathDataset.Length > 0) OpenDataset(_pathDataset);
        }

        #endregion

        //DONE
        #region LAYOUT and FORMATTING

        //DONE
        private void RawDataViewForm_Resize(object sender, EventArgs e)
        {
            SetLayout();
        }

        //DONE
        private void SetLayout()
        {
            int graphwidth = ClientRectangle.Width - groupBox1.Width;
            int graphheight = ClientRectangle.Height - 110;

            // Control Group dimentions
            groupBox1.Location = new Point(graphwidth, MainMenuStrip.Bottom); // +5 added
            groupBox1.Size = new Size(groupBox1.Width, graphheight); // -15 added          

            //Graph Dimensions
            zedGraphControl1.Location = new Point(0, MainMenuStrip.Bottom);
            zedGraphControl1.Size = new Size(graphwidth, graphheight);

            //Scroll Bar Dimentions
            hScrollBar1.Width = graphwidth - 10;
            hScrollBar1.Location = new Point(5, zedGraphControl1.Bottom + 20);

            //Date and Time Labels Locations
            lbFirstDate.Location = new Point(5, hScrollBar1.Bottom);
            lbSecondDate.Location = new Point(hScrollBar1.Right - lbSecondDate.Width - 100, hScrollBar1.Bottom);
            lbScrollTime.Location = new Point(hScrollBar1.Left, hScrollBar1.Top - lbScrollTime.Height);

            //Buttons Location
            buttonZoomOut.Location = new Point(hScrollBar1.Right + 5, hScrollBar1.Top - 20); //-30

            hScrollBar1.Visible = false;
        }

        //DONE
        private void SetGraphPanels()
        {
            MasterPane myMaster = zedGraphControl1.MasterPane;

            _firstDate = DateTime.Now;

            //JPN: Initialize the date of last point to be shown in the dataview to the beginning of the Wockets Era.
            //Let's say 01-01-2007. If a dataset predates 2007, you will have to zoom manually to the region of interest
            //This value will later be changed to the last timestamp observed in the dataset
            _lastDate = new DateTime(2007, 01, 01, 00, 00, 00);

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

        //DONE
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

            //RefreshMasterPaneLayout();

            return pane;
        }

        //DONE
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

            // Arrange checkboxes
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
        }

        //DONE
        private void SetPointSize()
        {
            if (zedGraphControl1.MasterPane.PaneList.Count > 0)
            {
                double minutes = ((TimeSpan)(_lastDate - _firstDate)).TotalMinutes;
                double ticks = (zedGraphControl1.MasterPane.PaneList[0].XAxis.Scale.Max - zedGraphControl1.MasterPane.PaneList[0].XAxis.Scale.Min) * 1000;
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

        //CHECKED
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

        //DONE
        private void WidenDatesIfNeeded(PointPairList pl)
        {
            if (pl.Count > 0)
                WidenDatesIfNeeded(new XDate(pl[0].X), new XDate(pl[pl.Count - 1].X));
        }

        //DONE
        private void WidenDatesIfNeeded(XDate fDate, XDate lDate)
        {
            if (fDate.DateTime < _firstDate) _firstDate = fDate.DateTime;
            if (lDate.DateTime > _lastDate) _lastDate = lDate.DateTime;
        }

        //DONE
        private void SetEnable(bool isEnabled)
        {
            zedGraphControl1.Enabled = isEnabled;
            groupBox1.Enabled = isEnabled;
            hScrollBar1.Enabled = isEnabled;
            buttonZoomOut.Enabled = isEnabled;
            zedGraphControl1.Visible = isEnabled;
        }

        //DONE
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

        // POSSIBLY READY
        #region GENERIC GRAPH

        private void CreateGenericGraph(GraphPane gp, string filePath)
        {
            string[] values = FileReadWrite.ReadLinesFromFile(filePath);
            string[] headers = values[0].Split(',');

            PointPairList[] listDataPoints = new PointPairList[headers.Length - 1];
            for (int j = 0; j < listDataPoints.Length; j++) listDataPoints[j] = new PointPairList();

            //for each row, add values to PointPairLists
            for (int i = 1; i < values.Length; i++)
            {
                try
                {
                    string[] split = values[i].Split(',');
                    for (int j = 1; j < split.Length; j++)
                    {
                        if (split.Length > 1) //TimeStamp + at least one data value
                        {
                            // TIMESTAMP - X VALUE
                            DateTime dt = DateTimeParse(split[0]); //TimeStamp, Column 0
                            double x = (double)new XDate(dt);       //x value is numeric representation of TimeStamp
                            if (x >= (double)startX && x <= (double)endX)
                            {
                                double y = 0; string label = "EMPTY LABEL";
                                if ((split.Length > 1) && (split[j].Length > 0))
                                {
                                    y = Convert.ToDouble(split[j]);//Column 3/C
                                    if (_isUsingLabels)
                                    {
                                        label = String.Format("{0}\n{1} {2}", headers[j], dt.ToLongTimeString(), y);
                                        listDataPoints[j - 1].Add(x, y, label);
                                    }
                                    else listDataPoints[j - 1].Add(x, y);
                                }
                            }
                        }
                    }
                }
                catch { }
            }

            LineItem[] pointsCurves = new LineItem[headers.Length - 1];
            for (int j = 0; j < pointsCurves.Length; j++)
            {
                pointsCurves[j] = new LineItem("TEST_LABEL");
                pointsCurves[j] = gp.AddCurve(headers[j], listDataPoints[j], DataViewForm._seriesColorPalette[j], SymbolType.Circle);
                pointsCurves[j].Symbol.Fill = new Fill(DataViewForm._seriesColorPalette[j]);
                if (!_isAdaptingPointSize) pointsCurves[j].Symbol.Size = 1F;
                // **** JPN SET TO TRUE IF A LINE IS DESIRED
                pointsCurves[j].Line.IsVisible = true;
                pointsCurves[j].Tag = "THIS IS A TAG";
                _alLinesWithSymbols.Add(pointsCurves[j]);
                WidenDatesIfNeeded(listDataPoints[j]);
            }
        }

        #endregion GENERIC GRAPH

        //IN PROGRESS
        #region ANNOTATION GRAPH
        private void CreateDiaryGraph(GraphPane gp, string filepath, string dirpath_colors,
                                       string title, int yoffset, string type)
        {
            gp.BarSettings.Base = BarBase.Y;
            gp.BarSettings.ClusterScaleWidth = 200.0;
            gp.BarSettings.Type = BarType.Overlay;

            PointPairList labelList = new PointPairList();

            if (filepath.Contains(".csv"))
            {

                string[] values = FileReadWrite.ReadLinesFromFile(filepath);

                for (int i = 1; i < values.Length; i++)
                {
                    try
                    {
                        string[] split = values[i].Split(',');

                        DateTime dtStart = DateTime.MinValue;
                        DateTime dtEnd = DateTime.MaxValue;

                        double startx = 0;
                        double endx = 0;

                        if (split.Length > 0 && split[0].Length > 0)
                        {
                            dtStart = DateTimeParse(split[0]);
                            startx = (double)new XDate(dtStart);
                        }
                        if (split.Length > 1 && split[1].Length > 0)
                        {
                            dtEnd = DateTimeParse(split[1]);
                            endx = (double)new XDate(dtEnd);
                        }

                        Color color = Color.White;
                        bool isSolid = false;
                        string clabel = "";
                        if (startx >= startX && endx >= endX)
                        {
                            if (split.Length > 2 && split[2].Length > 0)
                            {
                                clabel = split[2];
                                if (!DataViewForm.annotationColorMap.ContainsKey(clabel))
                                    DataViewForm.annotationColorMap.Add(clabel, DataViewForm._annotationColorPalette[DataViewForm.annotationColorMap.Count]);
                                color = DataViewForm.annotationColorMap[clabel];
                                isSolid = true;
                                labelList = new PointPairList();
                                labelList.Add(endx, yoffset, startx, String.Format("{3}: {0} - {1}\n {2}", dtStart.ToLongTimeString(), dtEnd.ToLongTimeString(), clabel, title));
                                HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, color);
                                myBar.Bar.Border.IsVisible = false;
                                if (isSolid) myBar.Bar.Fill.Type = FillType.Solid;
                                else myBar.Bar.Fill.Type = FillType.None;
                            }
                        }
                    }
                    catch { }
                }
            }
            else if (filepath.Contains(".xml"))
            {
                XmlDocument doc = new XmlDocument();
                doc.Load(filepath);
                XmlNodeList nodes = doc.GetElementsByTagName("ANNOTATION");

                foreach (XmlNode xn in nodes)
                {
                    try
                    {
                        DateTime dtStart = DateTimeParse(xn["START_DT"].InnerText);
                        DateTime dtEnd = DateTimeParse(xn["STOP_DT"].InnerText);

                        double startx = (double)new XDate(dtStart);
                        double endx = (double)new XDate(dtEnd);

                        Color color = Color.White;
                        bool isSolid = false;
                        string clabel = xn["LABEL"].InnerText;
                        if (startx >= (double)startX && endx >= (double)endX)
                        {
                            if (!DataViewForm.annotationColorMap.ContainsKey(clabel))
                                DataViewForm.annotationColorMap.Add(clabel, DataViewForm._annotationColorPalette[DataViewForm.annotationColorMap.Count]);
                            color = DataViewForm.annotationColorMap[clabel];
                            isSolid = true;
                            labelList = new PointPairList();
                            labelList.Add(endx, yoffset, startx, String.Format("{3}: {0} - {1}\n {2}", dtStart.ToLongTimeString(), dtEnd.ToLongTimeString(), clabel, title));
                            HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, color);
                            myBar.Bar.Border.IsVisible = false;
                            if (isSolid) myBar.Bar.Fill.Type = FillType.Solid;
                            else myBar.Bar.Fill.Type = FillType.None;
                        }
                    }
                    catch { }
                }

            }


        }

        #endregion

        //DONE
        #region CHART BUILDER

        private bool BuildCharts(string path)
        {
            paneOrders = new Hashtable();
            int paneOrdering = 1;
            SetGraphPanels();
            string[] files;

            files = Directory.GetFiles(path, RAW_DATA_EXTENSION);
            for (int i = 0; i < files.Length; i++)
            {
                string sensorType = Path.GetFileNameWithoutExtension(files[i]);
                if (sensorType.Contains(RAW_DATA_FLAG))
                {
                    //JPN: FIX THE Y-TITLE PLACE HOLDER
                    GraphPane ePane = AddPane(sensorType, "Y-TITLE PLACEHOLDER");
                    CreateGenericGraph(ePane, files[i]);
                    paneOrders.Add(sensorType, i);
                    paneOrdering++;
                }
            }

            files = Directory.GetFiles(path, ANNOTATION_EXTENSION_CSV);
            for (int i = 0; i < files.Length; i++)
            {
                string annotationType = Path.GetFileNameWithoutExtension(files[i]);
                GraphPane ePane = AddPane(annotationType, ANNOTATION_AXIS_TITLE);

                string path_annotations_color = "";

                CreateDiaryGraph(ePane, files[i], path_annotations_color, "Time: ", 0, annotationType);

                paneOrders.Add(annotationType, i);
                paneOrdering++;

                // JPN: Make sure the Annotations are showing up correctly.               
                ePane.YAxis.IsVisible = true;

                ////Hack - Dummy curve that forces the scale of the Y-axis and alignment not to change
                // JPN: Is this really necessary?
                PointPairList listACT = new PointPairList();
                listACT.Add(0, 0);
                ePane.AddCurve("annotation", listACT, Color.White, SymbolType.TriangleDown);
            }

            files = Directory.GetFiles(path, ANNOTATION_EXTENSION_XML);
            for (int i = 0; i < files.Length; i++)
            {
                string annotationType = Path.GetFileNameWithoutExtension(files[i]);
                GraphPane ePane = AddPane(annotationType, ANNOTATION_AXIS_TITLE);

                string path_annotations_color = "";

                CreateDiaryGraph(ePane, files[i], path_annotations_color, "Time: ", 0, annotationType);

                paneOrders.Add(annotationType, i);
                paneOrdering++;

                // JPN: Make sure the Annotations are showing up correctly.               
                ePane.YAxis.IsVisible = true;

                ////Hack - Dummy curve that forces the scale of the Y-axis and alignment not to change
                // JPN: Is this really necessary?
                PointPairList listACT = new PointPairList();
                listACT.Add(0, 0);
                ePane.AddCurve("annotation", listACT, Color.White, SymbolType.TriangleDown);
            }




            hScrollBar1.Value = 0;
            SetTimes();
            RefreshMasterPaneLayout();
            return true;
        }

        #endregion CHART BUILDER

        //DONE
        #region INTERACTION

        //DONE
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
                // JPN -- TEST !!!!!!!!!!!!!!!
                if (!BuildCharts(path)) Logger.LogError("OpenDataset", path + " does not appear to contain a dataset");
                SetEnable(true);
                this.Cursor = Cursors.Default;
            }
            else Logger.LogError("OpenDataset", path + " does not exist");
        }

        #endregion

        //DONE
        #region ZOOM

        private void hScrollBar1_ValueChanged(object sender, EventArgs e)
        {
            this.Cursor = Cursors.WaitCursor;
            XDate startx = new XDate(_firstDate.Year, _firstDate.Month, _firstDate.Day, _firstDate.Hour, _firstDate.Minute, _firstDate.Second);
            XDate endx = new XDate(startx);
            startx.AddMinutes(hScrollBar1.Value * _minutesPage);
            endx.AddMinutes((hScrollBar1.Value + 1) * _minutesPage);
            for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
            {
                zedGraphControl1.MasterPane[i].XAxis.Scale.Min = (double)startx;
                zedGraphControl1.MasterPane[i].XAxis.Scale.Max = (double)endx;
            }
            int pixelunits = (int)Math.Ceiling((double)(hScrollBar1.Width - 130) / hScrollBar1.Maximum);
            lbScrollTime.Location = new Point(hScrollBar1.Left + pixelunits * hScrollBar1.Value, lbScrollTime.Location.Y);
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

        //DONE
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

            int insertedPane = (int)paneOrders[pane] - 1;
            for (int i = 0; i < zedGraphControl1.MasterPane.PaneList.Count; i++)
            {
                if (!isFound)
                {
                    string panetitle = zedGraphControl1.MasterPane.PaneList[i].Title.Text;
                    //if (panetitle.CompareTo(pane) > 0)
                    int paneIndex = (int)paneOrders[panetitle] - 1;
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

        //DONE
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

        // Highlight the section of the data associated with the selected annotation label
        string zedGraphControl1_PointValueEvent(ZedGraphControl sender, GraphPane pane, CurveItem curve, int iPt)
        {
            if (curve[iPt] != ppHover)
            {
                ppHover = curve[iPt];
                // JPN: look for a better way to determine what series this belongs to
                if (curve.Label.Text.StartsWith("Time"))
                {
                    HighlightGraphs(curve[iPt].Z, curve[iPt].X - curve[iPt].Z);
                }
            }
            if (curve[iPt].Tag != null)
                return curve[iPt].Tag.ToString();
            else return curve[iPt].ToString();
        }

        #endregion

        #endregion INTERACTION

        //DONE
        #region DATETIME OPERATIONS

        public static DateTime DateTimeParse(string DateString)
        {
            string[] dateArray = DateString.Split(' ');
            string[] timeArray = dateArray[dateArray.Length - 1].Split(':');
            string[] secondArray = timeArray[2].Split('.');
            string[] newDateArray = new string[3];
            if (dateArray.Length > 1)                       //Create array to store date
                newDateArray = dateArray[0].Split('-');
            else                                            //Handle cases where date component is not defined in string
                newDateArray = new string[] { "1999", "01", "01" };
            int milliseconds = 0;
            // **** JPN: POSSIBLY MAKE THIS SO IT REJECTS INCORRECT TIME STAMPS
            if (secondArray.Length > 1) milliseconds = Convert.ToInt32(secondArray[1]);
            return new DateTime(Convert.ToInt32(newDateArray[0]), Convert.ToInt32(newDateArray[1]), Convert.ToInt32(newDateArray[2]), Convert.ToInt32(timeArray[0]), Convert.ToInt32(timeArray[1]), Convert.ToInt32(secondArray[0]), milliseconds);
        }

        #endregion DATETIME OPERATIONS


    }
}