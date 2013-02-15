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
using DataViewer.Utilities;//FileReadWrite
using DataViewer.Logging; //Logger


namespace DataViewer
{

    public partial class DataViewForm : Form
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

        Color[] _colorPalette = new Color[9] { Color.Red, Color.YellowGreen, Color.Beige, Color.Aqua, Color.Violet, Color.Bisque, Color.Cyan, Color.DarkOrange, Color.Khaki };

        Hashtable paneOrders;

        #endregion

        //DONE
        #region INITIALIZE

        public DataViewForm()
        {
            if (File.Exists("Configuration.xml"))
            {
                CurrentWockets._Configuration = new Wockets.Data.Configuration.WocketsConfiguration();
                CurrentWockets._Configuration.FromXML("Configuration.xml");
            }
            InitializeComponent();
        }

        public DataViewForm(string pathStartDS)
        {
            Logger.LogDebug("DataViewForm", "arguments " + pathStartDS);
            _pathDataset = pathStartDS;
            InitializeComponent();
        }

        private void DataViewForm_Load(object sender, EventArgs e)
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

        private void DataViewForm_Resize(object sender, EventArgs e)
        {
            SetLayout();
        }

        private void SetLayout()
        {
            int graphwidth = ClientRectangle.Width - groupBox1.Width;
            int graphheight = ClientRectangle.Height - 110;

            // Control Group dimentions
            groupBox1.Location = new Point(graphwidth, MainMenuStrip.Bottom + 5);//+5
            groupBox1.Size = new Size(groupBox1.Width, graphheight - 15); // added          

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
            buttonDisplayRaw.Location = new Point(hScrollBar1.Right + 5, hScrollBar1.Top + 5);//+5
            button_sync.Location = new Point(hScrollBar1.Right + 5, hScrollBar1.Top + 30);

            hScrollBar1.Visible = false;
        }

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

            // Add checkbox
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

        private void SetTimes()
        {
            lbFirstDate.Text = _firstDate.ToString();
            lbSecondDate.Text = _lastDate.ToString();
            lbScrollTime.Text = _firstDate.ToString();
            TimeSpan ts = _lastDate - _firstDate;

            // Determine paging width based on total duration of data
            //if (ts.TotalHours > 1)//4 or more hours of data
            //    _minutesPage = 20;
            //else 
            if (ts.TotalHours > 24)
                _minutesPage = 720;
            else if (ts.TotalMinutes > 60)//between 1-4 hours of data
                _minutesPage = 20;
            else if (ts.TotalMinutes > 15) _minutesPage = 5; //between 15-60 minutes of data
            else _minutesPage = 1;

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

        //IN PROGRESS
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
                catch { }
            }

            LineItem[] pointsCurves = new LineItem[headers.Length - 1];
            for (int j = 0; j < pointsCurves.Length; j++)
            {
                pointsCurves[j] = new LineItem("TEST_LABEL");
                pointsCurves[j] = gp.AddCurve("JPN SERIES", listDataPoints[j], _colorPalette[j], SymbolType.Circle);
                pointsCurves[j].Symbol.Fill = new Fill(_colorPalette[j]);
                if (!_isAdaptingPointSize) pointsCurves[j].Symbol.Size = 1F;
                // **** JPN SET TO TRUE IF A LINE IS DESIRED
                pointsCurves[j].Line.IsVisible = true;
                pointsCurves[j].Tag = "THIS IS A TAG";
                _alLinesWithSymbols.Add(pointsCurves[j]);
                WidenDatesIfNeeded(listDataPoints[j]);
            }
        }

        #endregion GENERIC GRAPH
    
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
                            label += split[c].Replace("_", ", ").Replace("-", " ").Trim(',', ' ') + "\n ";
                        }
                        labelList = new PointPairList();
                        labelList.Add(endx, y, startx, String.Format("{3} {0}-{1}\n,{2}", dtStart.ToShortTimeString(), dtEnd.ToShortTimeString(), label, title));
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
            bool is_category_3 = false;
            bool is_category_4 = false;

            string[] lines_read = null;
            string[] label_color = null;
            BindingList<string[]> labels_color_list_1 = null;
            BindingList<string[]> labels_color_list_2 = null;
            BindingList<string[]> labels_color_list_3 = null;
            BindingList<string[]> labels_color_list_4 = null;



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
            else if (type.CompareTo("smoking") == 0)
            {
                is_category_3 = true;

                if (File.Exists(dirpath_colors + "ActivityLabelsColors_3.csv"))
                {
                    labels_color_list_3 = new BindingList<string[]>();
                    lines_read = FileReadWrite.ReadLinesFromFile(dirpath_colors + "ActivityLabelsColors_3.csv");

                    foreach (string line in lines_read)
                    {
                        label_color = line.Split(',');
                        labels_color_list_3.Add(label_color);
                    }
                }
            }
            else if (type.CompareTo("puffing") == 0)
            {
                is_category_4 = true;

                if (File.Exists(dirpath_colors + "ActivityLabelsColors_4.csv"))
                {
                    labels_color_list_4 = new BindingList<string[]>();
                    lines_read = FileReadWrite.ReadLinesFromFile(dirpath_colors + "ActivityLabelsColors_4.csv");

                    foreach (string line in lines_read)
                    {
                        label_color = line.Split(',');
                        labels_color_list_4.Add(label_color);
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
                        if (is_category_1)
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
                        else if (is_category_3)
                        {
                            if ((split.Length > 2) && (split[5].Length > 0))
                            {
                                clabel = split[5];

                                for (int j = 0; j < labels_color_list_3.Count; j++)
                                {
                                    if (labels_color_list_3[j][1].CompareTo(clabel) == 0)
                                    {
                                        color = labels_color_list_3[j][3];
                                        isSolid = true;
                                        break;
                                    }
                                }
                            }
                        }
                        else if (is_category_4)
                        {
                            if ((split.Length > 2) && (split[6].Length > 0))
                            {
                                clabel = split[6];

                                for (int j = 0; j < labels_color_list_4.Count; j++)
                                {
                                    if (labels_color_list_4[j][1].CompareTo(clabel) == 0)
                                    {
                                        color = labels_color_list_4[j][3];
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
                            label += split[c].Replace("_", ", ").Replace("-", " ").Trim(',', ' ') + "\n ";
                        }

                        labelList = new PointPairList();
                        labelList.Add(endx, yoffset, startx, String.Format("{3}: {0}  -  {1}\n {2}", dtStart.ToLongTimeString(), dtEnd.ToLongTimeString(), label, title));

                        #endregion

                        #region ADD BAR


                        //HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, Color.FromName(color
                        HiLowBarItem myBar = gp.AddHiLowBar(title, labelList, Color.FromArgb(Int32.Parse(color)));


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
                    list_Photo.Add(x, 25, split[2] + "," + Path.Combine(imagedir, split[1]));
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
                    list.Add(x, 20, split[1].Replace(";", "\n"));
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

        #region CHART BUILDER

        private bool BuildCharts(string path)
        {
            paneOrders = new Hashtable();
            int paneOrdering = 1;
            SetGraphPanels();
            string[] files;
            files = Directory.GetFiles(path + "\\", "*.csv");
            for (int i = 0; i < files.Length; i++)
            {
                string sensorType = Path.GetFileNameWithoutExtension(files[i]);
                if (!sensorType.Contains("RAW_DATA"))
                {
                    GraphPane ePane = AddPane(sensorType, "Y-TITLE");
                    CreateGenericGraph(ePane, files[i]);
                    paneOrders.Add(sensorType, "Y-TITLE");
                    paneOrdering++;
                }
            }
            GraphPane hPane = null;
            string filepath = "";

            // Add annotations
            string ann_title = "Annotations";
            GraphPane aPane = AddPane(ann_title, "Annotations");
            aPane.YAxis.IsVisible = true;

            if (hPane != null) paneOrdering++;
            else paneOrders.Add(ann_title, paneOrdering);
           
            //Hack - Dummy curve that forces the scale of the Y-axis and alignment not to change
            PointPairList listACT = new PointPairList();
            listACT.Add(0, 0);
            aPane.AddCurve("annotation", listACT, Color.White, SymbolType.TriangleDown);

            //reading the corrected annotations in the merged folder
            string file_annotations = path + "\\merged\\" + "AnnotationIntervals.csv";

            if (File.Exists(file_annotations))
            {
                string path_annotations_color = "";

                if (Directory.Exists(path + "\\annotation\\audioannotation\\"))
                    path_annotations_color = path + "\\annotation\\audioannotation\\";
                else if (Directory.Exists(path + "\\annotation\\phoneannotation\\"))
                    path_annotations_color = path + "\\annotation\\phoneannotation\\";
                else if (Directory.Exists(path + "\\annotation\\tabletannotation\\"))
                    path_annotations_color = path + "\\annotation\\tabletannotation\\";

                CreateDiaryGraph(aPane, file_annotations, path_annotations_color, "Time: ", 0, "activity");
                CreateDiaryGraph(aPane, file_annotations, path_annotations_color, "Time:", 110, "posture");

                if (Directory.Exists(path + "\\annotation\\tabletannotation\\"))
                {
                    CreateDiaryGraph(aPane, file_annotations, path_annotations_color, "Time:", 220, "smoking");
                    CreateDiaryGraph(aPane, file_annotations, path_annotations_color, "Time:", 330, "puffing");
                }
            }

            // Add phone annotations
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

        #endregion INTERACTION

        //DONE
        #region BUTTONS & ZOOM

        RawDataViewForm rawForm = null;
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
                rawForm = new RawDataViewForm();

            rawForm.StartX = startx;
            rawForm.EndX = endx;
            rawForm.PathDataset = _pathDataset;

            if (rawForm.Visible == false)
                rawForm.Show();

        }

        SyncViewForm syncForm = null;
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
                syncForm = new SyncViewForm(_pathDataset);

            //syncForm.StartX = startx;
            //syncForm.EndX = endx;
            //syncForm.PathDataset = _pathDataset;

            if (syncForm.Visible == false)
                syncForm.Show();

        }

        #endregion Buttons & ZOOM

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

        private static DateTime ConvertUNIXDateTime(double timestamp)
        {
            // First make a System.DateTime equivalent to the UNIX Epoch.
            DateTime dateTime = new System.DateTime(1970, 1, 1, 0, 0, 0, 0);
            // Add the number of seconds in UNIX timestamp to be converted.
            dateTime = dateTime.AddSeconds(timestamp / 1000);
            return dateTime;
        }

        #endregion DATETIME OPERATIONS

    }

    //DONE
    #region CLASS LineSegment

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

    #endregion

}