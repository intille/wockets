using System;
using System.Collections;
using System.Collections.Generic;
using System.Data;
using System.Drawing;
using System.Diagnostics;
using System.Windows.Forms;
using OpenNETCF.GDIPlus;

namespace CircularProgress.SpinningProgress
{
    public partial class SpinningProgress  
    { 
        private Color m_InactiveColour = Color.FromArgb( 218, 218, 218 ); 
        private Color m_ActiveColour = Color.FromArgb( 35, 146, 33 ); 
        private Color m_TransistionColour = Color.FromArgb( 129, 242, 121 );

        public string _Label = "";
        private RegionPlus innerBackgroundRegion; 
        private GraphicsPath[] segmentPaths = new GraphicsPath[ 12 ];
        private Rectangle[] segmentRectangles = new Rectangle[12];
        private Rectangle innerRectangle = new Rectangle();
        private int[] startAngles = new int[12];
        private int[] sweepAngles = new int[12];
        
        private bool m_AutoIncrement = true; 
        private double m_IncrementFrequency = 100; 
        private bool m_BehindIsActive = true; 
        public int m_TransitionSegment = 0; 
        
        private System.Windows.Forms.Timer m_AutoRotateTimer;
        //[System.ComponentModel.DefaultValue(typeof(Color), "218, 218, 218")]
        public Color InactiveSegmentColour 
        { 
            get 
            { 
                return m_InactiveColour; 
            } 
            set 
            { 
                m_InactiveColour = value; 
                Invalidate(); 
            } 
        }
        //[System.ComponentModel.DefaultValue(typeof(Color), "35, 146, 33")]
        public Color ActiveSegmentColour 
        { 
            get 
            { 
                return m_ActiveColour; 
            } 
            set 
            { 
                m_ActiveColour = value; 
                Invalidate(); 
            } 
        } 
        //[ System.ComponentModel.DefaultValue( typeof( Color ), "129, 242, 121" ) ]
        public Color TransistionSegmentColour 
        { 
            get 
            { 
                return m_TransistionColour; 
            } 
            set 
            { 
                m_TransistionColour = value; 
                Invalidate(); 
            } 
        }
        [System.ComponentModel.DefaultValue(true)]
        public bool BehindTransistionSegmentIsActive 
        { 
            get 
            { 
                return m_BehindIsActive; 
            } 
            set 
            { 
                m_BehindIsActive = value; 
                Invalidate(); 
            } 
        }
        [System.ComponentModel.DefaultValue(-1)]
        public int TransistionSegment 
        { 
            get 
            { 
                return m_TransitionSegment; 
            } 
            set 
            { 
                if ( value > 11 || value < -1 ) 
                { 
                    throw new ArgumentException( "TransistionSegment must be between -1 and 11" ); 
                } 
                m_TransitionSegment = value; 
                Invalidate(); 
            } 
        }
        [System.ComponentModel.DefaultValue(true)]
        public bool AutoIncrement 
        { 
            get 
            { 
                return m_AutoIncrement; 
            } 
            set 
            { 
                m_AutoIncrement = value; 
                
                if ( value == false && m_AutoRotateTimer != null ) 
                { 
                    m_AutoRotateTimer.Dispose(); 
                    m_AutoRotateTimer = null; 
                } 
                
                if ( value == true && m_AutoRotateTimer == null ) 
                { 
                    m_AutoRotateTimer = new Timer();
                    m_AutoRotateTimer.Interval =(int) m_IncrementFrequency;
                    m_AutoRotateTimer.Tick += new EventHandler(m_AutoRotateTimer_Tick);
                    //; //+= new System.Timers.ElapsedEventHandler( IncrementTransisionSegment ); 
                    //m_AutoRotateTimer.Start(); 
                    //m_AutoRotateTimer.Enabled = false;
                } 
            } 
        }
        [System.ComponentModel.DefaultValue(100)]
        public double AutoIncrementFrequency 
        { 
            get 
            { 
                return m_IncrementFrequency; 
            } 
            set 
            { 
                m_IncrementFrequency = value; 
                
                if ( m_AutoRotateTimer != null ) 
                { 
                    AutoIncrement = false; 
                    AutoIncrement = true; 
                }
                if (m_IncrementFrequency > 0)
                    this.m_AutoRotateTimer.Enabled = true;
                else
                    this.m_AutoRotateTimer.Enabled = false;
            } 
        }
        static IntPtr token;
        static GdiplusStartupInput input = new GdiplusStartupInput();
        static GdiplusStartupOutput output;
        static GpStatusPlus stat = NativeMethods.GdiplusStartup(out token, input, out output);
        public SpinningProgress() 
        { 

            //  This call is required by the Windows Form Designer.
            InitializeComponent(); 
            
            //  Add any initialization after the InitializeComponent() call.
            CalculateSegments();

            m_AutoRotateTimer = new Timer(); 
            m_AutoRotateTimer.Interval=(int) m_IncrementFrequency;
            m_AutoRotateTimer.Tick += new EventHandler(m_AutoRotateTimer_Tick); //new System.Timers.ElapsedEventHandler(IncrementTransisionSegment);
            //this.DoubleBuffered = true;
            //m_AutoRotateTimer.Enabled = false;

            this.EnabledChanged += new EventHandler( SpinningProgress_EnabledChanged ); 
            // events handled by ProgressDisk_Paint
            this.Paint += new PaintEventHandler(ProgressDisk_Paint); 
            // events handled by ProgressDisk_Resize
            this.Resize += new EventHandler( ProgressDisk_Resize); 
            // events handled by ProgressDisk_SizeChanged
            //this.SizeChanged += new EventHandler(ProgressDisk_SizeChanged); 
        }

        void m_AutoRotateTimer_Tick(object sender, EventArgs e)
        {
            if (m_TransitionSegment == 11)
            {
                m_TransitionSegment = 0;
                m_BehindIsActive = !(m_BehindIsActive);
            }
            else if (m_TransitionSegment == -1)
            {
                m_TransitionSegment = 0;
            }
            else
            {
                m_TransitionSegment += 1;
            }

            Invalidate();
        }
        
        /*private void IncrementTransisionSegment( object sender, System.Timers.ElapsedEventArgs e ) 
        { 
            if ( m_TransitionSegment == 11 ) 
            { 
                m_TransitionSegment = 0; 
                m_BehindIsActive = !( m_BehindIsActive ); 
            } 
            else if ( m_TransitionSegment == -1 ) 
            { 
                m_TransitionSegment = 0; 
            } 
            else 
            { 
                m_TransitionSegment += 1; 
            } 
            
            Invalidate(); 
        } */
        
        
        private void CalculateSegments() 
        { 
            Rectangle rctFull = new Rectangle( 0, 0, this.Width, this.Height ); 
            Rectangle rctInner = new Rectangle( ((this.Width *  7) / 30),
                                                ((this.Height *  7) / 30),
                                                (this.Width -  ((this.Width *  14 ) / 30 )),
                                                (this.Height - ((this.Height * 14) / 30 ))); 

            GraphicsPath pthInnerBackground = null; 
            
            // Create 12 segment pieces
            for ( int intCount=0; intCount < 12; intCount++ ) 
            { 
                segmentPaths[ intCount ] = new GraphicsPath(); 
                
                // We subtract 90 so that the starting segment is at 12 o'clock
                //segmentPaths[intCount].AddPie( rctFull.X,rctFull.Y,rctFull.Width,rctFull.Height, ( intCount * 30 ) - 90, 25 ); 
                segmentRectangles[intCount] = rctFull;
                startAngles[intCount] = (intCount * 30) - 90;
                sweepAngles[intCount] = 25;
            } 
            
            // Create the center circle cut-out
            pthInnerBackground = new GraphicsPath();
            //pthInnerBackground.AddPie( rctInner.X, rctInner.Y,rctInner.Width,rctInner.Height, 0, 360 ); 
            innerRectangle = rctInner;
            innerBackgroundRegion = new RegionPlus(pthInnerBackground ); 
        } 
        
        
        private void SpinningProgress_EnabledChanged( object sender, System.EventArgs e ) 
        { 
            if ( Enabled == true ) 
            { 
                if ( m_AutoRotateTimer != null ) 
                {
                    m_AutoRotateTimer.Enabled = true; 
                } 
            } 
            else 
            { 
                if ( m_AutoRotateTimer != null ) 
                { 
                    m_AutoRotateTimer.Enabled=false; 
                } 
            } 
        }

        protected override void OnPaintBackground(PaintEventArgs e)
        {
            // Prevent flicker, we will take care of the background in OnPaint()
        }
        Bitmap bmpBuff = null;
        Graphics gOff=null; //Offscreen graphics
        IntPtr hdc;
        private void ProgressDisk_Paint( object sender, System.Windows.Forms.PaintEventArgs e ) 
        {

            if (bmpBuff == null)
            { //Bitmap for doublebuffering
                bmpBuff = new Bitmap(ClientSize.Width, ClientSize.Height);

                gOff = Graphics.FromImage(bmpBuff);
                hdc = gOff.GetHdc();
            }

/*            if (_Label!=""){
                if (m_TransitionSegment >= 9)
                    _Label = "Lag 4";
                else if (m_TransitionSegment >= 6)
                    _Label = "Lag 3";
                else if (m_TransitionSegment >= 3)
                    _Label = "Lag 2";                                
                else
                    _Label = "Lag 1";
            }*/
           
            
            using (GraphicsPlus g = new GraphicsPlus(hdc))
            {
                g.FillRectangle(Brushes.White, 0, 0, this.ClientRectangle.Width, this.ClientRectangle.Height);
                g.SetSmoothingMode(SmoothingMode.SmoothingModeAntiAlias);                              
                //e.Graphics.ExcludeClip(innerBackgroundRegion);                
                for (int intCount = 0; intCount < 12; intCount++)
                {
                    if (this.Enabled)
                    {
                        if (intCount == m_TransitionSegment)
                        {
                            // If this segment is the transistion segment, colour it differently
                            //g.FillPath(new SolidBrushPlus(m_TransistionColour), segmentPaths[intCount]);
                            g.FillPie(new SolidBrushPlus(m_TransistionColour), segmentRectangles[intCount].X, segmentRectangles[intCount].Y, segmentRectangles[intCount].Width, segmentRectangles[intCount].Height,startAngles[intCount],sweepAngles[intCount]);

                        }
                        else if (intCount < m_TransitionSegment)
                        {
                            // This segment is behind the transistion segment
                            if (m_BehindIsActive)
                            {
                                // If behind the transistion should be active, 
                                // colour it with the active colour
                                //g.FillPath(new SolidBrushPlus(m_ActiveColour), segmentPaths[intCount]);
                                g.FillPie(new SolidBrushPlus(m_ActiveColour), segmentRectangles[intCount].X, segmentRectangles[intCount].Y, segmentRectangles[intCount].Width, segmentRectangles[intCount].Height, startAngles[intCount], sweepAngles[intCount]);
                            }
                            else
                            {
                                // If behind the transistion should be in-active, 
                                // colour it with the in-active colour
                                //g.FillPath(new SolidBrushPlus(m_InactiveColour), segmentPaths[intCount]);
                                g.FillPie(new SolidBrushPlus(m_InactiveColour), segmentRectangles[intCount].X, segmentRectangles[intCount].Y, segmentRectangles[intCount].Width, segmentRectangles[intCount].Height, startAngles[intCount], sweepAngles[intCount]);
                            }
                        }
                        else
                        {
                            // This segment is ahead of the transistion segment
                            if (m_BehindIsActive)
                            {
                                // If behind the the transistion should be active, 
                                // colour it with the in-active colour
                                //g.FillPath(new SolidBrushPlus(m_InactiveColour), segmentPaths[intCount]);
                                g.FillPie(new SolidBrushPlus(m_InactiveColour), segmentRectangles[intCount].X, segmentRectangles[intCount].Y, segmentRectangles[intCount].Width, segmentRectangles[intCount].Height, startAngles[intCount], sweepAngles[intCount]);
                            }
                            else
                            {
                                // If behind the the transistion should be in-active, 
                                // colour it with the active colour
                                //g.FillPath(new SolidBrushPlus(m_ActiveColour), segmentPaths[intCount]);
                                g.FillPie(new SolidBrushPlus(m_ActiveColour), segmentRectangles[intCount].X, segmentRectangles[intCount].Y, segmentRectangles[intCount].Width, segmentRectangles[intCount].Height, startAngles[intCount], sweepAngles[intCount]);
                            }
                        }
                    }
                    else
                    {
                        // Draw all segments in in-active colour if not enabled
                        //g.FillPath(new SolidBrushPlus(m_InactiveColour), segmentPaths[intCount]);
                        g.FillPie(new SolidBrushPlus(m_InactiveColour), segmentRectangles[intCount].X, segmentRectangles[intCount].Y, segmentRectangles[intCount].Width, segmentRectangles[intCount].Height, startAngles[intCount], sweepAngles[intCount]);                       
                    }
                }


                g.FillPie(new SolidBrushPlus(Color.White), innerRectangle.X, innerRectangle.Y, innerRectangle.Width, innerRectangle.Height, (float)0, (float)359.99);
            }
            gOff.DrawString(_Label, new Font(FontFamily.GenericSansSerif,18, System.Drawing.FontStyle.Bold), new SolidBrush(Color.Black), 160, 60);
            e.Graphics.DrawImage(bmpBuff, 0, 0, this.ClientRectangle, GraphicsUnit.Pixel);
        } 
        
        
        private void ProgressDisk_Resize( object sender, System.EventArgs e ) 
        {            
            CalculateSegments(); 
        } 
        
        
        private void ProgressDisk_SizeChanged( object sender, System.EventArgs e ) 
        { 
            CalculateSegments(); 
        } 
        
    } 
    
    
} 
