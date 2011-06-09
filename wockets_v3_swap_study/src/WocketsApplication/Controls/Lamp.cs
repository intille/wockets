//==========================================================================================
//
//		OpenNETCF.Windows.Forms.Lamp
//		Copyright (c) 2004, OpenNETCF.org
//
//		This library is free software; you can redistribute it and/or modify it under 
//		the terms of the OpenNETCF.org Shared Source License.
//
//		This library is distributed in the hope that it will be useful, but 
//		WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
//		FITNESS FOR A PARTICULAR PURPOSE. See the OpenNETCF.org Shared Source License 
//		for more details.
//
//		You should have received a copy of the OpenNETCF.org Shared Source License 
//		along with this library; if not, email licensing@opennetcf.org to request a copy.
//
//		If you wish to contact the OpenNETCF Advisory Board to discuss licensing, please 
//		email licensing@opennetcf.org.
//
//		For general enquiries, email enquiries@opennetcf.org or visit our website at:
//		http://www.opennetcf.org
//
//==========================================================================================
using System;
using System.Drawing;
using System.Collections;
using System.ComponentModel;
#if DESIGN
using System.Globalization;
using System.ComponentModel.Design.Serialization;
using System.Reflection;
#endif
namespace OpenNETCF.Windows.Forms
{
    internal delegate void ChangeHandler();

    /// <summary>
    /// Position of Lamp relative to RoundGauge.
    /// <para><b>New in v1.1</b></para>
    /// <seealso cref="Lamp"/>
    /// <seealso cref="RoundGauge"/>
    /// </summary>
    public enum LampPosition : int
    {
        /// <summary>
        /// Upper Left
        /// </summary>
        UpperLeft = 0,
        /// <summary>
        /// Upper Right
        /// </summary>
        UpperRight = 1,
        /// <summary>
        /// Lower Left
        /// </summary>
        LowerLeft = 2,
        /// <summary>
        /// Lower Right
        /// </summary>
        LowerRight = 3
    }

    /// <summary>
    /// Indicator Lamp class
    /// <para><b>New in v1.1</b></para>
    /// </summary>
    /// <seealso cref="RoundGauge"/>
#if DESIGN
	[DesignTimeVisibleAttribute(false), 
	TypeConverter("LampConverter")]
#endif
    public class Lamp : System.ComponentModel.Component
    {
        private Color offColor;
        private Color onColor;
        private Color bezelColor;
        private Point upperRight;
        private int bezelWidth;
        private int diameter;
        private bool state;
        private LampPosition position;
        private bool visible = false;

        /// <summary>
        /// Lamp constructor
        /// </summary>
        public Lamp()
        {
            offColor = Color.DarkRed;
            onColor = Color.Red;
            bezelColor = Color.SlateGray;
            bezelWidth = 2;
            diameter = 0;
            upperRight = new Point(0, 0);
            position = LampPosition.UpperLeft;
        }

        internal Lamp(Point UpperRight, int Diameter, LampPosition Position)
            : base()
        {
            upperRight = UpperRight;
            diameter = Diameter;
            position = Position;
        }

        internal Point UpperRight
        {
            get
            {
                return upperRight;
            }
            set
            {
                upperRight = value;
            }
        }

        internal int Diameter
        {
            get
            {
                return diameter;
            }
            set
            {
                diameter = value;
            }
        }

        /// <summary>
        /// Sets whether the lamp is Visible or not
        /// </summary>
        public bool Visible
        {
            get
            {
                return visible;
            }
            set
            {
                visible = value;
            }
        }

        /// <summary>
        /// The position of the lamp relative to its parent RoundGauge
        /// <seealso cref="RoundGauge"/>
        /// </summary>
        public LampPosition Position
        {
            get
            {
                return position;
            }
            set
            {
                position = value;
            }
        }

        /// <summary>
        /// The state (on or off) of the Lamp
        /// </summary>
        public bool State
        {
            get
            {
                return state;
            }
            set
            {
                state = value;
            }
        }

        /// <summary>
        /// The lamp's color when its State is <b>true</b>
        /// <seealso cref="State"/>
        /// </summary>
        public Color OnColor
        {
            get
            {
                return onColor;
            }
            set
            {
                onColor = value;
            }
        }

        /// <summary>
        /// The lamp's color when its State is <b>false</b>
        /// <seealso cref="State"/>
        /// </summary>
        public Color OffColor
        {
            get
            {
                return offColor;
            }
            set
            {
                offColor = value;
            }
        }

        /// <summary>
        /// The border (bezel) color of the lamp
        /// </summary>
        public Color BezelColor
        {
            get
            {
                return bezelColor;
            }
            set
            {
                bezelColor = value;
            }
        }

        /// <summary>
        /// The border (bezel) width of the lamp
        /// </summary>
        public int BezelWidth
        {
            get
            {
                return bezelWidth;
            }
            set
            {
                bezelWidth = value;
            }
        }

        internal void Draw(Graphics TargetGraphics)
        {
            Brush brush;

            brush = new SolidBrush(bezelColor);
            TargetGraphics.FillEllipse(brush, upperRight.X - diameter, upperRight.Y - diameter, diameter, diameter);

            brush = (state) ? new SolidBrush(onColor) : new SolidBrush(offColor);
            TargetGraphics.FillEllipse(brush, upperRight.X - diameter + (bezelWidth / 2), upperRight.Y - diameter + (bezelWidth / 2), diameter - bezelWidth, diameter - bezelWidth);

            brush.Dispose();
        }

    }

    /// <summary>
    /// A Collection of Lamp classes
    /// <para><b>New in v1.1</b></para>
    /// </summary>
    /// <seealso cref="Lamp"/>
    public class Lamps : CollectionBase
    {
        internal event ChangeHandler LampsChanged;

        /// <summary>
        /// Adds a Lamp to the collection
        /// <seealso cref="Lamp"/>
        /// </summary>
        /// <param name="newLamp"></param>
        public void Add(Lamp newLamp)
        {
            if (LampsChanged != null)
            {
                LampsChanged();
            }

            List.Add(newLamp);
        }

        /// <summary>
        /// Retrieves the Lamp at a specific <b>index</b>
        /// <seealso cref="Lamp"/>
        /// </summary>
        public Lamp this[int index]
        {
            get
            {
                return (Lamp)List[index];
            }
            set
            {
                if (LampsChanged != null)
                {
                    LampsChanged();
                }

                List[index] = value;
            }
        }
    }

#if DESIGN
	internal class LampConverter : TypeConverter
	{
		public override bool CanConvertTo(ITypeDescriptorContext context, Type destinationType)
		{
			if (destinationType == typeof(InstanceDescriptor))
			{
				return true;
			}

			return base.CanConvertTo(context, destinationType);
		}

		public override object ConvertTo(ITypeDescriptorContext context, CultureInfo culture, object value, Type destinationType)
		{
			if (destinationType == typeof(InstanceDescriptor) && value is Lamp)
			{
				Lamp lamp = (Lamp)value;
              
				ConstructorInfo ci = typeof(Lamp).GetConstructor(new Type[] {});
				if (ci != null)
				{
					return new InstanceDescriptor(ci, null, false);
				}
			}
			return base.ConvertTo(context, culture, value, destinationType);
		}
	}
#endif
}
