using System;
using System.Collections.Generic;
using System.Text;
using System.Drawing;

namespace WocketsApplication.Controls.Utils
{
    public class GUIHelper
    {
        public static float DpiX;
        public static float DpiY;
        public static int Length = 4;

        public static string FONT_FAMILY = "Microsoft Sans Serif";
        public const int MAX_FONT = 64;
        public const int MIN_FONT = 9;

        public static Size CalculateBestListSize(Size oldSize, Point location, int entries, Size layoutSize, string s, float scale_width, float scale_height)
        {
            float hRatio = ((layoutSize.Height - location.Y) * scale_height) / oldSize.Height;//extent.Height;
            float wRatio = ((layoutSize.Width - location.X) * scale_width) / oldSize.Width;// extent.Width;
            float ratio = (hRatio < wRatio) ? hRatio : wRatio;
            return new Size((int)(wRatio * oldSize.Width), (int)(hRatio * oldSize.Height));
        }

        public static Font CalculateBestFitFont(Size oldSize, float minFontSize, float maxFontSize, Size layoutSize, string s, Font f, float scale_width, float scale_height)
        {
            if (maxFontSize == minFontSize)
                f = new Font(FONT_FAMILY, minFontSize, f.Style);


            if (maxFontSize <= minFontSize)
                return f;

            float hRatio = (layoutSize.Height * scale_height) / oldSize.Height;//extent.Height;
            float wRatio = (layoutSize.Width * scale_width) / oldSize.Width;// extent.Width;
            float ratio = (hRatio < wRatio) ? hRatio : wRatio;

            float newSize = f.Size * ratio;

            if (newSize < minFontSize)
                newSize = minFontSize;
            else if (newSize > maxFontSize)
                newSize = maxFontSize;

            f = new Font(FONT_FAMILY, newSize, f.Style);


            return f;
        }

        public static Font CalculateBestFitFontStart(Size oldSize, float minFontSize, float maxFontSize, Size layoutSize, string s, Font f, float scale_width, float scale_height)
        {
            if (maxFontSize == minFontSize)
                f = new Font(FONT_FAMILY, minFontSize, f.Style);


            if (maxFontSize <= minFontSize)
                return f;

            float hRatio = (layoutSize.Height * scale_height) / oldSize.Height;//extent.Height;
            float wRatio = (layoutSize.Width * scale_width) / oldSize.Width;// extent.Width;
            float ratio = (hRatio < wRatio) ? hRatio : wRatio;

            float newSize = f.Size * (5 / s.Length);

            if (newSize < minFontSize)
                newSize = minFontSize;
            else if (newSize > maxFontSize)
                newSize = maxFontSize;

            f = new Font(FONT_FAMILY, newSize, f.Style);

            return f;
        }

        public static Font CalculateBestFitFont(Graphics g, float minFontSize, float maxFontSize, Size layoutSize, string s, Font f, float scale_width, float scale_height)
        {
            if (maxFontSize == minFontSize)
                f = new Font(FONT_FAMILY, minFontSize, f.Style);

            SizeF extent = g.MeasureString(s, f);

            if (maxFontSize <= minFontSize)
                return f;

            float hRatio = (layoutSize.Height * scale_height) / extent.Height;
            float wRatio = (layoutSize.Width * scale_width) / extent.Width;
            float ratio = (hRatio < wRatio) ? hRatio : wRatio;

            float newSize = f.Size * ratio;

            if (newSize < minFontSize)
                newSize = minFontSize;
            else if (newSize > maxFontSize)
                newSize = maxFontSize;

            f = new Font(FONT_FAMILY, newSize, f.Style);
            extent = g.MeasureString(s, f);

            return f;
        }
    }
}
