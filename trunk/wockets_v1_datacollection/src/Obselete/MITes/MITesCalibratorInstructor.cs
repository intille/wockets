using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesCalibratorInstructor.
	/// </summary>
	public class MITesCalibratorInstructor
	{
		private static int NUM_SCREENS = 13;
		private String[] instruction = new String[NUM_SCREENS];
		private String[] instImFile = new String[NUM_SCREENS];
		
		private int screenNum = 0; 
		private bool isDone = false; 

		private MITesSensorCalibrator aMITesSensorCalibrator; 

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesSensorCalibrator"></param>
		public MITesCalibratorInstructor(MITesSensorCalibrator aMITesSensorCalibrator)
		{
			this.aMITesSensorCalibrator = aMITesSensorCalibrator;
						
			instruction[0] = "To start calibration, check the clock on your computer or PDA. Make sure it is properly synchronized with a reliable time as best as possible (e.g. use Atomic Clock Sync on PC).";
			instImFile[0] = "C:\\MITes\\CalibrationImages\\sitcalibrate3.bmp";

			instruction[1] = "Next, make sure the receiver is properly plugged into your computer. Most receivers use the USB port. Make sure there is no other program running that is trying to use the serial port (i.e. COM1). If they are, close them down and restart this program.";
			instImFile[1] = "C:\\MITes\\CalibrationImages\\statuserror.bmp";		

			instruction[2] = "Next you want to put working coin cell batteries in the MITes receivers. You do this as shown in the image below.";
			instImFile[2] = "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[3] = "The next step is to set the ID numbers of the mobile MITes you are using on the receiver. Layout all the MITes on a table as shown below then click on the SensorIDs button.";
			instImFile[3] = "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[4] = "You should see the configuration screen. Look at the sensor ID on each MITe sensor. Find that number on the list, click on the number, and click Add. When you have added all the sensor numbers, then also add number 60. After that, click Set. Then click Done.";
			instImFile[4] = "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[5] = "If the batteries are in the sensors and the receiver is properly plugged in and no applications are using the COM1 port, you should now see data plotting on the screen on the main window for each mobile MITes sensor.";
			instImFile[5] = "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[6] = "Next, if you are using the HR monitor, have the volunteer wear the band around the chest as shown in the image below.";
			instImFile[6] = "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[7] = "Plug in the HR MITes to a 9V battery and place that in the fanny pack or pocket of the volunteer. The HR MITe sensor must stay within about 2 feet of the chest strap. When this is working, you should start to see HR information appear on the main screen.";
			instImFile[7]= "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[8] = "\r\nThe IDs of the sensors being used are listed above. Double check that each mobile MITes ID is there as well as HR if you are using the HR monitor. The numbers should be in chronological order. This does not list beacons. A test for them will follow shortly.";
			instImFile[8]= "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[9] = "\r\nThe above shows the sampling rate of the receiver. Ideally this should be somewhere around 200. If it is not, contact Stephen.";
			instImFile[9]= "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[10] = "The next step is to store the configuration data for each sensor in use. The software must measure the internal noise in the sensor and store it in a file. Lay the sensors on a stable table in the exact orientation as shown below (i.e. flat with battery up). When you are ready, hit the Next button below and wait. Be sure the sensors do not move during this time.";
			instImFile[10]= "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[11] = "Wait 1 minute. Click Done. ";
			instImFile[11]= "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";

			instruction[12] = "\r\nAbove are the noise levels of the sensors. Please record them. It is x,y,z for each sensor, in numeric order by ID. ";
			instImFile[12]= "C:\\MITes\\CalibrationImages\\standcalibrate1.bmp";
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String DoTest8()
		{
			String str = aMITesSensorCalibrator.GetStatusLine();
			return str;
		}
/// <summary>
/// 
/// </summary>
/// <returns></returns>
        //public String DoTest9()
        //{
        //    String str = "Rate: " + aMITesSensorCalibrator.GetLastSamplingRateComputed ();
        //    return str;
        //}
/// <summary>
/// 
/// </summary>
/// <returns></returns>
		public String DoTest11()
		{
			String str = "";
			aMITesSensorCalibrator.SetIsComputingNoise (true);
			return str;
		}
/// <summary>
/// 
/// </summary>
/// <returns></returns>
		public String DoTest12()
		{
			aMITesSensorCalibrator.DoNoiseComputation();
			String str = "" + aMITesSensorCalibrator.GetNoiseDataString ();
			return str;
		}
/// <summary>
/// 
/// </summary>
/// <returns></returns>
		public String DoTest()
		{
			String str = "";
			switch (screenNum)
			{
				case 8:
					str = DoTest8();
					break;
				case 9:
					str = DoTest9();
					break;
				case 11:
					str = DoTest11();
					break;
				case 12:
					str = DoTest12();
					break;
				default: 
					str = "";
					break;
			}
			return str;
		}

		// 
		/// <summary>
		/// Return true if advanced, false if no more screens
		/// </summary>
		/// <returns></returns>
		public bool AdvanceScreen()
		{
			screenNum++; 		
			if (screenNum == NUM_SCREENS)
				isDone = true; 

			return !isDone;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public String GetInstructionText()
		{
			if (!isDone)
				return instruction[screenNum];
			else
				return null;
		}
/// <summary>
/// 
/// </summary>
/// <returns></returns>
		public String GetInstructionImFile()
		{
			if (!isDone)
				return instImFile[screenNum];
			else
				return null;
		}

	}
}
