The goal of this open source project is to create software and hardware that permits automatic, 24/7 physical activity and context detection on common mobile phones. We are doing this by iteratively designing and testing Wockets -- miniature, low-cost hardware devices that will measure human motion using accelerometers. Wockets will send data to mobile phones that are processed by software running on the phone to automatically detect type, duration and intensity of physical activity.

**[Project Home Page](http://web.mit.edu/wockets)**

We are currently maintaining our code (firmware, phone, and PC tools) on Google Code.


---


Update from 8/24/2011. For quite some time, the focus of the team has been on the Windows Mobile Platform, but we have recently switched to Android. We are in the process of organizing the code we do have for Android to make it easier for developers to get involved in the project. Until recently, we also had relatively little extra hardware, but we have a bit more supply now. The bottom line for developers who have expressed an interest in this project is that it is now much easier to start contributing and it should become more so as time goes on.


---


The newer Android code is located under /trunk/android. This is where the action will be.


---


The notes below refer to the Windows Mobile code, which we do not intend to develop any further.

## Current Wockets Release 1.23 ##
(February 9, 2010)
The release version comes in the form of a zip file with 2 applications:

**- PC Application:**
This includes (1) a Data Merger that synchronizes data from multiple wockets and other devices including MITes, Sensewear, Oxycon, Actigraphs etc. (2) a visualization tool that allows you to view the data.  (3) a time synchronizer tool that synchronizes time on multiple PC prior to data collection and (4) an audio annotation tool that generates an xml annotation file from audio annotation files. For detailed information on how to install the software, please visit the [Wockets Installation Instruction](http://wockets.wikispaces.com/Wockets+Software+Installation) on Wockets Wiki.

**- Phone Application:**
This is a setup.exe file that you can run from your PC and it will install the wockets software on your Windows Mobile phones. For detailed information on how to install the software, please visit the [Wockets Installation Instruction](http://wockets.wikispaces.com/Wockets+Software+Installation) on Wockets Wiki.

[![](http://wockets.wikispaces.com/file/view/download_button.gif)](http://wockets.googlecode.com/files/Wockets.zip)



---


## Wocket Document ##
This document includes information on:

1- What is the Wocket and how does it work

2- Wockets interface specification

3- How to work with Wockets

[Wocket Document](https://docs.google.com/document/d/1OWHHmzhNMPqJD4ha7WQq3uaaKJEEW5NZwat4WxyG55A/edit)



---


## Wockets Source Code ##

This is the code repository for [MIT's Wockets Project](http://web.mit.edu/wockets). The software consists of a set of libraries that collect data from wireless miniature accelerometers called Wockets. The code is written in C# and is released under an [MIT Public License](http://www.opensource.org/licenses/mit-license.php).

The software is organized into 3 components:

**1- The Source Directory (`svn/trunk/src`):** This includes the C# source files that are located under the [Source Tab](http://code.google.com/p/wockets/source/checkout). The source code is organized into multiple subdirectories. Two particularly important subdirectories are `src/Wockets` that includes the source code for communicating with wockets, decoding and logging accelerometer data and `src/WocketsWeka` that includes a partially ported and modified version of [Weka](http://www.cs.waikato.ac.nz/ml/weka/) in C#.

**2- The Projects Directory (`svn/trunk/projects`):** This includes the project files for visual studio 2008 for different device platforms (PocketPC and PC).

**3- The [Bin.zip](http://wockets.googlecode.com/files/bin.zip):** The file includes configuration files and external dlls to compile the project in visual studio 2008 and will include the binaries generated during compilation.



---



## Instructions for Compiling and Running the Wockets Code ##

**Prerequisites**

1. Microsoft Visual Studio 2005. The code has not been tested on later versions of Microsoft Visual Studio.

2. SVN Software such as [SVN Tortoise](http://tortoisesvn.tigris.org/).

3. [ActiveSync](http://www.microsoft.com/windowsmobile/en-us/help/synchronize/ActiveSync-download.mspx) for Windows XP users. Windows Vista ships with Microsoft Mobile Center and therefore Activesync is not needed.

4. A Windows Mobile phone with Microsoft Bluetooth Stack. We currently do not support Widcomm phones but will add support shortly.

**Instructions**

1. Install an SVN software such as [SVN Tortoise](http://tortoisesvn.tigris.org/) to checkout the wockets source tree.

2. Once the program is installed. Create a local directory on your disk where you can checkout the wockets source tree and projects.

3. Go to the [Source Tree Tab](http://code.google.com/p/wockets/source/checkout)  for instructions on how to checkout the project. The project supports 2 user groups:

**a. Members:** As a member, you can checkout the source tree, modify it and update the svn repository. This access level requires authentication. If you would like to contribute to the source tree, please email either [Dr. Stephen Intille](mailto:intille@mit.edu), [Dr. Fahd Albinali](mailto:albinali@mit.edu) or [Selene Mota](mailto:atenea@media.mit.edu).

**b. Non-members:** As a non-member, you will be able to checkout the source tree and modify it on your local machine. You won’t be able to commit any changes to the SVN repository. This access level does not require authentication.

4. Use your SVN software to checkout the source tree and project files from the repository. For [SVN Tortoise](http://tortoisesvn.tigris.org/) users, you simply need to right-click on the directory that you just created and choose `checkout`. You will be asked to provide a url for the SVN repository, please use the information listed under the [Source Tree Tab](http://code.google.com/p/wockets/source/checkout).

5. Download the most recent [Bin Zip File](http://wockets.googlecode.com/files/bin.zip) under the Download Tab.

6. Uncompress the zip file in the root source code directory (i.e. where both `src/` and `projects/` exist) so that you end up with the `src` directory, the `projects` directory and the `bin` directory at the same level.

7. To run the Phone version of the code, navigate under the source directory to `projects/PPC` and click `WocketsPPC.sln`. The PC version is not fully supported at the moment.

8. Using visual Studio’s Solution Explorer, set the `WocketsApplication` as the startup project.

9. Connect a phone with a Microsoft Bluetooth Stack to your PC. This should automatically run [ActiveSync](http://www.microsoft.com/windowsmobile/en-us/help/synchronize/ActiveSync-download.mspx) or Microsoft Mobile Center to connect both your PC and the phone. If you do not have [ActiveSync](http://www.microsoft.com/windowsmobile/en-us/help/synchronize/ActiveSync-download.mspx), download it and install it. Users of Windows Vista use Microsoft Mobile Center instead.

10. Compile and Build the code.

11. If your code compiles successfully, you can deploy to the Phone. The code will deploy to `/Device/Program Files/Wockets`. Once it is deployed, copy the contents of the following folder from your PC `bin/NeededFiles` to your phone at `/Device/Program Files/Wockets/NeededFiles`.

12. Before running the code, you will have to edit some configuration files to look for the right wocket. For detailed instructions on how to do that, scroll below and read our  **Tips for Running the Code**.



---



## Special Instructions for Members ##

**1. Don’t Commit Binaries:** Microsoft Visual Studio automatically creates many directories when compiling the code. Some of these directories are created within the source tree and may include intermediate object files that can take substantial space and therefore should not be committed to the source tree. **To avoid committing object or temporary files to the source tree, please follow these instructions before applying your first commit:**

a. First, compile the code on your local machine.

b. Go to the main `bin/` directory (that you unzipped), add it to the ignore list in your SVN program. In [SVN Tortoise](http://tortoisesvn.tigris.org/), this can be done by right clicking on the directory and choosing `Ignore List`. If you are asked to ignore the directory by extension or by name, choose by name.

c. Go to the PPC projects directory under `projects/PPC`. Add any subdirectories to the SVN ignore list.

d. Go to the PC projects directory under `projects/PC`. Add any subdirectories to the SVN ignore list.

e. Go to each project directory under `src/` and ignore any subdirectory with the name obj or bin. For instance, ignore `src/Wockets/obj/`

**2. Keep Project Files and Source Files Separate:** We would like to keep our source tree and project files in separate directories. Unfortunately, if you use the Solution Explorer in visual studio to add a file, the file is not added to the right location in the source tree. Instead, it is added to the directory where the project file lies. To maintain source files and project files in separate directories, each time you add a project file,  you **HAVE** to follow these steps:

a. Add the project file in the solution explorer of Microsoft Visual Studio.

b. Open a file explorer and navigate to `/projects` directory, you should see a copy of the file that you just added. Move this file to the appropriate location under `/src` directory. Make sure that the file has been moved and not copied.

c. Open the corresponding project file (under `/projects`) in a text editor. Search for the file that you just added, and make it point to the new location.

d. Your project will automatically reload in Visual Studio and should point to the new file. (You will see an icon with an arrow next to the filename in the solution explorer)

e. Now you can **COMMIT** the source tree.



---



## Tips for Running the Code and Common Issues ##

**1. Bluetooth Stack:** Many popular phones do not have Microsoft Bluetooth stacks but rather Widcomm stacks. At the moment, we do not support Widcomm but are planning to add support in the near future. Make sure that you are running the code on a platform that runs a Microsoft stack.

**2. Wockets Configurations:** To run the code, you need at least 1 wocket and you need to configure the software to look for it. After running the code, you will be prompted to choose a sensor configuration. The list that is displayed is generated from `bin/NeededFiles/Master/WocketsControllers.xml`.  This XML file points to different wockets configurations such as:

```
<WOCKETCONTROLLER>
	<NAME>Demo  3 Wockets</NAME>
	<DESCRIPTION>3 Wockets.</DESCRIPTION>
	<CONFIGURATIONFILE>SensorData5.xml</CONFIGURATIONFILE>
</WOCKETCONTROLLER>
```

3. To modify the configuration for the above element you need to modify `SensorData5.xml`. The file can be found at `bin/NeededFiles/SensorConfigurations/SensorData5.xml`.

4. An example of this file with 1 wocket is shown below:

```
<SENSORDATA dataset="house_n data" xmlns="urn:mites-schema">
<RECEIVERS>	
	<RECEIVER id="0" type="RFCOMM" MacAddress="00066601ab5b" PIN="1234" PortNumber="9" Parity="False" StopBit="True" BaudRate="57600" BufferSize="4096" MaxSR="70" />				
</RECEIVERS>
<DECODERS>
	<DECODER id="0" type="Wockets" />
</DECODERS>
<SENSORS>
	<SENSOR class="Wockets" type="ACCEL">
		<ID id="0"></ID>
		<SR text="60"></SR>
		<RANGE min="0" max="1024"/>
		<OBJECT text=""></OBJECT>
		<LOCATION text="Right Wrist"></LOCATION>
		<DESCRIPTION text="acc"></DESCRIPTION>
		<RECEIVER id="0"></RECEIVER>
		<DECODER id="0"></DECODER>
		<CALIBRATION  x1g="785.10" xn1g="270.93" y1g="711.35" yn1g="206.18" z1g="764.29" zn1g="273.37" xstd="0.21" ystd="0.21" zstd="0.22" />
	</SENSOR>
</SENSORS>
</SENSORDATA>
```

5. There are three important XML elments in the above file:

**a. Receivers:** This lists the number of reception channels that the configuration requires. Because wockets use Bluetooth and it is a point to point protocol, each wocket has to define one receiver element with the following parameters:

**i. ID:** Receivers has to be assigned unique incremental ids starting from 0. For example, if you have 2 wockets, you will define 2 receiver elements with ids 0 and 1.

**ii. Type:** The type of the reception protocol has to be RFCOMM since the wockets use RFCOMM on top of Bluetooth to exchange data with other devices.

**iii. Mac Address and PIN:** You need to make sure that the MAC address and PINs are correct.

**iv. Other Options:** are currently not used but will be used in the near future, so you should keep them as they are for the moment.

**b. Decoders:** This lists the number of decoders needed to decode wockets data. In theory, you can have 1 decoder for multiple wockets but at the moment, we require that each wocket has its own decoder. Again, each decoder has to have an ID and it should be unique and incremental from 0. For example, if you have 2 wockets, you would have 2 decoders with IDs 0 and 1.

**c. Sensors:** This lists the number of wockets that you have in the setup. Each wocket should be of class `Wockets` and should have a unique incremental ID from 0. Importantly, the wocket should point to its `Receiver` and `Decoder` in its element using their IDs.  `SR` is the sampling rate which is approximately 65 Hz and `Calibration` are values that allow us to reconstruct the sensitivity curves for each wocket.


For more information on the project, please visit the [Project Home Page](http://web.mit.edu/wockets)