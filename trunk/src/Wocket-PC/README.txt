This project is a Java application for computer that calibrates the sampling rate of Wockets.
To run the code using NetBeans platform you need to:

•	Install NetBeans (http://netbeans.org/) 
•	Make a new project
•	Delete the files in the folder of the project (usually in Documents\NetbeensProjects\)
•	Copy the file of  Wocket-PC  folder to the folder of the project
•	Run the "mainJFrame.java" in UserInterface folder  

The application allows you to calibrate several Wockets consequently with different sampling rates. The application, first measures the current sampling rate of the wocket. If sampling rate is not within acceptable range (the highest precision that could), it starts calibrating the Wocket. 

Eclipse doesn’t support the Swing library which is used in this project to design graphical user interface. But, it is possible to execute calibration without graphical user interface. After importing the project in Eclipse, you should run "MyPcClient.Java" in Bluetooth folder (Eclipse gives error on UserInterface folder, ignore that and proceed to run the program. The Eclipse version of the program sets the sampling rate to 40. If you want to set other sampling rates, you need to change the call to calibration function in MyPcClient.Java.
