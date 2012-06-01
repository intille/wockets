package bluetooth;

import java.io.*;
import javax.bluetooth.*;
import javax.microedition.io.*;
 
/**
* Class that implements an SPP Server which accepts single line of
* message from an SPP client and sends a single line of response to the client.
*/
public class MyPcServer {
	//********************test code 1*******************************************************************************************
    //start server
    /*private void startServer() throws IOException{
 
        //Create a UUID for SPP
        UUID uuid = new UUID("1101", true);
        //Create the servicve url
        String connectionString = "btspp://localhost:" + uuid +";name=Sample SPP Server";
       
        //open server url
        StreamConnectionNotifier streamConnNotifier = (StreamConnectionNotifier)Connector.open( connectionString );
       
        //Wait for client connection
        System.out.println("\nServer Started. Waiting for clients to connect...");
        StreamConnection connection=streamConnNotifier.acceptAndOpen();
 
        RemoteDevice dev = RemoteDevice.getRemoteDevice(connection);
        System.out.println("Remote device address: "+dev.getBluetoothAddress());
        System.out.println("Remote device name: "+dev.getFriendlyName(true));
       
        //read string from spp client
        InputStream inStream=connection.openInputStream();
        BufferedReader bReader=new BufferedReader(new InputStreamReader(inStream));
        String lineRead=bReader.readLine();
        System.out.println(lineRead);
       
        //send response to spp client
        OutputStream outStream=connection.openOutputStream();
        PrintWriter pWriter=new PrintWriter(new OutputStreamWriter(outStream));
        pWriter.write("Response String from SPP Server\r\n");
        pWriter.flush();
 
        pWriter.close();
        streamConnNotifier.close();
 
    }
 
 
    public static void main(String[] args) throws IOException {
       
        //display local device address and name
        LocalDevice localDevice = LocalDevice.getLocalDevice();
        System.out.println("Address: "+localDevice.getBluetoothAddress());
        System.out.println("Name: "+localDevice.getFriendlyName());
       
        MyPcServer myPcServer=new MyPcServer();
        myPcServer.startServer();
       
    }*/
    
  //********************test code 2*******************************************************************************************
	public final UUID uuid = new UUID(                              //the uid of the service, it has to be unique,
			"27012f0c68af4fbf8dbe6bbaf7aa432a", false); //it can be generated randomly
    public final String name = "Echo Server";                       //the name of the service
    public final String url  =  "btspp://localhost:" + uuid         //the service url
                                + ";name=" + name 
                                + ";authenticate=false;encrypt=false;";
    LocalDevice local = null;
    StreamConnectionNotifier server = null;
    StreamConnection conn = null;

    public MyPcServer() {
        try {
            System.out.println("Setting device to be discoverable...");
            local = LocalDevice.getLocalDevice();
            local.setDiscoverable(DiscoveryAgent.GIAC);
            System.out.println("Start advertising service...");
            server = (StreamConnectionNotifier)Connector.open(url);
            System.out.println("Waiting for incoming connection...");
            conn = server.acceptAndOpen();
            System.out.println("Client Connected...");
            DataInputStream din   = new DataInputStream(conn.openInputStream());
            while(true){
                String cmd = "";
                char c;
                while (((c = din.readChar()) > 0) && (c!='\n') ){
                    cmd = cmd + c;
                }
                System.out.println("Received " + cmd);
            }
            
        } catch (Exception  e) {System.out.println("Exception Occured: " + e.toString());}
    }
    
    public static void main (String args[]){
    	MyPcServer myPcServer = new MyPcServer(); 
    }
}
