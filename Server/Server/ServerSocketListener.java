package Server;

import java.io.IOException;
import java.net.Socket;
import java.net.ServerSocket;
import java.net.SocketException;

/** 
 * The ServerSocketListener starts waiting for new connections and when they arise 
 * immediately assigns them a ConnectionHandler. The ServerSocketListener is also responsible for 
 * appropriately closing of all connections. 
 * @author Stephan
 */

public class ServerSocketListener extends Thread {

	// ------------------ Instance variables ----------------
	private ServerController controller;
	private Socket newSocket; //Holder for a socket when it is created when a new connection is established
	private ServerSocket serverSocket; //the ServerSocket this ServerSocketListener listens to 
	private ConnectionHandler newConnectionHandler; //the ConnectionHandler object for a new client
	private boolean waitForConnections; //Flag for the while loop in run(), if this is set to false the class stops waiting for new connections and frees up its assets 


	// ------------------ Constructor ------------------------
	
	/**
	 * Sets up the instance variables
	 * @param serverController the ServerController of this application
	 * @param ServerSocket the ServerSocket this ServerSocketListener should listen to 
	 */
	public ServerSocketListener(ServerController newServerController, ServerSocket newServerSocket) {
		serverSocket = newServerSocket;
		controller = newServerController;
		waitForConnections = true;
		controller.writeToGUI("ServerSocketListener created");
	}

	// ------------------ Queries --------------------------
	// ------------------ Commands --------------------------
	/**
	 * Waits for a new connection on the <code>ServerSocket</code>.
	 * When one is established creates a new ConnectionHandler and adds it to 
	 * the Connections map in the ServerController
	 */
	public void run(){
		while (waitForConnections == true){
			try{
				newSocket = serverSocket.accept(); //Waits till a new TCP connection is made on this ServerSocket
				controller.writeToGUI("A new connection has been accepted.");
				newConnectionHandler = new ConnectionHandler(controller, newSocket); //Create a new Connectionhandler for the socket
				//The ConnectionHanlder notifies it's existence to the ServerController itself so that doesn't need to happen here
				newConnectionHandler.start();
				controller.writeToGUI("ConnectionHandler Started");
			} catch (SocketException s){
				//TODO find out why this exception is thrown				
				throw new UnsupportedOperationException();
				
			} catch (IOException i){
				//TODO find out why this exception is thrown				
				throw new UnsupportedOperationException();
			}
		}
	}

	/**
	 * Stops the loop in the run method and closes the ServerSocket.
	 */
	public void closeListener() {
		waitForConnections = false;
		
		try{
			serverSocket.close();
		} catch (IOException i){
			//TODO find out why this exception is thrown				
			throw new UnsupportedOperationException();
		}

	}

}