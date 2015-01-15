package Server;

import java.net.Socket;
import java.net.ServerSocket;

/**
 * 
 * The ServerSocketListener immediately starts waiting for new connections and when they arise 
 * immediately assigns them a ConnectionHandler. The ServerSocketListener is also responsible for 
 * appropriately closing of all connections. 
 * @author Stephan
 */

public class ServerSocketListener extends Thread {

	// ------------------ Instance variables ----------------
	private ServerController Controller;
	private Socket newSocket; //Holder for a socket when it is created when a new connection is established
	private ServerSocket ServerSocket; //the ServerSocket this ServerSocketListener listens to 
	

	// ------------------ Constructor ------------------------
	
	/**
	 * Sets up the instance variables
	 * @param serverController the ServerController of this application
	 * @param ServerSocket the ServerSocket this ServerSocketListener should listen to 
	 */
	public ServerSocketListener(ServerController serverController, ServerSocket serverSocket) {
		// TODO - implement Listener.Listener
		throw new UnsupportedOperationException();
	}

	// ------------------ Queries --------------------------
	// ------------------ Commands --------------------------
	/**
	 * Waits for a new connection on the <code>ServerSocket</code>.
	 * When one is established creates a new ConnectionHandler and adds it to 
	 * the Connections map in the ServerController
	 */
	public void run(){
		// TODO - implement Listener.run
		throw new UnsupportedOperationException();
	}

	/**
	 * Stops the loop in the run method and closes the ServerSocket.
	 */
	public void closeListener() {
		// TODO - implement Listener.closeListener
		throw new UnsupportedOperationException();
	}

}