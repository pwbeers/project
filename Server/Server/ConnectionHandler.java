package Server;

import java.io.BufferedReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.util.ArrayList;

import com.sun.java_cup.internal.runtime.Scanner;

/**
 * Manages a single TCP connection with a Player. It handles some of the logic
 * for client to client-user communication and  sends the commands through to 
 * the ServerController and GameController with which it doesn’t do anything itself. 
 * @author Stephan
 */
public class ConnectionHandler extends Thread {

	// ------------------ Instance variables ----------------
	private ServerController controller;
	private Socket socket;
	private String nickName; //the nickname of the player connected to this handler
	private GameController gameController;
	
	private PrintWriter writer; //for writing back over the socket
	private BufferedReader bufferedReader; //for reading from the socket
	private Scanner scanner; //scanner for the switch, reading the commands
	private String newCommand; //command for switch
	private ArrayList<String> arguments; //Argument for switch

	// ------------------ Constructor ------------------------
	/**
	 * Creates a BufferedReader connected to the inputstream of this socket.
	 * Creates a PrintWriter for writing to the Client.
	 * @param controller //the current ServerController
	 * @param socket /the socket created by the ServerController
	 */
	public ConnectionHandler(ServerController controller, Socket socket) {
		// TODO - implement ConnectionHandler.ConnectionHandler
		throw new UnsupportedOperationException();
	}

	// ------------------ Queries --------------------------
	/**
	 * Returns the current GameController if there is one
	 * @return the current Game Controller
	 */
	public GameController getGameController() {
		// TODO - implement ConnectionHandler.getGameController
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Returns the current NickName if there is one
	 * @return the current NickName
	 */
	public String getNickName() {
		// TODO - implement ConnectionHandler.getNickName
		throw new UnsupportedOperationException();
	}
	// ------------------ Commands --------------------------
	/**
	 * Waits for a new line. When one is received sends it to the commandReader
	 */
	public void run(){
		// TODO - implement ConnectionHandler.run
		throw new UnsupportedOperationException();
		
	}
	/**
	 * Sets the GameController attribute for referencing when in a game
	 * @param gameController the current GameController
	 */
	public void setGameController(GameController gameController) {
		// TODO - implement ConnectionHandler.setGameController
		throw new UnsupportedOperationException();
	}

	/**
	 * Sets the NickName for this Player
	 * @param name the NickName
	 */
	public void setNickName(String name) {
		// TODO - implement ConnectionHandler.setName
		throw new UnsupportedOperationException();
	}

	/**
	 * Switches all the commands in the AMULET protocol to the right parts of the system using a switch
	 * 
	 * @param newCommand a new Command which has been detected
	 */
	public void commandReader(String newCommand) {
		// TODO - implement ConnectionHandler.commandReader
		throw new UnsupportedOperationException();
	}

	

}