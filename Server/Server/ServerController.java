package Server;

/**
 * This Class initializes all other Classes and hence facilitates the creation of games,
 * houses the logic for the GUI, creates the ServerSocketListener for the serversocket 
 * and will implement the functionalities of any of the facultative extensions.
 * @author Stephan
 */

import java.util.List;
import java.util.Map;

import View.GUI;

public class ServerController {
	
	// ------------------ Instance variables ----------------
	private Map<String, ConnectionHandler> connections; //Keeps track of all current connections and their nicknames
	private Map<GameController, List<ConnectionHandler>> games; //Keeps track of alle current games and their respective ConnectionHandlers
	private GUI view;
	private ServerSocketListener serverSocketListener;
	
	// ------------------ Constructor ------------------------
	/**
	 * Creates a ServerSocketListener on <code>portNumber</code> and creates a ServerGui class. 
	 * Initializes all Instance Variables.
	 * @param portNumber the port the server uses for connections
	 */
	public ServerController(int portNumber) {
		// TODO - implement ServerController.ServerController
		throw new UnsupportedOperationException();
	}
	// ------------------ Queries --------------------------
	// ------------------ Commands --------------------------
	/**
	 * Creates a ServerSocketListeren object on port <code>portNumber</code>
	 * @param portNumber the number on what port the listener should wait for connections
	 */
	public void startServerSocketListener(int portNumber) {
		// TODO - implement ServerController.startServerSocketListener
		throw new UnsupportedOperationException();
	}

	/**
	 * Creates a GameController object which starts a game with players <code>player1</code> and <code>player2</code>
	 * @param player1 the first player 
	 * @param player2 the second player
	 */
	public void startGame(ConnectionHandler player1, ConnectionHandler player2) {
		// TODO - implement ServerController.startGame
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Creates a new ServerGUI object
	 */
	public void buildServerGUI(){
		// TODO - implement ServerController.buildServerGUI
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Adds a ConnectionHandler to the Connections Map
	 * @param newPlayer the ConnectionHandler to be added
	 */
	public void addConnectionHandler(ConnectionHandler newPlayer) {
		// TODO - implement ServerController.addConnectionHandler
		throw new UnsupportedOperationException();
	}

	/**
	 * Removes a ConnectionHandler from the Connections Map
	 * @param removePlayer the ConnectionHandler to be removed 
	 */
	public void removeConnectionHandler(ConnectionHandler removePlayer) {
		// TODO - implement ServerController.removeConnectionHandler
		throw new UnsupportedOperationException();
	}

}