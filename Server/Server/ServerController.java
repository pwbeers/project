package Server;

/**
 * This Class initializes all other Classes and hence facilitates the creation of games,
 * houses the logic for the GUI, creates the ServerSocketListener for the serversocket 
 * and will implement the functionalities of any of the facultative extensions.
 * @author Stephan
 */

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import View.View;

public class ServerController {
	
	// ------------------ Instance variables ----------------
	private Map<String, ConnectionHandler> connections; //Keeps track of all current connections and their nicknames
	private Map<GameController, List<ConnectionHandler>> games; //Keeps track of alle current games and their respective ConnectionHandlers
	private View view;
	private ServerSocketListener serverSocketListener;
	private final String EXTENSIONS ="NONE"; //The AMULET value for which extensions are supported
	
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
	/**
	 * Returns the AMULET value for which extensions are supported.
	 * @return
	 */
	public String getExtensions(){
		return EXTENSIONS;
	}
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
	 * This methods handles the situation when there is a new player without challange capabilities
	 * It looks for any other players which are not in a game and selects one randomly
	 * It puts them both in a GameController
	 * @param player1 the first player 
	 * @param player2 the second player
	 */
	public void startGame(ConnectionHandler player1) {
		// TODO - implement ServerController.startGame
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Creates a GameController object which starts a game with players <code>player1</code> and <code>player2</code>
	 * Used when both players are known.
	 * @param player1 the first player 
	 * @param player2 the second player
	 */
	public void startChallangeGame(ConnectionHandler player1, ConnectionHandler player2) {
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
	 * @param nickName the Nickname of the player
	 */
	public void addConnectionHandler(String nickName, ConnectionHandler newPlayer) {
		// TODO - implement ServerController.addConnectionHandler
		throw new UnsupportedOperationException();
		//because there is a new connection it should now be placed in a game
	}

	/**
	 * Removes a ConnectionHandler from the Connections Map
	 * @param removePlayer the ConnectionHandler to be removed 
	 */
	public void removeConnectionHandler(ConnectionHandler removePlayer) {
		// TODO - implement ServerController.removeConnectionHandler
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Prints a message to the GUI
	 * @param string
	 */
	public void writeToGUI(String string) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();		
	}
	
	/**
	 * Because of the AMULET protocol the extensions which a client supports must be kept track of.
	 * The ServerController puts the connectionHandler in the  different extention sets
	 * @param extensions the ArrayList housing the extensions
	 * @param connectionHandler
	 */
	public void matchExtensions(ArrayList<String> extensions,
			ConnectionHandler connectionHandler) {
		// TODO Auto-generated method stub
		// sort the connection handler into the differen extention sets
		//write extensions reader
		
	}

}