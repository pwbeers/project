package Server;

/**
 * This Class initializes all other Classes and hence facilitates the creation of games,
 * houses the logic for the ServerGUI, creates the ServerSocketListener for the serversocket 
 * and would implement the functionalities of any of the facultative extensions.
 * @author Stephan
 */

//TODO handle close events properly

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.ServerSocket;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;
import View.ServerGui;


public class ServerController implements ActionListener{
	
	// ------------------ Instance variables ----------------
	private ServerGui serverGUI; //the ServerGui for this Server
	private ServerSocket serverSocket; //The serverSocket this server is on
	private ServerSocketListener serverSocketListener; //The ServerSocketListener of this server
	
	private TreeMap<String, ConnectionHandler> connections; //Keeps track of all current connections and their nicknames
	private TreeMap<String, List<ConnectionHandler>> games; //Keeps track of all current games and their respective ConnectionHandlers
	
	private String extensions; //The AMULET value for which extensions are supported
	private List<ConnectionHandler> normalPlayers; //Lists players with no extensions
	private List<ConnectionHandler> challengePlayers;//Lists players who support the AMULET Challenge extension
	private List<ConnectionHandler> chatPlayers;//Lists players who support the AMULET chat extension
	private List<ConnectionHandler> leaderboardPlayers;//Lists players who support the AMULET leaderboard extension
	private List<ConnectionHandler> securityPlayers;//Lists players who support the AMULET security extension
	
	// ------------------ Constructor ------------------------
	/**
	 * Creates a ServerSocketListener which creates a ServerGui class. 
	 * Sets the AMULET-extensions to "NONE"
	 * Initializes all Instance Variables.
	 */
	public ServerController() {
		serverGUI = new ServerGui(this);
		writeToGUI("ServerGUI has been created");
		
		extensions = "NONE"; //We hardcode the extensions, there is not yet support to en/dis-able them
		connections = new TreeMap<String, ConnectionHandler>();
		games = new TreeMap<String, List<ConnectionHandler>>();
		
		normalPlayers = new ArrayList<ConnectionHandler>();
		challengePlayers = new ArrayList<ConnectionHandler>();
		chatPlayers = new ArrayList<ConnectionHandler>();
		leaderboardPlayers = new ArrayList<ConnectionHandler>();
		securityPlayers = new ArrayList<ConnectionHandler>();
	}
	// ------------------ Queries --------------------------
	/**
	 * Returns the AMULET value for which extensions are supported.
	 * @return string containg the AMULET value for the extensions
	 */
	public String getExtensions(){
		// TODO Make thread safe
		return extensions;
	}
	
	// ------------------ Commands --------------------------
	/**
	 * startServerSocketListener creates a new ServerSocket and a new ServerSocketListener. 
	 * It also starts the ServerSocketListener Thread.
	 * @param portNumber the number on what port the listener should wait for connections
	 * @throws IOException when there is an error on the ServerSocket constructor
	 */
	public void startServerSocketListener(int portNumber) throws IOException {
		serverSocket = new ServerSocket(portNumber);	
		serverSocketListener = new ServerSocketListener(this, serverSocket);
		writeToGUI("ServerSocket has been created");

		serverSocketListener.start();
	}
	
	/**
	 * Because of the AMULET protocol the extensions which a client supports must be kept track of.
	 * The ServerController puts the connectionHandler in the  different extension sets
	 * @param extensions the ArrayList housing the extensions
	 * @param connectionHandler the player to be matched
	 */
	public synchronized void matchExtensions(ArrayList<String> extensions, ConnectionHandler player) throws Error {
		if(extensions.get(0).equals("NONE") && extensions.size() == 1){ //no extensions are supported and no more arguments should follow
			normalPlayers.add(player);
		} else if (extensions.get(0).equals("CHAT") && extensions.get(1).equals("CHALLENGE") 
				&& extensions.get(2).equals("LEADERBOARD") && extensions.size() == 3){ //all extensions are supported by the client
			chatPlayers.add(player);
			challengePlayers.add(player);			
			leaderboardPlayers.add(player);
		} else if (extensions.get(0).equals("CHAT") && extensions.size() > 3){ //either CHAT and or CHALLANGE or LEADERBOARD are supported by the client
			chatPlayers.add(player);
			if (extensions.get(1).equals("CHALLENGE")){ //only CHALLENGE or LEADERBOARD can follow
				challengePlayers.add(player);
			} else if (extensions.get(1).equals("LEADERBOARD")){
				leaderboardPlayers.add(player);
			} else { //Something other than LEADERBOARD followed which isn't allowed
				throw new Error("ERROR AMULET EXTENSION PROTOCOL NOT FOLLOWED. YOUR CONNECTION WILL BE TERMINATED");
			}
		} else if (extensions.get(0).equals("CHALLENGE") && extensions.size() > 3){ //CHALLENGE and or LEADERBOARD are supported
			challengePlayers.add(player);
			if (extensions.get(1).equals("LEADERBOARD")){ //only LEADERBOARD can follow
				leaderboardPlayers.add(player);
			} else { //Something other than LEADERBOARD followed which isn't allowed
				throw new Error();
			}
		}  else if (extensions.get(0).equals("LEADERBOARD") && extensions.size() == 1){//only LEADERBOARD can be supported
			leaderboardPlayers.add(player);			
		} else { //Extensions aren't given following the format
			throw new Error("ERROR AMULET EXTENSION PROTOCOL NOT FOLLOWED. YOUR CONNECTION WILL BE TERMINATED");
		}
	}
	
	/**
	 * Because of AMULET the security players need to be added separately.
	 * @param player the player to be added to the Security list
	 */
	public synchronized void addSecurityPlayer(ConnectionHandler player){
		securityPlayers.add(player);
	}
	
	/**
	 * Adds a ConnectionHandler to the Connections Map
	 * @param newPlayer the ConnectionHandler to be added
	 * @param nickName the Nickname of the player
	 */
	public synchronized void addConnectionHandler(String nickName, ConnectionHandler newPlayer) {
		// TODO make thread safe

		connections.put(nickName, newPlayer);
		writeToGUI("A new Player with the NickName [" + nickName + "] has joined this Server.");
		
		//The ActivePlayers list should be updated.
		updateActivePlayers();	
		
		//TODO start game properly, check if this is a Challange Playerotherwise wait for the Challange command.
		if (connections.size() > 1) {
			startGame(newPlayer);
		}
	}

	/**
	 * This methods handles the situation when there is a new player without challenge capabilities
	 * It looks for any other players which are not in a game and selects one randomly
	 * It puts them both in a GameController and assigns the GameController to their respective gameController Attributes
	 * @param player1 the first player 
	 * @param player2 the second player
	 */
	public synchronized void startGame(ConnectionHandler player1) {
		// TODO Make thread safe
		//We need to select a random key from our connections TreeMap
		Random random = new Random();
		List<String> connectionKeys = new ArrayList<String>(connections.keySet());
		connectionKeys.remove(player1.getNickName());
		String randomKey = connectionKeys.get(random.nextInt(connectionKeys.size()));
		
		ConnectionHandler randomPlayer = connections.get(randomKey);
		
		GameController newGame = new GameController(player1, randomPlayer);
		player1.setGameController(newGame);
		randomPlayer.setGameController(newGame);
		
		writeToGUI("A new game has been started between players " + player1.getNickName() + "and " + randomPlayer.getNickName());

		
		List<ConnectionHandler> playerList = new ArrayList<ConnectionHandler>();
		playerList.add(player1);
		playerList.add(randomPlayer);
		
		String gameName = player1.getNickName() + " v.s. " + randomPlayer.getNickName();	
		newGame.setName(gameName);
		addGame(gameName, playerList);
	}

	/**
	 * Creates a GameController object which starts a game with players <code>player1</code> and <code>player2</code>
	 * Used when both players are known.
	 * @param player1 the first player 
	 * @param player2 the second player
	 */
	public synchronized void startChallangeGame(ConnectionHandler player1, ConnectionHandler player2) {
		GameController newGame = new GameController(player1, player2);
		
		List<ConnectionHandler> playerList = new ArrayList<ConnectionHandler>();
		playerList.add(player1);
		playerList.add(player2);

		String gameName = player1.getNickName() + " v.s. " + player2.getNickName();		
		newGame.setName(gameName);
		addGame(gameName, playerList);

	}
	
	/**
	 * addGame removes the players of a new game from the ActivePlayers map and puts a new entry into the games map.
	 * The CurrentGames list in the ServerGUI is updated.
	 * @param newGame the GameController of the new game
	 * @param playerList the List with the ConnectionHandler references of two clients
	 */
	public synchronized void  addGame(String nameGame,List<ConnectionHandler> playerList) {
		removeConnectionHandler(playerList.get(0));
		removeConnectionHandler(playerList.get(1));
		
		games.put(nameGame, playerList);
		updateCurrentGames();
	}

	/**
	 * Removes a ConnectionHandler from the Connections Map. It doesn't matter if it has been already deleted 
	 * by a GameController because calling remove() on a Map does not throw an error.
	 * @param removePlayer the ConnectionHandler to be removed 
	 */
	public synchronized void removeConnectionHandler(ConnectionHandler removePlayer) {
		// TODO Make thread safe
		//TODO remove the ConnectionHandler from the lists
		connections.remove(removePlayer.getNickName());
		updateActivePlayers();
	}
	
	/**
	 * deleteGame removes the entry from the games map that has <code>game</code> as a key.
	 * It updates the CurrentGames list in the GUI.
	 * The GameController puts the Client(s) back in the connectionsmap, so that isn't done here.
	 * @param game the game that has ended and needs to be removed.
	 */
	public synchronized void deleteGame(String gameName) {
		games.remove(gameName);
		updateCurrentGames();
	}

	/**
	 * Prints a message to the GUI
	 * @param string the message to be printed
	 */
	public synchronized void writeToGUI(String message) {
		// TODO Make thread safe
		serverGUI.printText(message);
	}
	
	/**
	 * Because the ServerController acts as an ActionListener it receives ActionEvents for the four buttons in the ServerGui
	 * If the Start button is pressed it checks if the port number is indeed a number and if it is between 1025 and 65536.
	 * If the port number is legal it calls the startServerSocketListener method.
	 * @param arg0 the ActionEvent that has taken place
	 */
	@Override
	public void actionPerformed(ActionEvent arg0) {
		String command = arg0.getActionCommand();
		if(command.equals("Start")){
			String portNumber = serverGUI.getPortNumber();
			if(portNumber.matches("[0-9]+") && Integer.parseInt(portNumber) >= 1025 && Integer.parseInt(portNumber) <= 65536)	{
				int port = Integer.parseInt(portNumber);
				try {
					startServerSocketListener(port);
				} catch (IOException e) {
					writeToGUI("Port is already in use, try another port.");
				}
			}
			else	{
				writeToGUI("An illegal port has been given.");
			}
		}
		if(command.equals("Close")){
			if(serverSocketListener == null){
				writeToGUI("No port has been opened yet.");
			}else {
				serverSocketListener.closeListener();
				serverSocketListener = null;
			}
		}
		if(command.equals("Refresh Players")){
			updateActivePlayers();
		}
		if(command.equals("Refresh Games")){
			updateCurrentGames();
		}
	
	}
	
	/**
	 * updateActivePlayers updates the ActivePlayers list in the ServerGui. It retrieves the keySet from the connectionsmap
	 * It clears the ActivePlayers TextArea. It loops over the entries in the keySet 
	 * and appends each of them to the TextArea.
	 * It also lists the Players in the mainTextArea
	 */
	//TODO loop invariant
	public synchronized void updateActivePlayers(){
		List<String> activePlayers = new ArrayList<String>(connections.keySet());
		
		serverGUI.clearActivePlayers();

		if(connections.isEmpty()){
			writeToGUI("No Players are loggedin to this Server.");	
		}else {
			writeToGUI("Current Players are:");
		}

		for (int i = 0; i < activePlayers.size(); i++){
			writeToGUI(i +": [" + activePlayers.get(i) + "]");
			serverGUI.appendActivePlayers(activePlayers.get(i));
		}
	}

	/**
	 * updateCurrentGames updates the CurrentGames list in the ServerGui. It retrieves the valueSet from the gamesmap
	 * It clears the CurrentGames TextArea. It loops over the entries in the valueset, creates a game name in the format
	 * "i: player 1 vs. player 2" and appends each of them to the TextArea.
	 * It also lists the Players in the mainTextArea
	 */
	//TODO loop invariant
	public synchronized void updateCurrentGames(){
		List<String> gameNames = new ArrayList<String>(games.keySet());
		
		serverGUI.clearCurrentGames();
		
		if(games.isEmpty()){
			writeToGUI("There are currently no games running on this Server");
		}else {
			writeToGUI("Current Games are:");
		}

		for (int i = 0; i < gameNames.size(); i++){
			String gameName =  gameNames.get(i);
			writeToGUI(1 + ": " + gameName);
			serverGUI.appendCurrentGames(i + ": " + gameName);
		}
	}

		

}