package Server;

/**
 * This Class initializes all other Classes and hence facilitates the creation of games,
 * houses the logic for the GUI, creates the ServerSocketListener for the serversocket 
 * and will implement the functionalities of any of the facultative extensions.
 * @author Stephan
 */

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.ServerSocket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import View.ServerGui;
import View.View;

public class ServerController implements ActionListener{
	
	// ------------------ Instance variables ----------------
	private View serverGUI;	
	private ServerSocket serverSocket;
	private ServerSocketListener serverSocketListener;
	
	private TreeMap<String, ConnectionHandler> connections; //Keeps track of all current connections and their nicknames
	private HashMap<GameController, List<ConnectionHandler>> games; //Keeps track of alle current games and their respective ConnectionHandlers
	
	private String extensions; //The AMULET value for which extensions are supported
	private List<ConnectionHandler> normalPlayers;
	private List<ConnectionHandler> challengePlayers;
	private List<ConnectionHandler> chatPlayers;
	private List<ConnectionHandler> leaderboardPlayers;
	private List<ConnectionHandler> securityPlayers;
	
	
	// ------------------ Constructor ------------------------
	/**
	 * Creates a ServerSocketListener which creates a ServerGui class. 
	 * Initializes all Instance Variables.
	 */
	public ServerController() {
		serverGUI = new ServerGui(this);
		writeToGUI("ServerGUI has been created");
		
		extensions = "NONE"; //We hardcode the extensions for now, they can be enabled and disabled in the GUI
		connections = new TreeMap<String, ConnectionHandler>();
		games = new HashMap<GameController, List<ConnectionHandler>>();
		
		//the serverSocketListener gets made after a button is pressed in the GUI so it isn't initialized here
		try {
			serverSocket = new ServerSocket(2200);
			writeToGUI("ServerSocket has been created");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		serverSocketListener = new ServerSocketListener(this, serverSocket);
		serverSocketListener.start();
		
		normalPlayers = new ArrayList<ConnectionHandler>();
		challengePlayers = new ArrayList<ConnectionHandler>();
		chatPlayers = new ArrayList<ConnectionHandler>();
		leaderboardPlayers = new ArrayList<ConnectionHandler>();
		securityPlayers = new ArrayList<ConnectionHandler>();
	}
	// ------------------ Queries --------------------------
	/**
	 * Returns the AMULET value for which extensions are supported.
	 * @return
	 */
	public String getExtensions(){
		// TODO Make thread safe
		return extensions;
	}
	
	// ------------------ Commands --------------------------
	/**
	 * Creates a ServerSocketListeren object on port <code>portNumber</code>
	 * @param portNumber the number on what port the listener should wait for connections
	 * @throws IOException 
	 */
	public void startServerSocketListener(int portNumber) throws IOException {
		serverSocket = new ServerSocket(portNumber);
		serverSocketListener = new ServerSocketListener(this, serverSocket);
	}

	/**
	 * This methods handles the situation when there is a new player without challange capabilities
	 * It looks for any other players which are not in a game and selects one randomly
	 * It puts them both in a GameController
	 * @param player1 the first player 
	 * @param player2 the second player
	 */
	public synchronized void startGame(ConnectionHandler player1) {
		// TODO Make thread safe
		//TODO make sure player 1 is not selected from the list
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
		
		addGame(newGame, playerList);

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
		
		addGame(newGame, playerList);
	}
	
	/**
	 * Adds a ConnectionHandler to the Connections Map
	 * @param newPlayer the ConnectionHandler to be added
	 * @param nickName the Nickname of the player
	 */
	public synchronized void addConnectionHandler(String nickName, ConnectionHandler newPlayer) {
		// TODO make thread safe
		//TODO update GUI
		connections.put(nickName, newPlayer);
		updateActivePlayers();
		
		//TODO start game properly
		if (connections.size() > 1) {
			startGame(newPlayer);
		}
	}

	/**
	 * Removes a ConnectionHandler from the Connections Map
	 * @param removePlayer the ConnectionHandler to be removed 
	 */
	public synchronized void removeConnectionHandler(ConnectionHandler removePlayer) {
		// TODO Make thread safe
		connections.remove(removePlayer.getNickName());
		updateActivePlayers();
	}
	
	public synchronized void  addGame(GameController newGame,List<ConnectionHandler> playerList) {
		games.put(newGame, playerList);
		updateCurrentGames();
	}
	
	public synchronized void deleteGame(GameController game) {
		games.remove(game);
		updateCurrentGames();
	}

	
	/**
	 * Prints a message to the GUI
	 * @param string
	 */
	public synchronized void writeToGUI(String message) {
		// TODO Make thread safe
		serverGUI.printText(message + "\n");
	}
	
	public synchronized void updateActivePlayers(){
		List<String> activePlayers = new ArrayList<String>(connections.keySet());
		((ServerGui) serverGUI).clearActivePlayers();
		for (int i = 0; i < activePlayers.size(); i++){
			((ServerGui) serverGUI).appendActivePlayers(activePlayers.get(i));
		}
	}

	public synchronized void updateCurrentGames(){
		List<List <ConnectionHandler>> playersInGames = new ArrayList<List <ConnectionHandler>>(games.values());
		((ServerGui) serverGUI).clearCurrentGames();
		for (int i = 0; i < playersInGames.size(); i++){
			List<ConnectionHandler> game = new ArrayList<ConnectionHandler>(playersInGames.get(i));
			String gameName = game.get(0).getNickName() + " v.s. " + game.get(1).getNickName();
			((ServerGui) serverGUI).appendCurrentGames(i + ": " + gameName);
		}
	}
	
	/**
	 * Because of the AMULET protocol the extensions which a client supports must be kept track of.
	 * The ServerController puts the connectionHandler in the  different extention sets
	 * @param extensions the ArrayList housing the extensions
	 * @param connectionHandler
	 */
	public synchronized void matchExtensions(ArrayList<String> extensions, ConnectionHandler player) throws Error {
		// TODO Make thread safe
		// TODO Auto-generated method stub
		// sort the connection handler into the differen extention sets
		//write extensions reader
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
	
	@Override
	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
	}

}