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
	private TreeMap<GameController, List<ConnectionHandler>> games; //Keeps track of alle current games and their respective ConnectionHandlers
	
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
		extensions = "NONE"; //We hardcode the extensions for now, they can be enabled and disabled in the GUI
		connections = new TreeMap<String, ConnectionHandler>();
		games = new TreeMap<GameController, List<ConnectionHandler>>();
		//the serverSocketListener gets made after a button is pressed in the GUI so it isn't initialized here
		
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
	public void startGame(ConnectionHandler player1) {
		// TODO Make thread safe
		//We need to select a random key from our connections TreeMap
		Random random = new Random();
		List<String> connectionKeys = new ArrayList<String>(connections.keySet());
		String randomKey = connectionKeys.get(random.nextInt(connectionKeys.size()));
		
		ConnectionHandler randomPlayer = connections.get(randomKey);

		GameController newGame = new GameController(player1, randomPlayer);
		
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
	public void startChallangeGame(ConnectionHandler player1, ConnectionHandler player2) {
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
	public void addConnectionHandler(String nickName, ConnectionHandler newPlayer) {
		// TODO make thread safe
		//TODO update GUI
		connections.put(nickName, newPlayer);		
	}

	/**
	 * Removes a ConnectionHandler from the Connections Map
	 * @param removePlayer the ConnectionHandler to be removed 
	 */
	public void removeConnectionHandler(ConnectionHandler removePlayer) {
		// TODO Make thread safe
		connections.remove(removePlayer.getNickName());
	}
	
	public void addGame(GameController newGame,List<ConnectionHandler> playerList) {
		games.put(newGame, playerList);
		//TODO Update GUI
	}
	
	public void deleteGame(GameController game) {
		games.remove(game);
		//TODO Update GUI
	}

	
	/**
	 * Prints a message to the GUI
	 * @param string
	 */
	public void writeToGUI(String string) {
		// TODO Make thread safe
		serverGUI.printTekst(string);
	}
	
	/**
	 * Because of the AMULET protocol the extensions which a client supports must be kept track of.
	 * The ServerController puts the connectionHandler in the  different extention sets
	 * @param extensions the ArrayList housing the extensions
	 * @param connectionHandler
	 */
	public void matchExtensions(ArrayList<String> extensions, ConnectionHandler player) throws Error {
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
				throw new Error();
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
			throw new Error();
		}
		
	}
	@Override
	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
	}

}