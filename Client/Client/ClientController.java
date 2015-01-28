package Client;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;

import Model.Game;
import Model.Model;
import View.ClientGUI;

/**
 * Makes the model, gui and connectionHandler for the client and shares information
 * between them.
 * @author peter
 */
public class ClientController implements ActionListener	{

	private /*@ spec_public @*/ ClientGUI gui;
	private /*@ spec_public @*/ Model game;
	private /*@ spec_public @*/ ClientConnectionHandler connection;
	private AI aiSimple;
	private boolean[] serverExtensions;
	private String opponentName;
	private ArrayList<String[]> otherClientExtensions;
	private String[] clientExtension;

	/*@public invariant gui != null; @*/ //class invariant
	/*@public invariant game != null; @*/ //class invariant
	
	/**
	 * Makes a new GUI.
	 */
	//@ ensures gui != null && game == null && connection == null;
	public ClientController() {
		gui = new ClientGUI(this);
		game = null;
		connection = null;
		otherClientExtensions = new ArrayList<String[]>();
		clientExtension = new String[3];
		clientExtension[0] = "CHAT";
		clientExtension[1] = "CHALLENGE";
		clientExtension[2] = "LEADERBOARD";
	}

	/**
	 * Receives actions from the GUI and responds accordingly to them.
	 */
	public void actionPerformed(ActionEvent arg0) {
		String command = arg0.getActionCommand();
		if(command.matches("[0-9]+"))	{
			//number to x and y coordinate
			int column = Integer.parseInt(command);
			if(game.isLegalMove(column) && game.onTurn(1))	{
				String message = "MOVE " + column;
				connection.sendMessage(message);
			}
			else if(!game.onTurn(1))	{
				gui.printText("It is not your turn yet.");
			}
			else	{
				gui.printText("Unvalid move, please make another.");
			}
		}
		else if(command.equals("Connect"))	{
			String[] arguments = gui.getConnection();
			if(arguments[0].matches("[0-9]+") && Integer.parseInt(arguments[0]) >= 1025 && Integer.parseInt(arguments[0]) <= 65536)	{
				int port = Integer.parseInt(arguments[0]);
				try {
					InetAddress ip = InetAddress.getByName(arguments[1]);
					startConnection(port, ip);
				} catch (UnknownHostException e) {
					gui.printText("The ip adress is of an illegal format.");
				}
			}
			else	{
				gui.printText("An illegal port has been given.");
			}
		}
		else if(command.equals("Challenge"))	{
			if(connection != null)	{
				//TODO
			}
			else	{
				gui.printText("First a connection must be made.");
			}
		}
		else if(command.equals("chatText"))	{
			if(connection != null)	{
				//TODO
			}
			else	{
				gui.printText("First a connection must be made.");
			}
		}
		else if(command.equals("Start Game"))	{
			String name = gui.getStartGame();
			if(name != null && !name.equals(""))	{
				String message = "JOINREQ " + name;
				connection.sendMessage(message);
				connection.setName(name);
			}
			else	{
				gui.printText("Give a player name.");
			}
		}
		else if(command.equals("Hint"))	{
			if(connection != null)	{
				if(game != null)	{
					hint();
				}
				else	{
					gui.printText("First a game must be started.");
				}
			}
			else	{
				gui.printText("First a connection must be made.");
			}
		}
		else if(command.equals("LeaderBoard"))	{
			if(connection != null)	{
					String message = "LEADERBOARDREQ";
					connection.sendMessage(message);
			}
			else	{
				gui.printText("First a connection must be made.");
			}
		}
		else if(command.equals("End Game"))	{
			String message = "ENDGAME";
			connection.closeConnection(message);
			closeAGame();
		}
	}
	
	private void closeAGame()	{
		connection = null;
		game = null;
		aiSimple = null;
		serverExtensions = null;
		opponentName = null;
		otherClientExtensions = null;
		gui.setNewGame();
	}
	
	/**
	 * Starts a connection with the given port and ip address
	 * @param port
	 * @param ip
	 */
	private void startConnection(int port, InetAddress ip)	{
		try {
			Socket socket = new Socket(ip, port);
			gui.printText("A connection has been made to the server.");
			//TODO Aanpassen
			gui.setConnectionScreen();
			connection = new ClientConnectionHandler(socket, this);
			connection.start();
		} catch (IOException e)	{
			gui.printText("A connection could not be made with the given port and ip address. (Server might be offline)");
		}
	}
	
	/**
	 * Registers the extensions that the server supports in the following way.
	 * The extensions parameter is checked in the following sequence for containing
	 * NONE, CHAT, CHALLENGE or LEADERBOARD. The results of the check are saved.
	 * @param extensions contains the extensions of the server
	 */
	public void addServerExtensions(List<String> extensions)	{
		serverExtensions = new boolean[4];
		serverExtensions[0] = extensions.contains("NONE");
		serverExtensions[1] = extensions.contains("CHAT");
		serverExtensions[2] = extensions.contains("CHALLENGE");
		serverExtensions[3] = extensions.contains("LEADERBOARD");
		String message = "EXTENSIONS";
		for (int i = 0; i < clientExtension.length; i++) {
			message = message + " " + clientExtension[i];
		}
		connection.sendMessage(message);
	}
	
	/**
	 * Start a game against the given player
	 * @param name is the name of the player against who the game is played
	 */
	public void startGame(String name)	{
		opponentName = name;
		game = new Game();
		//TODO verander dat dit wordt ingesteld door de gui
		aiSimple = new SmartAI();
		game.addObserver(gui);
		game.addObserver(aiSimple);
		//TODO vervangen door slimme game voor hint
		gui.printText("A game has been started against " + name);
		//TODO aanpassen		
		gui.gameStartScreen();
	}
	
	/**
	 * This method is called when the player is on turn and 
	 * is asked to do a move.
	 */
	public void onTurn()	{
		//TODO remove
		game.setOnTurn();
		if(gui.isHumanPlayer())	{
			gui.printText("It's your turn.");
		}
		else	{
			//TODO aanpassen 4
			int column = aiSimple.getMove(4);
			String message = "MOVE " + column;
			connection.sendMessage(message);
		}
	}
	
	/**
	 * Gives the name of the opponent in the current game
	 * @return
	 */
	public String getOpponent()	{
		return opponentName;
	}
	
	/**
	 * Do a move from the server
	 * @param arguments
	 */
	public void serverMove(String[] arguments)	{
		int player = isPlayer(arguments[0]);
		int column = Integer.parseInt(arguments[1]);
		game.doMove(column, player);
		gui.printText("Player " + arguments[0] + " has placed a stone in column " + column);
	}
	
	/**
	 * The end of a game has been reached with a move given in arguments
	 * by the winner in arguments.
	 * @param arguments
	 */
	public void gameEnd(String[] arguments)	{
		String winner = arguments[0];
		int player = isPlayer(winner);
		int column = Integer.parseInt(arguments[1]);
		game.doMove(column, player);
		boolean newGame = gui.gameWinner(winner);
		if(newGame)	{
			gui.setNewGame();
			String message = "JOINREQ " + connection.getName();
			connection.sendMessage(message);
		}
		else	{
			gui.setNewGame();
		}
	}
	
	/**
	 * The errormessage passed on from the server to inform the 
	 * client that a wrong move has been made by this client.
	 * @param message
	 */
	public void error(String message)	{
		gui.printText("Server gave the following message: " + message);
	}
	
	/**
	 * Gets a hint from the AI and gives this to the gui.
	 */
	public void hint()	{
		gui.hint(aiSimple.getMove(3));
	}
	
	/**
	 * Gets a leaderboard as argument and passes this on to the gui.
	 * @param leaderboard
	 */
	public void leaderboard(String[] leaderboard)	{
		gui.printLeaderboard(leaderboard);
	}
	
	/**
	 * Prints a personal message to the client.
	 * @param message
	 */
	public void message(String message)	{
		gui.guiMessage(message);
	}
	
	/**
	 * Prints a broadcast message to the client.
	 * @param broadcast
	 */
	public void broadcast(String broadcast)	{
		gui.guiMessage(broadcast);
	}
	
	/**
	 * Updates the list of extensions from the other clients
	 * @param updates
	 * @require updates.size() > 0
	 */
	public void update(String[] updates)	{
		//TODO nog verder aanpassen en vooral die else if statements vervangen
		String current = updates[0];
		for (int i = 0; i < updates.length; i++) {
			boolean found = false;
			int positionFound = 0;
			for (int j = 0; j < otherClientExtensions.size() && !found; j++) {
				String name = otherClientExtensions.get(j)[0];
				if(current.equals(name))	{
					positionFound = j;
					found = true;
				}
			}
			if(found)	{
				for (int j = 1; j < 6; j++) {
					otherClientExtensions.get(positionFound)[j] = null;
				}
				String keyword = updates[i++];
				if(updates.equals("NONE"))	{
					otherClientExtensions.get(positionFound)[1] = "YES";
				}
				else	{
					if(keyword.equals("CHAT"))	{
						otherClientExtensions.get(positionFound)[2] = "YES";
						keyword = updates[i++];
					}
					if(keyword.equals("CHALLENGE"))	{
						otherClientExtensions.get(positionFound)[3] = "YES";
						keyword = updates[i++];
					}
					if(keyword.equals("LEADERBOARD"))	{
						otherClientExtensions.get(positionFound)[4] = "YES";
						keyword = updates[i++];
					}
					if(keyword.equals("SECURITY"))	{
						otherClientExtensions.get(positionFound)[5] = "YES";
					}
					i--;
				}						
			}
			else	{
				otherClientExtensions.add(otherClientExtensions.size(), new String[6]);
				String[] player = otherClientExtensions.get(otherClientExtensions.size() - 1);
				player[0] = current;
				for (int j = 1; j < 6; j++) {
					player[j] = null;
				}
				String keyword = updates[i++];
				if(updates.equals("NONE"))	{
					player[1] = "YES";
				}
				else	{
					if(keyword.equals("CHAT"))	{
						player[2] = "YES";
						keyword = updates[i++];
					}
					if(keyword.equals("CHALLENGE"))	{
						player[3] = "YES";
						keyword = updates[i++];
					}
					if(keyword.equals("LEADERBOARD"))	{
						player[4] = "YES";
						keyword = updates[i++];
					}
					if(keyword.equals("SECURITY"))	{
						player[5] = "YES";
					}
					i--;
				}	
			}
		}
	}
	
	/**
	 * Receives a challenge from the player and responds by accepting or declining.
	 * @param player
	 */
	public void challenged(String player)	{
		boolean choice = gui.challenged(player);
		if(choice)	{
			connection.sendMessage("CHALLANGERESP Y");
		}
		else	{
			connection.sendMessage("CHALLANGERESP N");
		}
	}
	
	/**
	 * Authenticate with the server by sending a password.
	 */
	public void authenticate()	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Tells if the client is the player that is given as an argument.
	 * @return 1 if the given player is the name of the clinent. And 2 if
	 * 		   the given player is the opponent.
	 */
	private int isPlayer(String player)	{
		int result;
		if(player.equals(connection.getName()))	{
			result = 1;
		}
		else	{
			result = 2;
		}
		return result;
	}
	
	/**
	 * Tells the GUI that the connection has been broken and a new connection can be made.
	 * @param message
	 */
	public void connectionClosed(String message)	{
		gui.guiMessage("The connection with the server has been broken with the following message: " + message);
		gui.connectionBroken();
	}
	
	/**
	 * Removes a given player from all lists and his extensions
	 * @param playerName is the name of the player that disconnected
	 */
	public void otherPlayerDisconnected(String playerName)	{
		for (int i = 0; i < otherClientExtensions.size(); i++) {
			if(otherClientExtensions.get(i)[0].equals(playerName))	{
				otherClientExtensions.remove(i);
			}
		}
	}
}