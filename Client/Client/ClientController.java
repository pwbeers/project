package Client;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
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
	private AI ai;
	private final int PLAYER = 0;
	private boolean[] serverExtensions;
	private String opponentName;

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
	}

	/**
	 * Sends a command to the server using the ClientConnectionHandler
	 */
	public void commandProducer() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Receives actions from the GUI and responds accordingly to them.
	 */
	public void actionPerformed(ActionEvent arg0) {
		String command = arg0.getActionCommand();
		if(command.matches("[0-9]+"))	{
			//Controlleer of een game gestart is, geeft melding start game
			if(game != null)	{
				//number to x and y coordinate
				int column = Integer.parseInt(command);
				if(game.doMove(column, PLAYER) != 0)	{
					//TODO verder implementeren
					//Controller of het een geldige zet is
					//Zo ja stuur de zet naar de server
				}
				else	{
					gui.printTekst("Unvalid move, please make another.");
				}
			}
			else	{
				gui.printTekst("You must first start make a connection and start a game.");
			}
			System.out.println(command);
		}
		else if(command.equals("Connect"))	{
			//TODO voeg checks en fouten afvangen toe
			String[] arguments = gui.getConnection();
			if(arguments[0].matches("[0-9]+"))	{
				int port = Integer.parseInt(arguments[0]);
				try {
					InetAddress ip = InetAddress.getByName(arguments[1]);
					startConnection(port, ip);
				} catch (UnknownHostException e) {
					gui.printTekst("The ip adress is of an illegal format.");
				}
			}
			else	{
				gui.printTekst("An illegal port has been given.");
			}
		}
		else if(command.equals("Challenge"))	{
			if(connection != null)	{
				System.out.println("yes");
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("chatText"))	{
			if(connection != null)	{
				System.out.println("yes");
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("Start Game"))	{
			if(connection != null)	{
				String name = gui.getStartGame();
				if(name != null && !name.equals(""))	{
					String message = "JOINREQ " + name;
					connection.sendMessage(message);
					connection.setName(name);
				}
				else	{
					gui.printTekst("Give a player name.");
				}
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("Hint"))	{
			if(connection != null)	{
				if(game != null)	{
					hint();
				}
				else	{
					gui.printTekst("First a game must be started.");
				}
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("LeaderBoard"))	{
			if(connection != null)	{
					String message = "LEADERBOARDREQ";
					connection.sendMessage(message);
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("End Game"))	{
			//TODO tells the server the game is ended
			//TODO deletes the current game and makes the client ready to be restarted
		}
	}
	
	/**
	 * Starts a connection with the given port and ip address
	 * @param port
	 * @param ip
	 */
	private void startConnection(int port, InetAddress ip)	{
		try {
			Socket socket = new Socket(ip, port);
			gui.printTekst("A connection has been made to the server.");
			connection = new ClientConnectionHandler(socket, this);
			connection.start();
		} catch (IOException e)	{
			gui.printTekst("A connection could not be made with the given port and ip address. (Server might be offline)");
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
		//TODO testen of dit niet allemaal String dus true oplevert.
	}
	
	/**
	 * Start a game against the given player
	 * @param name is the name of the player against who the game is played
	 */
	public void startGame(String name)	{
		opponentName = name;
		game = new Game();
		game.addObserver(gui);
		gui.printTekst("A game has been started against " + name);
	}
	
	/**
	 * This method is called when the player is on turn and 
	 * is asked to do a move.
	 */
	public void onTurn()	{
		gui.printTekst("It's your turn.");
		//TODO iets om duidelijk de beurt aan te geven toevoegen
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
		gui.printTekst("Player " + arguments[0] + " has placed a stone in column " + column);
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
		//TODO GUI is notified of winner and there is an option to start a new game
	}
	
	/**
	 * The errormessage passed on from the server to inform the 
	 * client that a wrong move has been made by this client.
	 * @param message
	 */
	public void error(String message)	{
		gui.printTekst("Server gave the following message: " + message);
	}
	
	/**
	 * Gets a hint from the AI and gives this to the gui.
	 */
	public void hint()	{
		gui.hint(ai.getMove());
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
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Prints a broadcast message to the client.
	 * @param broadcast
	 */
	public void broadcast(String broadcast)	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Updates the list of extensions from the other clients
	 * @param updates
	 */
	public void update(String[] updates)	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Receives a challenge from the player and responds by accepting or declining.
	 * @param player
	 */
	public void challenged(String player)	{
		//TODO
		throw new UnsupportedOperationException();
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
	 * @return
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
		//TODO
		throw new UnsupportedOperationException();
	}
}