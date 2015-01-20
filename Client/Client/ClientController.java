package Client;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
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
	private final int PLAYER = 0;

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
				System.out.println("yes");
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("LeaderBoard"))	{
			if(connection != null)	{
				System.out.println("yes");
			}
			else	{
				gui.printTekst("First a connection must be made.");
			}
		}
		else if(command.equals("End Game"))	{
			System.out.println("yes");
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
	 * Registers the extensions that the server supports
	 * @param extensions
	 */
	public void addServerExtensions(String[] extensions)	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Start a game against the given player
	 * @param name is the name of the player against who the game is played
	 */
	public void startGame(String name)	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * This method is called when the player is on turn and 
	 * is asked to do a move
	 */
	public void onTurn()	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Gives the opponent in the current game
	 * @return
	 */
	public String getOpponent()	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Do a move from the server
	 * @param arguments
	 */
	public void serverMove(String[] arguments)	{
		
	}
	
	/**
	 * The end of a game has been reached with a move given in arguments
	 * by the winner in arguments.
	 * @param arguments
	 */
	public void gameEnd(String[] arguments)	{
		
	}
	
	/**
	 * The errormessage passed on from the server to inform the 
	 * client that a wrong move has been made by this client.
	 * @param message
	 */
	public void error(String message)	{
		
	}
}