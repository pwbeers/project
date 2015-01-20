package Client;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import Model.Model;
import View.ClientGUI;
import View.GUI;

/**
 * Makes the model, gui and connectionHandler for the client and shares information
 * between them.
 * @author peter
 */
public class ClientController implements ActionListener	{

	private /*@ spec_public @*/ GUI view;
	private /*@ spec_public @*/ Model game;
	private /*@ spec_public @*/ ClientConnectionHandler connection;
	private final int PLAYER = 0;

	/*@public invariant view != null; @*/ //class invariant
	/*@public invariant game != null; @*/ //class invariant
	
	/**
	 * Makes a new GUI.
	 */
	//@ ensures view != null && game == null && connection == null;
	public ClientController() {
		view = new ClientGUI(this);
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
					view.printTekst("Unvalid move, please make another.");
				}
			}
			else	{
				view.printTekst("You must first start a game.");
			}
			System.out.println(command);
		}
		else if(command.equals("Connect"))	{
			//TODO voeg checks en fouten afvangen toe
			String[] arguments = ((ClientGUI) view).getConnection();
			if(arguments[0].matches("[0-9]+"))	{
				int port = Integer.parseInt(arguments[0]);
				try {
					InetAddress ip = InetAddress.getByName(arguments[1]);
					startConnection(port, ip);
				} catch (UnknownHostException e) {
					view.printTekst("The ip adress is of an illegal format.");
				}
			}
			else	{
				view.printTekst("An illegal port has been given.");
			}
		}
		else if(command.equals("Challenge"))	{
			System.out.println("yes");
		}
		else if(command.equals("chatText"))	{
			System.out.println("yes");
		}
		else if(command.equals("StartGame"))	{
			System.out.println("yes");
		}
		else if(command.equals("Hint"))	{
			System.out.println("yes");
		}
		else if(command.equals("LeaderBoard"))	{
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
			view.printTekst("A connection has been made to the server.");
			connection = new ClientConnectionHandler(socket, this);
			connection.start();
		} catch (IOException e)	{
			view.printTekst("A connection could not be made with the given port and ip address. (Server might be offline)");
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
}