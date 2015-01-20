package Client;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

import Model.Game;
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

	/*@public invariant view != null; @*/ //class invariant
	/*@public invariant game != null; @*/ //class invariant
	
	/**
	 * Makes a new Model and GUI. Also adds the GUI observer to the Model.
	 */
	//@ ensures view != null && game != null;
	public ClientController() {
		view = new ClientGUI(this);
		game = new Game();
		game.addObserver(view);
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
			//Controller of het een geldige zet is
			//Zo nee print een message op de gui
			//Zo ja stuur de zet naar de server
			System.out.println(command);
		}
		else if(command.equals("Connect"))	{
			//TODO voeg checks en fouten afvangen toe
			String[] arguments = ((ClientGUI) view).getConnection();
			/*int port = Integer.parseInt(arguments[0]);
			InetAddress ip;
			try {
				ip = InetAddress.getByName(arguments[1]);
				startConnection(new Socket(ip, port));
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}*/
			System.out.println(arguments[0]);
			if(arguments[0].matches("[0-9]+"))	{
				int port = Integer.parseInt(arguments[0]);
				try {
					InetAddress ip = InetAddress.getByName(arguments[1]);
					System.out.println(arguments[1]);
					Socket socket = new Socket(InetAddress.getByName("8.0.8.0"), 8080);
					startConnection(socket);
					view.printTekst("");
				} catch (UnknownHostException e) {
					view.printTekst("The ip adress is of an illegal format.");
				} catch (IOException e)	{
					view.printTekst("A connection could not be made with the given port and ip address.");
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
	 * Starts a connection with the given port and ip adress
	 * @param port
	 * @param ip
	 */
	private void startConnection(Socket socket)	{
		connection = new ClientConnectionHandler(socket, this);
		System.out.println("yes");
	}
}