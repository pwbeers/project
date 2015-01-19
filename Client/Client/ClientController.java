package Client;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

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
			System.out.println("yes");
		}
		else if(command.equals("Connect"))	{
			System.out.println("yes");
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
}