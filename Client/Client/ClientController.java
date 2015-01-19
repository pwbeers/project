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
		view = new ClientGUI();
		view.addController(this);
		game = new Game();
		game.addObserver(view);
	}

	/**
	 * Sends a command to the server using the ClientConnectionHandler
	 */
	public void commandProducer() {
		throw new UnsupportedOperationException();
	}

	@Override
	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
	}

}