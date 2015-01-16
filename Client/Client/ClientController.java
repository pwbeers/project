package Client;

import Model.Model;
import View.GUI;

/**
 * Makes the model, gui and connectionHandler for the client and shares information
 * between them.
 * @author peter
 */
public class ClientController {

	private /*@ spec_public @*/ GUI view;
	private /*@ spec_public @*/ Model game;
	private /*@ spec_public @*/ ClientConnectionHandler connection;

	/*@public invariant view != null; @*/ //class invariant
	/*@public invariant game != null; @*/ //class invariant
	/*@public invariant connection != null; @*/ //class invariant
	
	/**
	 * Makes a new Model, GUI and ClienConnectionHandler.
	 */
	//@ ensures view != null && game != null && connection != null;
	public ClientController() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Sends a command to the server using the ClientConnectionHandler
	 */
	public void commandProducer() {
		throw new UnsupportedOperationException();
	}

}