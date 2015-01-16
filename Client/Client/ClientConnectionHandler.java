package Client;

import java.net.Socket;

/**
 * Starts and keeps a connection running with a server and passes messages 
 * on over this connection.
 * @author peter
 */
public class ClientConnectionHandler {

	private /*@ spec_public @*/ ClientController controller;
	private /*@ spec_public @*/ Socket socket;
	private /*@ spec_public @*/ String name;

	/*@public invariant controller != null; @*/ //class invariant
	/*@public invariant socket != null; @*/ //class invariant
	
	/**
	 * Makes a new ClientConnectionHandler on the given socket. Also saves
	 * the ClientController that is given. 
	 * @param socket is a socket on which the connection is kept
	 * @param controller is used to pass on messages from the server to the client
	 */
	//@ requires socket != null && controller != null;
	//@ ensures this.controller == controller && this.socket == socket;
	public ClientConnectionHandler(Socket socket, ClientController controller) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Sets the name of this class with the given name
	 * @param name is the name of the client
	 */
	//@ requires name != null && name.length() > 0;
	//@ ensures this.name == name;
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * Gives the name of the client.
	 * @return the name of the client
	 */
	//@ ensures \result == name;
	public String getName() {
		return this.name;
	}

	/**
	 * Reads a received command and passes this on to the ClientController.
	 * @param line is the message received from a server
	 */
	//@ requires line != null;
	public void commandReader(String line) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Sends a message from the client to a server with the given message as the message.
	 * @param message is line of text to be send to the server
	 */
	//@ requires message != null;
	public void sendMessage(String message) {
		throw new UnsupportedOperationException();
	}

}