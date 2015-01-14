package Client;

import java.net.Socket;

public class ClientConnectionHandler {

	private ClientController controller;
	private Socket socket;
	private String name;

	/**
	 * 
	 * @param socket
	 * @param controller
	 */
	public ClientConnectionHandler(Socket socket, ClientController controller) {
		// TODO - implement ClientConnectionHandler.ClientConnectionHandler
		throw new UnsupportedOperationException();
	}

	/**
	 * 
	 * @param name
	 */
	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return this.name;
	}

	/**
	 * 
	 * @param line
	 */
	public void commandReader(String line) {
		// TODO - implement ClientConnectionHandler.commandReader
		throw new UnsupportedOperationException();
	}

	/**
	 * 
	 * @param message
	 */
	public void sendMessage(String message) {
		// TODO - implement ClientConnectionHandler.sendMessage
		throw new UnsupportedOperationException();
	}

}