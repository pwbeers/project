package Server;

import java.net.Socket;

/**
 * Extends Thread, run aanpassen
 */
public class ConnectionHandler {

	private ServerController controller;
	private Socket socket;
	private String name;
	private GameController gameController;

	/**
	 * 
	 * @param controller
	 * @param socket
	 */
	public ConnectionHandler(ServerController controller, Socket socket) {
		// TODO - implement ConnectionHandler.ConnectionHandler
		throw new UnsupportedOperationException();
	}

	public void setGameController() {
		// TODO - implement ConnectionHandler.setGameController
		throw new UnsupportedOperationException();
	}

	public void setName() {
		// TODO - implement ConnectionHandler.setName
		throw new UnsupportedOperationException();
	}

	/**
	 * 
	 * @param line
	 */
	public void commandReader(String line) {
		// TODO - implement ConnectionHandler.commandReader
		throw new UnsupportedOperationException();
	}

	public ServerController getServerController() {
		// TODO - implement ConnectionHandler.getServerController
		throw new UnsupportedOperationException();
	}

}