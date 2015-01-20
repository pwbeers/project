package Server;

import java.util.ArrayList;
import java.util.List;

import Model.Model;

public class GameController {

	// ------------------ Instance variables ----------------
	private List<ConnectionHandler> connections;
	private Model game;

	// ------------------ Constructor ------------------------
	/**
	 * 
	 * @param connectionX
	 * @param connectionY
	 */
	public GameController(ConnectionHandler connectionX, ConnectionHandler connectionY) {
		// TODO - implement GameController.GameController
		throw new UnsupportedOperationException();
	}
	
	// ------------------ Queries --------------------------
	// ------------------ Commands --------------------------
	public void startGame() {
		// TODO - implement GameController.startGame
		throw new UnsupportedOperationException();
	}

	public void hasWinner() {
		// TODO - implement GameController.hasWinner
		throw new UnsupportedOperationException();
	}

	public void doMove() {
		// TODO - implement GameController.doMove
		throw new UnsupportedOperationException();
	}

	public void illegalMove() {
		// TODO - implement GameController.illegalMove
		throw new UnsupportedOperationException();
	}

	public void draw() {
		// TODO - implement GameController.draw
		throw new UnsupportedOperationException();
	}

	/**
	 * 
	 * @param line
	 */
	public void gameCommandReader(String line) {
		// TODO - implement GameController.gameCommandReader
		throw new UnsupportedOperationException();
	}

	/**
	 * Handles the AMULET protocol for doing a move
	 * @param connectionHandler
	 * @param arguments
	 */
	public void newMove(ConnectionHandler connectionHandler, ArrayList<String> arguments) {
		// TODO Auto-generated method stub
		//make a new move and feedback what the result is, wrong move = error normal move = nothing endgame = endgame
		throw new UnsupportedOperationException();
	}

}