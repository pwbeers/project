package Server;

import java.util.ArrayList;
import java.util.List;

import Model.Game;
import Model.Model;

public class GameController {

	// ------------------ Instance variables ----------------
	private Model game; //the game that this controller uses
	private ConnectionHandler player1;
	private ConnectionHandler player2;

	// ------------------ Constructor ------------------------
	/**
	 * Creates a new Game with two players.
	 * Fills the Instance Variables
	 * @param player1
	 * @param player2
	 */
	public GameController(ConnectionHandler newPlayer1, ConnectionHandler newPlayer2) {
		game = new Game();
		player1 = newPlayer1;
		player2 = newPlayer2;
	}
	
	// ------------------ Queries --------------------------
	// ------------------ Commands --------------------------
	/**
	 * Creates a new Game object
	 * Send AMULET TURN command to player1
	 */
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