package Model;

import java.util.List;
import java.util.Observable;

/**
 * This class keeps track of a game from start till finish.
 * @author peter
 */
public class Game extends Observable	{

	private /*@ spec_public @*/ Board board;
	private /*@ spec_public @*/ List<Integer> players;

	/*@public invariant board != null; @*/ //class invariant
	/*@public invariant players.size() == 2 && players.get(0) == 1 && players.get(1) == 2; @*/ //class invariant
	
	/**
	 * Makes a new Board class and saves it
	 */
	//@ ensures board != null;
	public Game() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the given player is onTurn at the moment.
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires player == 1 || player == 2;
	public boolean onTurn(int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the given player has won the game.
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires player == 1 || player == 2;
	public boolean isWinner(int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if placing a stone in the given column is a legal move.
	 * @param column >= 0 && column <= 6
	 */
	//@ requires column >= 0 && column <= 6;
	public boolean isLegalMove(int column) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Ends the game and tells who the winner is.
	 */
	//@ requires isWinner(players.get(0)) || isWinner(players.get(1));
	public void endGame() {
		throw new UnsupportedOperationException();
	}

}