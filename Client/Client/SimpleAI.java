package Client;

import java.util.Observable;
import java.util.Observer;

import Model.Board;

public class SimpleAI implements AI,Observer	{

	private Board board;
	
	/**
	 * Starts an implementation of SimpleAI
	 */
	public SimpleAI() {
		board = new Board();
	}
	
	/**
	 * Asks the AI for a possible move to play in the current
	 * game that is on the board and legal.
	 * @return a legal move, \result >= 0 && \result <= 6
	 */
	public int getMove(int dephth) {
		int result = 6;
		for (int i = 0; i < result; i++) {
			board.legalMove(i);
		}
		return result;
	}

	/**
	 * Updates the board of the AI.
	 */
	public void update(Observable o, Object arg) {
		this.board = (Board) arg;
	}
}
