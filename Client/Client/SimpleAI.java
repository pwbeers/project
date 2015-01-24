package Client;

import java.util.Observable;
import java.util.Observer;

import Model.Board;

public class SimpleAI implements AI,Observer	{

	private Board board;
	
	/**
	 * Starts an implementation of SimpleAI with a given model and controller.
	 * @param modelCopy is a copy of the board from the model
	 * @param controller is the clientcontroller
	 */
	public SimpleAI() {
		// TODO Auto-generated method stub
	}

	/**
	 * Tells the AI a move has been done and tells the AI to put this
	 * in its own board version.
	 */
	//@ ensures move != null && move.length() > 0;
	public void doMove(String move) {
		// TODO Auto-generated method stub
		
	}

	/**
	 * Asks the AI for a possible move to play in the current
	 * game that is on the board and legal.
	 * @return a legal move, \result >= 0 && \result <= 6
	 */
	//@ ensures \result >= 0 && \result <= 6;
	public int getMove() {
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
