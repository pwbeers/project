package Client;

import java.util.Observer;

/**
 * Is an interface that is there for multiple leves of AI to be started on.
 * @author peter
 */
public interface AI extends Observer	{

	/**
	 * Tells the AI a move has been done and tells the AI to put this
	 * in its own board version.
	 */
	//@ ensures move != null && move.length() > 0;
	public void doMove(String move);

	/**
	 * Asks the AI for a possible move to play in the current
	 * game that is on the board and legal.
	 * @return a legal move, \result >= 0 && \result <= 6
	 */
	//@ ensures \result >= 0 && \result <= 6;
	public int getMove();

}