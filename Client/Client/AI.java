package Client;

import java.util.Observer;

/**
 * Is an interface that is there for multiple leves of AI to be started on.
 * @author peter
 */
public interface AI extends Observer	{

	/**
	 * Asks the AI for a possible move to play in the current
	 * game that is on the board and legal.
	 * @return a legal move, \result >= 0 && \result <= 6
	 */
	public int getMove(int depth);

}