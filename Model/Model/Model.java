package Model;

import java.util.Observer;

/**
 * An interface that gives functionality for the interaction with the model.
 * @author peter
 */
public interface Model {

	/**
	 * Places a stone in the given column for the given player if the move is legal
	 * and the player is on turn. Then checks if the board has a winner,draw, or no winner.
	 * If 0 is returned then the game hasn't ended yet.
	 * If 1 is returned then the player has won.
	 * If 2 is returned then there is a draw.
	 * @param column <code> => 0 && column <= 6</code>
	 * @param player <code> == 1 || player == 2</code>
	 */
	int doMove(int column, int player);
	
	/**
	 * Adds an Observer to the Observable
	 * @param o is an Observer && <code>0 != null</code>
	 */
	public void addObserver(Observer o);

	public boolean isLegalMove(int column);
	
	public boolean onTurn(int player);
}