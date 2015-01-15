package Model;

/**
 * Keeps track of a board with multiple fields in it.
 * @author peter
 */
public class Board {

	private Field[][] fields;
	private final int MOSTLEFTCOLUMN = 0;
	private final int MOSTRIGHTCOLUMN = 6;
	private final int STONES = 4;

	/**
	 * Makes a new board filled with empty fields.
	 */
	public Board() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks the board if the move in the given <code>column</code> is 
	 * a valid move.
	 * @param column <code>=> MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN</code>
	 * @return If <code>true</code> then the move is legal<code>EMPTY</code>, if 
	 * 		   <code>false</code> then the move is illegal.
	 */
	public boolean legalMove(int column) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Places a stone by the given player in the given column on the board.
	 * @param column <code>=> MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN</code>
	 * @param player <code>== 0 || 1</code>
	 */
	public void doMove(int column, int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the board has a horizontal line of <code>STONES</code>
	 * stones for the given player.
	 * @param player <code>== 0 || 1</code>
	 * @return If <code>true</code> then the board has a winner for the given player with 
	 * 		   a horizontal line, if <code>false</code> then the board has no winner for 
	 * 		   the given player with a horizontal line.
	 */
	public boolean horizontalWinner(int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the board has a vertical line of <code>STONES</code>
	 * stones for the given player.
	 * @param player <code>== 0 || 1</code>
	 * @return If <code>true</code> then the board has a winner for the given player with 
	 * 		   a vertical line, if <code>false</code> then the board has no winner for 
	 * 		   the given player with a vertical line.
	 */
	public boolean verticalWinner(int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the board has a diagonal line of <code>STONES</code>
	 * stones for the given player.
	 * @param player <code>== 0 || 1</code>
	 * @return If <code>true</code> then the board has a winner for the given player with 
	 * 		   a diagonal line, if <code>false</code> then the board has no winner for 
	 * 		   the given player with a diagonal line.
	 */
	public boolean diagonalWinner(int player) {
		throw new UnsupportedOperationException();
	}

}