package Model;

/**
 * Keeps track of a board with multiple fields in it.
 * @author peter
 */
public class Board {

	private /*@ spec_public @*/ Field[][] fields;
	private /*@ spec_public @*/ final int MOSTLEFTCOLUMN = 0;
	private /*@ spec_public @*/ final int MOSTRIGHTCOLUMN = 6;
	private /*@ spec_public @*/ final int STONES = 4;
	private /*@ spec_public @*/ final int COLUMNS = 7;
	private /*@ spec_public @*/ final int ROWS = 6;

	/*@public invariant fields.length == COLUMNS && fields[MOSTRIGHTCOLUMN].length == ROWS; @*/ //class invariant
	
	/**
	 * Makes a new board filled with empty fields.
	 */
	//@ ensures fields != null && fields.length == COLUMNS && fields[MOSTRIGHTCOLUMN].length == ROWS;
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
	//@ requires column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN;
	public boolean legalMove(int column) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Places a stone by the given player in the given column on the board.
	 * @param column <code>=> MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN</code>
	 * @param player <code>== 0 || 1</code>
	 */
	//@ requires column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN;
	//@ requires player == 1 || player == 2;
	//@ ensures fields[column][nextEmptyRowInColumn(column)-1].isField(player);
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
	//@ requires player == 1 || player == 2;
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
	//@ requires player == 1 || player == 2;
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
	//@ requires player == 1 || player == 2;
	public boolean diagonalWinner(int player) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Gives the bottommost row that is empty in the given column.
	 * @param column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN
	 * @return >= 0 && return <= 5
	 */
	//@ requires column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN;
	//@ ensures \result >= 0 && \result <= ROWS -1;
	private /*@ spec_public @*/ int nextEmptyRowInColumn(int column)	{
		throw new UnsupportedOperationException();
	}

}