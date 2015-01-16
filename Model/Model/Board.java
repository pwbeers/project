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
		//TODO loop invariant toevoegen.
		fields = new Field[COLUMNS][ROWS];
		for (int i = 0; i < fields.length; i++) {
			for (int j = 0; j < fields[i].length; j++) {
				fields[i][j] = new Field();
			}
		}
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
		boolean result = false;
		if(nextEmptyRowInColumn(column) != 6)	{
			result = true;
		}
		return result;
	}

	/**
	 * Places a stone by the given player in the given column on the board.
	 * @param column <code>=> MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN</code>
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN;
	//@ requires player == 1 || player == 2;
	//@ ensures fields[column][nextEmptyRowInColumn(column)-1].isField(player);
	public void doMove(int column, int player) {
		fields[column][nextEmptyRowInColumn(column)].setField(player);
	}

	/**
	 * Checks if the board has a horizontal line of <code>STONES</code>
	 * stones for the given player.
	 * @param player <code>== 1 || player == 2</code>
	 * @return If <code>true</code> then the board has a winner for the given player with 
	 * 		   a horizontal line, if <code>false</code> then the board has no winner for 
	 * 		   the given player with a horizontal line.
	 */
	//@ requires player == 1 || player == 2;
	public boolean horizontalWinner(int player) {
		boolean result = false;
		for (int row = 0; row < fields[row].length && !result; row++) {
			for (int i = 0; i < 4 && !result; i++) {
				boolean winner = true;
				for (int j = 0; j < 4 && winner; j++) {
					winner = fields[row][i+j].isField(player);
				}
				if(winner == true)	{
					result = true;
				}
			}
		}
		return result;
	}

	/**
	 * Checks if the board has a vertical line of <code>STONES</code>
	 * stones for the given player.
	 * @param player <code>== 1 || player == 2</code>
	 * @return If <code>true</code> then the board has a winner for the given player with 
	 * 		   a vertical line, if <code>false</code> then the board has no winner for 
	 * 		   the given player with a vertical line.
	 */
	//@ requires player == 1 || player == 2;
	public boolean verticalWinner(int player) {
		boolean result = false;
		for (int column = 0; column < fields.length - 4 && !result; column++) {
			for (int i = 0; i < 3 && !result; i++) {
				boolean winner = true;
				for (int j = 0; j < fields[j].length && winner; j++) {
					winner = fields[i+j][column].isField(player);
				}
				if(winner == true)	{
					result = true;
				}
			}
		}
		return result;
	}

	/**
	 * Checks if the board has a diagonal line of <code>STONES</code>
	 * stones for the given player.
	 * @param player <code>== 1 || player == 2</code>
	 * @return If <code>true</code> then the board has a winner for the given player with 
	 * 		   a diagonal line, if <code>false</code> then the board has no winner for 
	 * 		   the given player with a diagonal line.
	 */
	//@ requires player == 1 || player == 2;
	public boolean diagonalWinner(int player) {
		boolean result = false;
		for (int row = 0; row < fields[row].length - 4 && !result; row++) {
			for (int i = 0; i < 4 && !result; i++) {
				boolean winner = true;
				for (int j = 0; j < 4 && winner; j++) {
					winner = fields[j+i][j+row].isField(player);
				}
				if(winner == true)	{
					result = true;
				}
			}
		}
		//TODO andere kant afmaken van Board
		return result;
	}
	
	/**
	 * Gives the bottommost row that is empty in the given column.
	 * And returns 6 if the column is filled completely.
	 * @param column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN
	 * @return >= 0 && return <= 6
	 */
	//@ requires column >= MOSTLEFTCOLUMN && column <= MOSTRIGHTCOLUMN;
	//@ ensures \result >= 0 && \result <= ROWS;
	private /*@ spec_public @*/ int nextEmptyRowInColumn(int column)	{
		throw new UnsupportedOperationException();
	}
	
	public boolean isBoardFull()	{
		throw new UnsupportedOperationException();
	}

}