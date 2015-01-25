package Model;

/**
 * Keeps track of a board with multiple fields in it.
 * @author peter
 */
// TODO there should be a function which enables the GUI to display which fields makup the winning four streak

public class Board {

	private /*@ spec_public @*/ Field[][] fields;
	private /*@ spec_public @*/ final int STONES = 4;
	private /*@ spec_public @*/ final int COLUMNS = 7;
	private /*@ spec_public @*/ final int ROWS = 6;
	private /*@ spec_public @*/ final int PLAYERONE = 1;
	private /*@ spec_public @*/ final int PLAYERTWO = 2;

	/*@public invariant fields.length == COLUMNS && fields[COLUMNS - 1].length == ROWS; @*/ //class invariant
	
	/**
	 * Makes a new board filled with empty fields.
	 */
	//@ ensures fields != null && fields.length == COLUMNS && fields[COLUMNS - 1].length == ROWS;
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
	 * @param column <code>=> 0 && column <= COLUMNS - 1</code>
	 * @return If <code>true</code> then the move is legal<code>EMPTY</code>, if 
	 * 		   <code>false</code> then the move is illegal.
	 */
	//@ requires column >= 0 && column <= COLUMNS - 1;
	public boolean legalMove(int column) {
		boolean result = false;
		if(nextEmptyRowInColumn(column) != 6)	{
			result = true;
		}
		return result;
	}

	/**
	 * Places a stone by the given player in the given column on the board.
	 * @param column <code>=> 0 && column <= COLUMNS - 1</code>
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires column >= 0 && column <= COLUMNS - 1;
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
		for (int yBegin = 0; yBegin < fields[yBegin].length && !result; yBegin++) {
			for (int xBegin = 0; xBegin < 4 && !result; xBegin++) {
				boolean winner = true;
				for (int j = 0; j < STONES && winner; j++) {
					winner = fields[xBegin + j][yBegin].isField(player);
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
		for (int xBegin = 0; xBegin < fields.length - STONES && !result; xBegin++) {
			for (int yBegin = 0; yBegin < 3 && !result; yBegin++) {
				boolean winner = true;
				for (int j = 0; j < fields[j].length && winner; j++) {
					winner = fields[xBegin][yBegin + j].isField(player);
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
		//Checks if there is a diagonal winner from left to right
		for (int yBegin = 0; yBegin < fields[yBegin].length - STONES && !result; yBegin++) {
			for (int xBegin = 0; xBegin < 4 && !result; xBegin++) {
				boolean winner = true;
				for (int j = 0; j < STONES && winner; j++) {
					winner = fields[j+xBegin][j+yBegin].isField(player);
				}
				if(winner == true)	{
					result = true;
				}
			}
		}
		//Checks if there is a diagonal winner from right to left
		for (int yBegin = 0; yBegin < fields[yBegin].length - STONES && !result; yBegin++) {
			for (int xBegin = fields.length - 1; xBegin > 2 && !result; xBegin--) {
				boolean winner = true;
				for (int j = 0; j < STONES && winner; j++) {
					winner = fields[j+xBegin][j+yBegin].isField(player);
				}
				if(winner == true)	{
					result = true;
				}
			}
		}
		return result;
	}
	
	/**
	 * Gives the bottommost row that is empty in the given column.
	 * And returns 6 if the column is filled completely.
	 * @param column >= 0 && column <= COLUMNS - 1
	 * @return >= 0 && return <= 6
	 */
	//@ requires column >= 0 && column <= COLUMNS - 1;
	//@ ensures \result >= 0 && \result <= ROWS;
	//@ pure;
	private /*@ spec_public @*/ int nextEmptyRowInColumn(int column)	{
		int result = ROWS;
		for (int i = 0; i < fields[column].length && result == 6; i++) {
			if(fields[column][i].isEmpty())	{
				result = i;
			}
		}
		return result;
	}
	
	/**
	 * Determines if the board is full or empty
	 * @return If <code>true</code> then the board is full, if <code>false</code> 
	 * 		   then the board has no winner for the given player with a diagonal line.
	 */
	//@ requires fields != null;
	public boolean isBoardFull()	{
		boolean result = false;
		for (int x = 0; x < fields.length && !result; x++) {
			for (int y = 0; y < fields[x].length && !result; y++) {
				result = fields[x][y].isEmpty();
			}
		}
		return result;
	}
	
	/**
	 * Tells the caller if the given field is filled by player 1 or player 2 or is still empty.
	 * @param field
	 * @return is 0 if empty, is 1 if player 1 fills the field, is 2 if player 2 fills the field
	 */
	public int isFiledWith(int column, int row)	{
		int result = 0;
		if(fields[column][row].isField(PLAYERONE))	{
			result = 1;
		}
		else if(fields[column][row].isField(PLAYERTWO))	{
			result = 2;
		}
		return result;
	}
	
	/**
	 * Makes a copy of the current board
	 * @return
	 */
	public Board copy()	{
		Board copyBoard = new Board();
		for (int i = 0; i < COLUMNS; i++) {
			for (int j = 0; j < ROWS; j++) {
				copyBoard.doMove(i, isFiledWith(i, j));
			}
		}
		return copyBoard;
	}

}