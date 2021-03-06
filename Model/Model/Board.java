package Model;

/**
 * Keeps track of a board with multiple fields in it.
 * @author peter
 */
public class Board {

	private /*@ spec_public @*/ Field[][] fields;
	private /*@ spec_public @*/ final int COLUMNS = 7;
	private /*@ spec_public @*/ final int ROWS = 6;
	private /*@ spec_public @*/ final int PLAYERONE = 1;
	private /*@ spec_public @*/ final int PLAYERTWO = 2;
	private /*@ spec_public @*/ final int STONES = 4;

	/*@public invariant fields.length == COLUMNS && fields[COLUMNS - 1].length == ROWS; @*/ //class invariant
	
	/**
	 * Makes a new board filled with empty fields.
	 */
	//@ ensures fields != null && fields.length == COLUMNS && fields[COLUMNS - 1].length == ROWS;
	public Board() {
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
		int amount = horizontalStoneCount(player, STONES);
		if(amount > 0)	{
			result = true;
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
		int amount = verticalStoneCount(player, STONES);
		if(amount > 0)	{
			result = true;
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
		int amount = diagonalStoneCount(player, STONES);
		if(amount > 0)	{
			result = true;
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
	public int nextEmptyRowInColumn(int column)	{
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
	public boolean isBoardFull()	{
		boolean result = true;
		for (int x = 0; x < COLUMNS && result; x++) {
			result = !legalMove(x);
		}
		return result;
	}
	
	/**
	 * Tells the caller if the given field is filled by player 1 or player 2 or is still empty.
	 * @param column >= 0 && column <= COLUMNS - 1
	 * @param row >= 0 && row <= ROWS - 1
	 * @return is 0 if empty, is 1 if player 1 fills the field, is 2 if player 2 fills the field
	 */
	//@ requires column >= 0 && column <= COLUMNS - 1;
	//@ requires row >= 0 && row <= ROWS - 1;
	//@ ensures \result >= 0 && \result <= 2;
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
	 * @return a new Board that has the same values as the current board
	 */
	//@ ensures \result != null;
	public Board copy()	{
		Board copyBoard = new Board();
		for (int i = 0; i < COLUMNS; i++) {
			for (int j = 0; j < ROWS; j++) {
				copyBoard.doMove(i, isFiledWith(i, j));
			}
		}
		return copyBoard;
	}
	
	/**
	 * Counts the amount of times that given amount of stones of given player are next to 
	 * eachother without interruption by an empty field or another players stones on a 
	 * horizontal line.
	 * @param player is the player for who the stones are counted
	 * @param amount is the amount of stones that are to be counted on one horizontal row
	 * @return the number of times a row of the given player with a given amount of stones is found
	 */
	//@ requires player == 1 || player == 2;
	//@ requires amount >= 0;
	//@ ensures \result >= 0;
	public int horizontalStoneCount(int player, int amount) {
		int result = 0;
		for (int yBegin = 0; yBegin < ROWS; yBegin++) {
			for (int xBegin = 0; xBegin < COLUMNS - (amount - 1); xBegin++) {
				int correct = 0;
				for (int j = 0; j < amount; j++) {
					if(fields[xBegin + j][yBegin].isField(player))	{
						correct++;
					}
				}
				if(correct == amount)	{
					result++;
				}
			}
		}
		return result;
	}
	
	/**
	 * Counts the amount of times that given amount of stones of given player are next to 
	 * eachother without interruption by an empty field or another players stones on a vertical
	 * line.
	 * @param player is the player for who the stones are counted
	 * @param amount is the amount of stones that are to be counted on one vertical row
	 * @return the number of times a row of the given player with a given amount of stones is found
	 */
	//@ requires player == 1 || player == 2;
	//@ requires amount >= 0;
	//@ ensures \result >= 0;
	public int verticalStoneCount(int player, int amount)	{
		int result = 0;
		for (int xBegin = 0; xBegin < COLUMNS; xBegin++) {
			for (int yBegin = 0; yBegin < ROWS - (amount - 1); yBegin++) {
				int correct = 0;
				for (int j = 0; j < amount; j++) {
					if(fields[xBegin][yBegin + j].isField(player))	{
						correct++;
					}
				}
				if(correct == amount)	{
					result++;
				}
			}
		}
		return result;
	}
	
	/**
	 * Counts the amount of times that given amount of stones of given player are diagonal to 
	 * eachother without interruption by an empty field or another players stones on a diagonal
	 * line.
	 * @param player is the player for who the stones are counted
	 * @param amount is the amount of stones that are to be counted on one diagonal row
	 * @return the number of times a row of the given player with a given amount of stones is found
	 */
	//@ requires player == 1 || player == 2;
	//@ requires amount >= 0;
	//@ ensures \result >= 0;
	public int diagonalStoneCount(int player, int amount)	{
		int result = 0;
		//Checks if there is a diagonal winner from left to right
		 for (int yBegin = 0; yBegin < ROWS - (amount - 1); yBegin++) {
			for (int xBegin = 0; xBegin < COLUMNS - (amount - 1); xBegin++) {
				int correct = 0;
				for (int j = 0; j < amount; j++) {
					if(fields[xBegin + j][yBegin + j].isField(player))	{
						correct++;
					}
				}
				if(correct == amount)	{
					result++;
				}
			}
		}
		//Checks if there is a diagonal winner from right to left
		for (int yBegin = 0; yBegin < ROWS - (amount - 1); yBegin++) {
			for (int xBegin = COLUMNS - 1; xBegin >= (amount - 1); xBegin--) {
				int correct = 0;
				for (int j = 0; j < amount; j++) {
					if(fields[xBegin - j][yBegin + j].isField(player))	{
						correct++;
					}
				}
				if(correct == amount)	{
					result++;
				}
			}
		}
		return result;
	}
}