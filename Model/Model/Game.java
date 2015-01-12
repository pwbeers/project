package Model;

public class Game {
	
	private Field[][] board;
	
	/**
	 * Bij aanroepen wordt een nieuw board gemaakt met een kolom van 7 en 6 rijen
	 * in elke kolom.
	 */
	public Game()	{
		board = new Field[7][6];
		for (int i = 0; i < board.length; i++) {
			for (int j = 0; j < board[i].length; j++) {
				board[i][j] = new Field();
			}
		}
	}
}
