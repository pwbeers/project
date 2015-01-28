package Model;

import java.util.Observable;
import java.util.Observer;

/**
 * This class keeps track of a game from start till finish.
 * @author peter, Stephan
 */
public class Game extends Observable implements Model	{

	// ------------------ Instance variables ----------------
	private /*@ spec_public @*/ Board board;
	private /*@ spec_public @*/ int currentTurn; //the Player who is currently on turn	

	
	/*@public invariant board != null; @*/ //class invariant
	/*@public invariant currentTurn == 1 || currentTurn == 2; @*/ //class invariant
	
	// ------------------ Constructor ------------------------
	/**
	 * Makes a new Board class and saves it
	 * sets current Turn to 1. Client needs it to be 2.
	 */
	//@ ensures board != null && currentTurn == 1 || currentTurn == 2;
	public Game(int turnInt) {
		board = new Board();
		currentTurn = turnInt;
	}

	// ------------------ Queries --------------------------
	/**
	 * Checks if the given player is on Turn at the moment.
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires player == 1 || player == 2;
	public boolean onTurn(int player) {
		if (player == currentTurn){
			return true;					
		}else{
			return false;
		}
	}
	
	/**
	 * Checks if the given player has won the game.
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires player == 1 || player == 2;	
	public boolean isWinner(int player) {
		if(board.horizontalWinner(player) == true){
			return true;
		}else if (board.diagonalWinner(player) == true){
			return true;
		}else if (board.verticalWinner(player) == true){
			return true;
		}else {
			return false;
		}
	}
	
	/**
	 * Checks if placing a stone in the given column is a legal move.
	 * @param column >= 0 && column <= 6
	 */
	//@ requires column >= 0 && column <= 6;
	public boolean isLegalMove(int column) {
		if(board.legalMove(column) == true){
			return true;
		}else{
			return false;
		}
	}

	/**
	 * Places a stone in the given column for the given player if the move is legal
	 * and the player is on turn. Then checks if the board has a winner,draw, or no winner.
	 * Then changes the turn of the player.
	 * If 0 is returned then there the game can continue and the other player is on turn.
	 * If 1 is returned then the player has won.
	 * If 2 is returned then there is a draw.
	 * @param column <code>=> 0 && column <= 6</code>
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires column >= 0 && column <= 6;
	//@ requires player == 1 || player == 2;
	//@ ensures \result == 0 || \result == 1 || \result == 2;
	public int doMove(int column, int player) {	
		board.doMove(column, player);
		Integer[] field = new Integer[3];
		field[0] = column;
		field[1] = board.nextEmptyRowInColumn(column) - 1;
		field[2] = player;
		setChanged();
		notifyObservers(field);
		if (isWinner(player)){ 
			//Check if after the move there is a winner.
			return 1;
		}
		else if (board.isBoardFull() == true){  
			//Check is the game is over because this was the last move.
			return 2;
		}
		else { 
			//The Game continues.
			nextTurn();
			return 0;
		}
	}

	// ------------------ Commands --------------------------
	/**
	 * Sets the currentTurn variable to 2 when it is 1 and to 1 when it is 2 using modulo dividing 
	 * on numberOfTurns.
	 */
	//@ requires currentTurn == 1 || currentTurn == 2;
	//@ ensures currentTurn == 1 || currentTurn == 2;
	public void nextTurn() {
		currentTurn = (currentTurn % 2) + 1;
	}
	
	/**
	 * Adds an observer to this observable object
	 * @param newGUI the Observer
	 */
	public void addObserver(Observer newGUI){
		super.addObserver(newGUI);
	}

	//TODO remove
	public void setOnTurn() {
		currentTurn = 1;
	}
}
