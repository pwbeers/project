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
	private /*@ spec_public @*/ int numberOfTurns; //the number of turns played in this game, used to 
	//-assign who is on turn	
	private Observer GUI;
	
	/*@public invariant board != null; @*/ //class invariant
	/*@public invariant currentTurn == 1 || currentTurn == 2; @*/ //class invariant
	/*@public invariant numberOfTurns > 0 ; @*/ //class invariant
	
	// ------------------ Constructor ------------------------
	/**
	 * Makes a new Board class and saves it
	 * sets current Turn to 1
	 */
	//@ ensures board != null && numberOfTurns > 0 && currentTurn == 1;
	public Game(Observer newGUI) {
		GUI = newGUI;
		board = new Board();
		currentTurn = 1;
		numberOfTurns = 1;
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
	 * If 0 is returned then the player is not on turn or the player made an illegal move.
	 * If 1 is returned then the player has won.
	 * If 2 is returned then there is a draw.
	 * If 3 is returned then there the game can continue and the other player is on turn.
	 * @param column <code>=> 0 && column <= 6</code>
	 * @param player <code>== 1 || player == 2</code>
	 */
	//@ requires column >= 0 && column <= 6;
	//@ requires player == 1 || player == 2;
	//@ ensures \result == 0 || \result == 1 || \result == 2;
	public int doMove(int column, int player) {
		
		if (onTurn(player) == false){ //Check if it's actually the players turn.
			return 0;
		}else if (isLegalMove(column) == false){ //Check if the move is legal.
			return 0;
		}else{
			board.doMove(column, player);
		}
		if (isWinner(player)){ //Check if after the mover there is a winner.
			return 1; // TODO implement board copy and observer notification
		}else if (board.isBoardFull() == true){  //Check is the game is over because this was the last move.
			return 2;
		}else { //The Game continues.
			nextTurn();
			return 3;
		}
	}

	// ------------------ Commands --------------------------
	/**
	 * Sets the currentTurn variable to 2 when it is 1 and to 1 when it is 2 using modulo dividing 
	 * on numberOfTurns.
	 * Increases numberOfTurns with 1.
	 */
	//@ requires currentTurn == 1 || currentTurn == 2 && numberOfTurns>0;
	//@ ensures currentTurn == 1 || currentTurn == 2 && numberOfTurns == \old(numberOfTurns) + 1;
	private void nextTurn() {
		currentTurn = (numberOfTurns % 2) + 1;
		numberOfTurns++;
	}
}