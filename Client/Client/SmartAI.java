package Client;

import java.util.LinkedList;
import java.util.List;
import java.util.Observable;
import Model.Board;

public class SmartAI implements AI	{

	//Start andere classes
    private Board board;
    private final int COLUMNS = 7;
	
	/**
	 * Starts an implementation of SimpleAI
	 */
	public SmartAI() {
		board = null;
	}

	public void update(Observable arg0, Object arg1) {
		board = (Board) arg1;
	}

	@Override
	public int getMove(int depth) {
		return minimax(board, depth, true);
	}
	
	private int minimax(Board board, int depth, boolean maximizingPlayer)	{
		int result;
		int player;
		if(depth == 0 || board.isBoardFull())	{
			//TODO Add values to the situation on the board
			result = 0;
		}
		else	{
			if(maximizingPlayer)	{
				player = 1;
				result = -1000;
				List<Integer> legalMoves = new LinkedList<Integer>();
				for (int i = 0; i < COLUMNS; i++) {
					if(board.legalMove(i))	{
						legalMoves.add(i);
					}
				}
				for (int i = 0; i < legalMoves.size(); i++) {
					Board boardCopy = board.copy();
					boardCopy.doMove(legalMoves.get(i), player);
					int val = minimax(boardCopy, depth - 1, false);
					result = max(result, val);
				}
			}
			else	{
				player = 2;
				result = 1000;
				List<Integer> legalMoves = new LinkedList<Integer>();
				for (int i = 0; i < COLUMNS; i++) {
					if(board.legalMove(i))	{
						legalMoves.add(i);
					}
				}
				for (int i = 0; i < legalMoves.size(); i++) {
					Board boardCopy = board.copy();
					boardCopy.doMove(legalMoves.get(i), player);
					int val = minimax(boardCopy, depth - 1, true);
					result = min(result, val);
				}
			}
		}
		return result;
	}
	
	/**
	 * Returns the maximum of the two given numbers.
	 * @param value1
	 * @param value2
	 * @return
	 */
	private int max(int value1, int value2)	{
		int result;
		if(value1 > value2)	{
			result = value1;
		}
		else	{
			result = value2;
		}
		return result;
	}
	
	/**
	 * Returns the minimum of the two given numbers.
	 * @param value1
	 * @param value2
	 * @return
	 */
	private int min(int value1, int value2)	{
		int result;
		if(value1 < value2)	{
			result = value1;
		}
		else	{
			result = value2;
		}
		return result;
	}
}
