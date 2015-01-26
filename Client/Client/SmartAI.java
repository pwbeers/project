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
		int result = 0;
		int player;
		if(maximizingPlayer)	{
			player = 1;
		}
		else	{
			player = 2;
		}
		if(depth == 0 || board.isBoardFull())	{
			int otherPlayer = (player % 2) + 1;
			//Add values to the situation on the board
			if(board.horizontalWinner(player) || board.verticalWinner(player) || board.diagonalWinner(player))	{
				result = 1000;
			}
			else if(board.horizontalWinner(otherPlayer) || board.verticalWinner(otherPlayer) || board.diagonalWinner(otherPlayer)){
				result = -1000;
			}
			else	{
				//three stones on a row
				result = result + 25 * (board.diagonalStoneCount(player, 3) + board.horizontalStoneCount(player, 3) + board.verticalStoneCount(player, 3));
				result = result - 25 * (board.diagonalStoneCount(otherPlayer, 3) + board.horizontalStoneCount(otherPlayer, 3) + board.verticalStoneCount(otherPlayer, 3));
				//two stones on a row
				result = result + 5 * (board.diagonalStoneCount(player, 2) + board.horizontalStoneCount(player, 2) + board.verticalStoneCount(player, 2));
				result = result - 5 * (board.diagonalStoneCount(otherPlayer, 2) + board.horizontalStoneCount(otherPlayer, 2) + board.verticalStoneCount(otherPlayer, 2));
				//single stones
				result = result + 1 * (board.diagonalStoneCount(player, 1) + board.horizontalStoneCount(player, 1) + board.verticalStoneCount(player, 1));
				result = result - 1 * (board.diagonalStoneCount(otherPlayer, 1) + board.horizontalStoneCount(otherPlayer, 1) + board.verticalStoneCount(otherPlayer, 1));
			}

			result = 0;
		}
		else	{
			if(maximizingPlayer)	{
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
