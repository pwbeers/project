package modelTest;

import static org.junit.Assert.*;
import org.junit.Test;
import Model.Board;

public class BoardTest {
	
	@Test
	public void test() {
		doMoveTest();
		legalMoveTest();
		horizontalWinnerTest();
	}

	public void doMoveTest()	{
		Board board = new Board();
		assertEquals(0, board.isFiledWith(0, 0)); 
		board.doMove(0, 1);
		assertEquals(1, board.isFiledWith(0, 0)); 
		assertEquals(0, board.isFiledWith(3, 0)); 
		board.doMove(3, 1);
		assertEquals(1, board.isFiledWith(3, 0)); 
		assertEquals(0, board.isFiledWith(6, 0));
		board.doMove(6, 2);
		assertEquals(2, board.isFiledWith(6, 0)); 
	}
	
	public void legalMoveTest()	{
		Board board = new Board();
		board.doMove(0, 1);
		board.doMove(0, 1);
		assertEquals(true, board.legalMove(0));
		board.doMove(0, 1);
		board.doMove(0, 1);
		assertEquals(true, board.legalMove(0));
		board.doMove(0, 1);
		board.doMove(0, 1);
		assertEquals(false, board.legalMove(0));
	}
	
	public void horizontalWinnerTest()	{
		Board board = new Board();
		board.doMove(0, 1);
		board.doMove(0, 1);
	}
}
