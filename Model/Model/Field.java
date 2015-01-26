package Model;

/**
 * This class keeps track of the status of field. This status can be
 * empty, filled by player 1 or filled by player 2.
 * @author peter
 */
public class Field {

	private /*@ spec_public @*/ int status;
	private /*@ spec_public @*/ final int EMPTY = 0;
	
	/*@public invariant 0 <= status && status <= 2; @*/ //class invariant

	/**
	 * Makes a new field with the status <code>EMPTY</code>
	 */
	//@ ensures status == EMPTY;
	public Field() {
		status = EMPTY;
	}

	/**
	 * Checks if the field is <code>EMPTY</code> or filled by a player.
	 * @return If <code>true</code> then the field is <code>EMPTY</code>, if 
	 * 		   <code>false</code> then the field is filled by a player.
	 */
	public boolean isEmpty() {
		boolean result = false;
		if(status == EMPTY)	{
			result = true;
		}
		return result;
	}

	/**
	 * Changes the status of the field to filled by the given player.
	 * @param <code>player == 1 || 2</code>
	 */
	//@ requires player == 1 || player == 2;
	//@ ensures status == player;
	public void setField(int player) {
		status = player;
	}

	/**
	 * Checks if the field is filled by the given player
	 * @param <code>player == 1 || 2</code>
	 * @return If <code>true</code> then the field is filled by <code>player</code>, 
	 * 		   if <code>false</code> then the field is not filled by <code>player</code>.
	 */
	//@ requires player == 1 || player == 2;
	//@ pure;
	public boolean isField(int player) {
		boolean result = false;
		if(status == player)	{
			result = true;
		}
		return result;
	}
}