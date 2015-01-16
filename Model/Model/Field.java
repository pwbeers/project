package Model;

/**
 * This class keeps track of the status of field. This status can be
 * empty, filled by player 1 or filled by player 2.
 * @author peter
 */
public class Field {

	private /*@ spec_public @*/ int status;
	private /*@ spec_public @*/ final int EMPTY = 0;
	private /*@ spec_public @*/ final int PLAYERONE = 1;
	private /*@ spec_public @*/ final int PLAYERTWO = 2;
	
	/*@public invariant 0 <= status && status <= 2; @*/ //class invariant

	/**
	 * Makes a new field with the status <code>EMPTY</code>
	 */
	//@ ensures status == EMPTY;
	public Field() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the field is <code>EMPTY</code> or filled by a player.
	 * @return If <code>true</code> then the field is <code>EMPTY</code>, if 
	 * 		   <code>false</code> then the field is filled by a player.
	 */
	public boolean isEmpty() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Changes the status of the field to filled by the given player.
	 * @param <code>player == PLAYERONE || PLAYERTWO</code>
	 */
	//@ requires player == PLAYERONE || player == PLAYERTWO;
	//@ ensures status == player;
	public void setField(int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Checks if the field is filled by the given player
	 * @param <code>player == PLAYERONE || PLAYERTWO</code>
	 * @return If <code>true</code> then the field is filled by <code>player</code>, 
	 * 		   if <code>false</code> then the field is not filled by <code>player</code>.
	 */
	//@ requires player == PLAYERONE || player == PLAYERTWO;
	public boolean isField(int player) {
		throw new UnsupportedOperationException();
	}

}