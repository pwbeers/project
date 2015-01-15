package Model;

/**
 * Deze klasse houdt de waarde bij van een veld. De waarde kan
 * leeg, gevuld door speler 1 of gevuld door speler 2 zijn.
 * @author peter
 */
public class Field {

	private int status;

	/**
	 * Maakt een nieuw field aan met de standaard waarde van een leeg veld.
	 */
	public Field() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Controleert of het veld leeg is of niet
	 * @return If <code>true</code> dan is het veld leeg, if <code>false</code>
	 * 		   dan is het veld bezet door één van de twee spelers.
	 */
	public boolean isEmpty() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Maakt een veld bezet door de meegegeven speler
	 * @param player = 0 || 1
	 */
	public void setField(int player) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Controleert of het veld bezet is door de meegegeven speler of niet
	 * @param player = 0 || 1
	 * @return If <code>true</code> dan is het veld bezet door de meegegeven speler, 
	 * 		   if <code>false</code> dan is het veld niet bezet door de meegegeven speler
	 */
	public boolean isField(int player) {
		throw new UnsupportedOperationException();
	}

}