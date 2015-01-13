package View;

public interface GUI {

	void printTekst();

	void startScherm();

	/**
	 * 
	 * @param controller
	 */
	void addController(Actionlistener controller);

}