package View;

import javax.swing.event.AncestorListener;

public interface ServerGUI {

	void printTekst();

	void startScherm();

	/**
	 * 
	 * @param controller
	 */
	void addController(AncestorListener controller);

}