package View;

import javax.swing.event.AncestorListener;

public interface ClientGUI {

	void printTekst();

	void startScherm();

	/**
	 * 
	 * @param controller
	 */
	void addController(AncestorListener controller);

}