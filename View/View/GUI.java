package View;

import javax.swing.event.AncestorListener;

public interface GUI {

	void printTekst();

	void startScherm();

	/**
	 * 
	 * @param controller
	 */
	void addController(AncestorListener controller);

}