package View;

import java.awt.event.ActionListener;

import javax.swing.event.AncestorListener;

public interface GUI {

	void printTekst(String message);

	void startScherm();

	/**
	 * 
	 * @param controller
	 */
	void addController(ActionListener controller);

}