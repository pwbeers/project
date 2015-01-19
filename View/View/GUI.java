package View;

import java.awt.event.ActionListener;
import java.util.Observer;

import javax.swing.event.AncestorListener;

public interface GUI extends Observer	{

	void printTekst(String message);

	void startScherm();

	/**
	 * 
	 * @param controller
	 */
	void addController(ActionListener controller);

}