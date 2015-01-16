package View;

import java.awt.event.ActionListener;
import javax.swing.event.AncestorListener;
import View.GUI;

/**
 * A graphical user interface for the client.
 * @author peter
 */
public class ClientGUI_not_eclipse implements GUI	{

	private /*@ spec_public @*/ ActionListener controller;
	
	/*@public invariant controller != null; @*/ //class invariant
	
	/**
	 * Makes a new clientGUI screen.
	 */
	public ClientGUI_not_eclipse()	{
		
	}
	
	/**
	 * Prints a message one the GUI.
	 * @param message is the tekst that is to be printed on the GUI.
	 */
	//@ requires message != null & message.length() > 0;
	public void printTekst(String message) {
		
	}

	/**
	 * Desribes and starts a screen with all the buttons and screen information.
	 */
	public void startScherm() {
		
	}

	/**
	 * Saves the given controller.
	 * @param controller != null
	 */
	//@ requires controller != null;
	public void addController(ActionListener controller) {
		
	}

}
