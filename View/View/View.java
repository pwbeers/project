package View;

import java.awt.event.ActionListener;
import java.util.Observer;

import javax.swing.event.AncestorListener;

public interface View extends Observer	{

	void printTekst(String message);

	void startScherm();
}