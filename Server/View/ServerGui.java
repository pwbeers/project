package View;

import java.awt.EventQueue;

import javax.swing.JFrame;
import javax.swing.JFrame;
import javax.swing.JPanel;

import java.awt.FlowLayout;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.JButton;
import javax.swing.SwingConstants;
import javax.swing.JTextPane;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.SystemColor;
import java.util.Observable;

import javax.swing.ImageIcon;

import java.awt.event.ActionListener;
import java.awt.GridLayout;

import javax.swing.UIManager;
import javax.swing.JToggleButton;
import javax.swing.JSlider;

/**
 * A ServerGui that shows a graphical interface for the Server/user to use.
 * @author peter
 */
public class ServerGui implements View {

	private JFrame frame;
	private ActionListener controller;

	/**
	 * Create the application.
	 */
	public ServerGui(ActionListener newController) {
		controller = newController;
		initialize();
	}

	/**
	 * Initialize the contents of the frame.
	 */
	private void initialize() {
		frame = new JFrame();
		frame.setBounds(100, 100, 450, 300);
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
	}
	
	public void printTekst(String message){
		throw new UnsupportedOperationException();		
	}

	public void startScherm(){
		throw new UnsupportedOperationException();
	}


}
