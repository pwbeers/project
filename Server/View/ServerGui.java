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

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.GridLayout;

import javax.swing.UIManager;
import javax.swing.JToggleButton;
import javax.swing.JSlider;
import javax.swing.JTextArea;
import javax.swing.BoxLayout;

/**
 * A ServerGui that shows a graphical interface for the Server/user to use.
 * @author peter
 */
public class ServerGui implements View {

	private JFrame frame;
	private ActionListener controller;
	private JTextField textField;
	private JTextArea textArea;

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
		frame.getContentPane().setLayout(null);
		
		textArea = new JTextArea();
		textArea.setBounds(0, 0, 434, 199);
		frame.getContentPane().add(textArea);
		
		JButton btnNewButton = new JButton("Send");
		btnNewButton.setBounds(335, 210, 89, 41);
		frame.getContentPane().add(btnNewButton);
		
		textField = new JTextField();
		textField.setBounds(10, 220, 314, 20);
		frame.getContentPane().add(textField);
		textField.setColumns(10);
		
		btnNewButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				String Line = textField.getText();
				printTekst(Line);
			}
		});

	}
	
	public void printTekst(String message){
		textArea.append(message);		
	}

	public void startScherm(){
		throw new UnsupportedOperationException();
	}
	
	public void update(Observable arg0, Object arg1) {
		throw new UnsupportedOperationException();
	}

	public  void main(String[] args){
		initialize();
	}
}
