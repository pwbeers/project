package View;

import java.awt.EventQueue;

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
import javax.swing.JSplitPane;
import javax.swing.JScrollPane;

import java.awt.GridBagLayout;
import java.awt.GridBagConstraints;
import java.awt.Insets;

import com.jgoodies.forms.layout.FormLayout;
import com.jgoodies.forms.layout.ColumnSpec;
import com.jgoodies.forms.layout.RowSpec;

import java.awt.Component;

import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.LayoutStyle.ComponentPlacement;

import com.jgoodies.forms.factories.FormFactory;

import java.awt.CardLayout;

/**
 * A ServerGui that shows a graphical interface for the Server/user to use.
 * @author Stephan
 */

//TODO repaint

public class ServerGui implements View {

	private ActionListener controller;
	
	private JFrame serverFrame;
	
	private JPanel addresErrorPanel;
	
	private JTextField manualInTextField;
	private JTextField portTestField;
	
	private JTextArea errorTextArea;
	private JTextArea currentGamesTextArea;
	private JTextArea connectedClientsTextArea;

	/**
	 * Create the application.
	 */
	public ServerGui(ActionListener newController) {
		controller = newController;
		initialize();
		//System.out.println("ServerGUI initialized");
	}

	/**
	 * Initialize the contents of the frame.
	 */
	private void initialize() {
		serverFrame = new JFrame();
		serverFrame.setBounds(100, 100, 713, 511);
		serverFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		serverFrame.getContentPane().setLayout(new GridLayout(0, 2, 0, 0));
		serverFrame.setVisible(true);
		
		addresErrorPanel = new JPanel();
		serverFrame.getContentPane().add(addresErrorPanel);
		
		JPanel adressPanel = new JPanel();
		adressPanel.setLayout(new GridLayout(0, 3, 0, 0));
		
		JPanel portNumberPanel = new JPanel();
		adressPanel.add(portNumberPanel);
		
		JLabel addresFieldLabel = new JLabel("port:");
		portNumberPanel.add(addresFieldLabel);
		addresFieldLabel.setHorizontalAlignment(SwingConstants.CENTER);
		
		portTestField = new JTextField();
		portNumberPanel.add(portTestField);
		portTestField.setColumns(10);
		
		JPanel iNetPanel = new JPanel();
		adressPanel.add(iNetPanel);
		iNetPanel.setLayout(new FormLayout(new ColumnSpec[] {
				ColumnSpec.decode("116px"),},
			new RowSpec[] {
				RowSpec.decode("27px"),
				FormFactory.LINE_GAP_ROWSPEC,
				RowSpec.decode("32px"),}));
		iNetPanel.setLayout(null);
		
		JLabel iNetAdresLabel = new JLabel("IP adress:");
		iNetAdresLabel.setBounds(25, 28, 49, 14);
		iNetPanel.add(iNetAdresLabel);
		iNetAdresLabel.setHorizontalAlignment(SwingConstants.CENTER);
		
		//TODO get local inet
		JLabel iNetLabel = new JLabel("INetAdress");
		iNetLabel.setBounds(25, 11, 54, 14);
		iNetPanel.add(iNetLabel);
		iNetLabel.setHorizontalAlignment(SwingConstants.CENTER);
		
		JPanel openPortPanel = new JPanel();
		adressPanel.add(openPortPanel);
		openPortPanel.setLayout(null);
		
		JButton openPortButton = new JButton("Open Port");
		openPortButton.setBounds(10, 11, 81, 23);
		openPortPanel.add(openPortButton);
		openPortButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) {
			}
		});
		
		JPanel errorPanel = new JPanel();
		GroupLayout gl_addresErrorPanel = new GroupLayout(addresErrorPanel);
		gl_addresErrorPanel.setHorizontalGroup(
			gl_addresErrorPanel.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_addresErrorPanel.createSequentialGroup()
					.addGroup(gl_addresErrorPanel.createParallelGroup(Alignment.LEADING)
						.addComponent(adressPanel, GroupLayout.PREFERRED_SIZE, 348, GroupLayout.PREFERRED_SIZE)
						.addComponent(errorPanel, GroupLayout.PREFERRED_SIZE, 348, GroupLayout.PREFERRED_SIZE))
					.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
		);
		gl_addresErrorPanel.setVerticalGroup(
			gl_addresErrorPanel.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_addresErrorPanel.createSequentialGroup()
					.addComponent(adressPanel, GroupLayout.PREFERRED_SIZE, 65, GroupLayout.PREFERRED_SIZE)
					.addPreferredGap(ComponentPlacement.UNRELATED)
					.addComponent(errorPanel, GroupLayout.PREFERRED_SIZE, 396, GroupLayout.PREFERRED_SIZE)
					.addGap(1))
		);
		
		errorTextArea = new JTextArea();
		
		JPanel manualInPanel = new JPanel();
		
		manualInTextField = new JTextField();
		manualInTextField.setColumns(10);
		
		JButton manualInButton = new JButton("Send In");
		GroupLayout gl_errorPanel = new GroupLayout(errorPanel);
		gl_errorPanel.setHorizontalGroup(
			gl_errorPanel.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_errorPanel.createSequentialGroup()
					.addGroup(gl_errorPanel.createParallelGroup(Alignment.LEADING)
						.addComponent(manualInPanel, GroupLayout.PREFERRED_SIZE, 348, GroupLayout.PREFERRED_SIZE)
						.addComponent(errorTextArea, GroupLayout.PREFERRED_SIZE, 348, GroupLayout.PREFERRED_SIZE))
					.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
		);
		gl_errorPanel.setVerticalGroup(
			gl_errorPanel.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_errorPanel.createSequentialGroup()
					.addComponent(errorTextArea, GroupLayout.PREFERRED_SIZE, 361, GroupLayout.PREFERRED_SIZE)
					.addPreferredGap(ComponentPlacement.UNRELATED)
					.addComponent(manualInPanel, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
					.addGap(1))
		);
		GroupLayout gl_manualInPanel = new GroupLayout(manualInPanel);
		gl_manualInPanel.setHorizontalGroup(
			gl_manualInPanel.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_manualInPanel.createSequentialGroup()
					.addComponent(manualInTextField, GroupLayout.PREFERRED_SIZE, 259, GroupLayout.PREFERRED_SIZE)
					.addComponent(manualInButton))
		);
		gl_manualInPanel.setVerticalGroup(
			gl_manualInPanel.createParallelGroup(Alignment.LEADING)
				.addComponent(manualInTextField, GroupLayout.PREFERRED_SIZE, 23, GroupLayout.PREFERRED_SIZE)
				.addComponent(manualInButton)
		);
		manualInPanel.setLayout(gl_manualInPanel);
		errorPanel.setLayout(gl_errorPanel);
		addresErrorPanel.setLayout(gl_addresErrorPanel);
		
		JPanel connectionsPanel = new JPanel();
		serverFrame.getContentPane().add(connectionsPanel);
		connectionsPanel.setLayout(new BoxLayout(connectionsPanel, BoxLayout.Y_AXIS));
		
		JPanel connectedClientsPanel = new JPanel();
		connectionsPanel.add(connectedClientsPanel);
		connectedClientsPanel.setLayout(null);
		
		JLabel connectedClientsLabel = new JLabel("Connected Clients:");
		connectedClientsLabel.setBounds(0, 0, 348, 29);
		connectedClientsPanel.add(connectedClientsLabel);
		
		connectedClientsTextArea = new JTextArea();
		connectedClientsTextArea.setBounds(0, 29, 348, 128);
		connectedClientsPanel.add(connectedClientsTextArea);
		
		JPanel currentGamesPanel = new JPanel();
		connectionsPanel.add(currentGamesPanel);
		currentGamesPanel.setLayout(null);
		
		JLabel currentGamesLabel = new JLabel("Current Games:");
		currentGamesLabel.setBounds(0, 0, 348, 24);
		currentGamesPanel.add(currentGamesLabel);
		
		currentGamesTextArea = new JTextArea();
		currentGamesTextArea.setBounds(0, 25, 348, 152);
		currentGamesPanel.add(currentGamesTextArea);
		
		JPanel extensionsPanel = new JPanel();
		connectionsPanel.add(extensionsPanel);
		
		JButton challengeButton = new JButton("Challenge");
		challengeButton.setBounds(0, 0, 177, 82);
		
		JButton chatButton = new JButton("Chat");
		chatButton.setBounds(176, 0, 172, 82);
		
		JButton leaderboardButton = new JButton("Leaderboard");
		leaderboardButton.setBounds(0, 81, 177, 76);
		
		JButton securityButton = new JButton("Security");
		securityButton.setBounds(176, 81, 172, 76);
		extensionsPanel.setLayout(null);
		extensionsPanel.add(challengeButton);
		extensionsPanel.add(chatButton);
		extensionsPanel.add(leaderboardButton);
		extensionsPanel.add(securityButton);

	}
	
	public void printText(String message){
		errorTextArea.append(message);		
	}
	
	public void appendActivePlayers(String player){
		connectedClientsTextArea.append(player + "\n");
	}
	
	public void appendCurrentGames(String game){
		currentGamesTextArea.append(game + "\n");	
	}

	public void startScherm(){
		throw new UnsupportedOperationException();
	}
	
	public void update(Observable arg0, Object arg1) {
		throw new UnsupportedOperationException();
	}

}
