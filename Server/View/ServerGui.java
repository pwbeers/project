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
import java.net.InetAddress;
import java.net.UnknownHostException;
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
import javax.swing.border.LineBorder;


/**
 * A ServerGui that shows a graphical interface for the Server/user to use.
 * @author Stephan
 */

//TODO repaint
//TODO refresh buttons on lists

public class ServerGui implements View {

	private ActionListener controller;
	
	private JFrame serverFrame;
	private JTextField portTestField;
	private JTextField portTextField;
	private JTextField textField;
	
	private JTextArea mainTextArea;
	private JTextArea activePlayersTextArea;
	private JTextArea currentGamesTextArea;
	private String inet;

	/**
	 * Create the application.
	 */
	public ServerGui(ActionListener newController) {
		controller = newController;
		initialize();
		//System.out.println("ServerGUI initialized");
		inet = "xxx.xx.xx.x";
		//TODO get local inet
		try {
			inet = InetAddress.getLocalHost().getHostAddress();
		} catch (UnknownHostException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * Initialize the contents of the frame.
	 */
	private void initialize() {
		serverFrame = new JFrame();
		serverFrame.setTitle("Captain's Mistress Server");
		serverFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		serverFrame.setBounds(200, 200, 900, 570);
		serverFrame.getContentPane().setBackground(Color.DARK_GRAY);
		serverFrame.getContentPane().setLayout(null);
		serverFrame.setVisible(true);
		
		JPanel addresTextPanel = new JPanel();
		addresTextPanel.setBounds(10, 67, 500, 450);
		serverFrame.getContentPane().add(addresTextPanel);
		addresTextPanel.setLayout(new BorderLayout(0, 0));
		
		mainTextArea = new JTextArea();
		mainTextArea.setEditable(false);
		mainTextArea.setLineWrap(true);
		addresTextPanel.add(mainTextArea, BorderLayout.CENTER);
		
		JPanel panel = new JPanel();
		addresTextPanel.add(panel, BorderLayout.SOUTH);
		
		textField = new JTextField();
		panel.add(textField);
		textField.setColumns(30);
		
		JButton btnNewButton = new JButton("Send In");
		panel.add(btnNewButton);
		
		JPanel currentPlayerPanel = new JPanel();
		currentPlayerPanel.setBounds(530, 11, 344, 210);
		serverFrame.getContentPane().add(currentPlayerPanel);
		currentPlayerPanel.setLayout(new BorderLayout(0, 0));
		
		activePlayersTextArea = new JTextArea();
		activePlayersTextArea.setEditable(false);
		activePlayersTextArea.setLineWrap(true);
		currentPlayerPanel.add(activePlayersTextArea, BorderLayout.CENTER);
		
		JLabel activePlayersLabel = new JLabel("Active Players:");
		activePlayersLabel.setHorizontalAlignment(SwingConstants.CENTER);
		currentPlayerPanel.add(activePlayersLabel, BorderLayout.NORTH);
		
		JPanel currentGamePanel = new JPanel();
		currentGamePanel.setBounds(530, 252, 344, 210);
		serverFrame.getContentPane().add(currentGamePanel);
		currentGamePanel.setLayout(new BorderLayout(0, 0));
		
		JLabel currentGameLabel = new JLabel("Current Games:");
		currentGameLabel.setHorizontalAlignment(SwingConstants.CENTER);
		currentGamePanel.add(currentGameLabel, BorderLayout.NORTH);
		
		currentGamesTextArea = new JTextArea();
		currentGamesTextArea.setEditable(false);
		currentGamesTextArea.setLineWrap(true);
		currentGamePanel.add(currentGamesTextArea, BorderLayout.CENTER);
		
		JButton leaderBoardButton = new JButton("Leaderboard");
		leaderBoardButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) {
			}
		});
		leaderBoardButton.setBounds(648, 494, 156, 23);
		serverFrame.getContentPane().add(leaderBoardButton);
		
		JPanel connectionsPanel = new JPanel();
		connectionsPanel.setBounds(10, 10, 500, 56);
		serverFrame.getContentPane().add(connectionsPanel);
		connectionsPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		JLabel portLabel = new JLabel("port:");
		connectionsPanel.add(portLabel);
		
		portTextField = new JTextField();
		connectionsPanel.add(portTextField);
		portTextField.setColumns(10);
		
		JLabel adressLabel = new JLabel("Ip address:");
		connectionsPanel.add(adressLabel);
		
		JLabel addressValueLabel = new JLabel("xxx.xx.xx");
		addressValueLabel.setHorizontalAlignment(SwingConstants.CENTER);
		connectionsPanel.add(addressValueLabel);
		
		JButton startButton = new JButton("Start");
		connectionsPanel.add(startButton);
	
	}
	
	public void printText(String message){
		mainTextArea.append(message + "\n");		
	}
	
	public void appendActivePlayers(String player){
		activePlayersTextArea.append(player + "\n");
	}
	
	public void appendCurrentGames(String game){
		currentGamesTextArea.append(game + "\n");	
	}
	
	public void clearActivePlayers(){
		activePlayersTextArea.setText("");
	}
	
	public void clearCurrentGames(){
		currentGamesTextArea.setText("");
	}

	public void startScherm(){
		throw new UnsupportedOperationException();
	}
	
	public void update(Observable arg0, Object arg1) {
		throw new UnsupportedOperationException();
	}
}
