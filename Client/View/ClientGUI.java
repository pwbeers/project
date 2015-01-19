package View;

import java.awt.EventQueue;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JMenu;
import javax.swing.JPopupMenu;

import java.awt.Component;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.FlowLayout;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.JButton;
import javax.swing.SwingConstants;
import javax.swing.BoxLayout;
import javax.swing.JTextPane;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.SystemColor;
import java.io.File;
import java.util.NoSuchElementException;
import java.util.Observable;

import javax.swing.ImageIcon;

import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.GridLayout;

import javax.swing.UIManager;
import javax.swing.border.Border;

import java.awt.GridBagLayout;
import java.awt.GridBagConstraints;
import java.awt.Insets;

import javax.swing.JToggleButton;
import javax.swing.JSlider;

import Client.ClientController;

/**
 * A ClientGUI that shows an graphical interface for the client/user to use.
 * @author peter
 */
public class ClientGUI implements GUI {

	private JFrame frmFour;
	private JTextField connectionPortText;
	private JTextField connectionIPText;
	private JButton[] board; 
	private JTextField gameName;
	private ActionListener controller;

	/**
	 * Starts the ClientGUI and saves the given controller.
	 */
	public ClientGUI(ActionListener controller) {
		this.controller = controller;
		initialize();
		frmFour.setVisible(true);
	}

	/**
	 * Initialize the contents of the frame.
	 */
	private void initialize() {
		frmFour = new JFrame();
		frmFour.setTitle("Captain\u2019s Mistress");
		frmFour.setBounds(100, 100, 1200, 700);
		frmFour.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frmFour.getContentPane().setLayout(null);
		
		JPanel challengePanel = new JPanel();
		challengePanel.setBounds(780, 16, 370, 197);
		frmFour.getContentPane().add(challengePanel);
		challengePanel.setLayout(new BorderLayout(0, 0));
		
		JLabel challengeTitle = new JLabel("Challenge:");
		challengePanel.add(challengeTitle, BorderLayout.NORTH);
		
		JTextPane challengeText = new JTextPane();
		challengePanel.add(challengeText, BorderLayout.CENTER);
		
		JButton challengeButton = new JButton("Challenge");
		challengeButton.addActionListener(controller);
		challengePanel.add(challengeButton, BorderLayout.SOUTH);
		
		JPanel boardPanel = new JPanel();
		boardPanel.setBackground(SystemColor.textHighlight);
		boardPanel.setBounds(35, 75, 715, 500);
		frmFour.getContentPane().add(boardPanel);
		boardPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		JPanel boardButtons = new JPanel();
		boardButtons.setForeground(UIManager.getColor("textHighlight"));
		boardButtons.setBackground(UIManager.getColor("textHighlight"));
		boardPanel.add(boardButtons);
		boardButtons.setOpaque(false);
		boardButtons.setLayout(new GridLayout(6, 7, 24, 7));
		
		//TODO netter maken
		board = new JButton[7*6];
		for (int i = 0; i < 7 * 6; i++) {
			board[i] = new JButton(new ImageIcon(ClientGUI.class.getResource("/View/Geel.png")));
			board[i].setOpaque(false);
			board[i].setContentAreaFilled(false);
			board[i].setBorderPainted(false);
			board[i].setPreferredSize(new Dimension(75, 75));
			board[i].setActionCommand(Integer.toString(i));
			board[i].addActionListener(controller);
			boardButtons.add(board[i]);
		}
		
		JPanel connectionPanel = new JPanel();
		connectionPanel.setBounds(35, 16, 715, 43);
		frmFour.getContentPane().add(connectionPanel);
		connectionPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		JLabel connectionPortLabel = new JLabel("   Port:");
		connectionPanel.add(connectionPortLabel);
		
		connectionPortText = new JTextField();
		connectionPanel.add(connectionPortText);
		connectionPortText.setColumns(10);
		
		JLabel connectionIPLabel = new JLabel("   IP address:");
		connectionIPLabel.setHorizontalAlignment(SwingConstants.RIGHT);
		connectionPanel.add(connectionIPLabel);
		
		connectionIPText = new JTextField();
		connectionPanel.add(connectionIPText);
		connectionIPText.setColumns(10);
		
		JButton connectionButton = new JButton("Connect");
		connectionButton.addActionListener(controller);
		connectionPanel.add(connectionButton);
		
		JPanel chatPanel = new JPanel();
		chatPanel.setBounds(780, 229, 370, 197);
		frmFour.getContentPane().add(chatPanel);
		chatPanel.setLayout(new BorderLayout(0, 0));
		
		JTextPane chatTextScreen = new JTextPane();
		chatPanel.add(chatTextScreen);
		
		JTextField chatTextField = new JTextField();
		chatTextField.setActionCommand("chatText");
		chatTextField.addActionListener(controller);
		chatTextField.setText("Vul een bericht in...");
		
		chatTextField.setBorder(BorderFactory.createLineBorder(Color.BLACK));
		chatPanel.add(chatTextField, BorderLayout.SOUTH);
		
		JLabel chatTitle = new JLabel("Chat:");
		chatPanel.add(chatTitle, BorderLayout.NORTH);
		
		JPanel gamePanel = new JPanel();
		gamePanel.setBounds(780, 442, 370, 186);
		frmFour.getContentPane().add(gamePanel);
		gamePanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		JToggleButton gameHumanButton = new JToggleButton("Human player");
		gameHumanButton.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameHumanButton);
		
		JToggleButton gameAIButton = new JToggleButton("AI speler");
		gameAIButton.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameAIButton);
		
		gameName = new JTextField();
		gameName.setText("Spelernaam...");
		gameName.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameName);
		gameName.setColumns(10);
		
		JSlider gameAISlider = new JSlider();
		gameAISlider.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameAISlider);
		
		JButton gameStartGame = new JButton("StartGame");
		gameStartGame.addActionListener(controller);
		gameStartGame.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameStartGame);
		
		JPanel hintPanel = new JPanel();
		hintPanel.setBounds(35, 591, 350, 37);
		frmFour.getContentPane().add(hintPanel);
		
		JButton hintButton = new JButton("Hint");
		hintButton.addActionListener(controller);
		hintPanel.add(hintButton);
		
		JPanel leaderboardPanel = new JPanel();
		leaderboardPanel.setBounds(400, 591, 350, 37);
		frmFour.getContentPane().add(leaderboardPanel);
		
		JButton leaderboardButton = new JButton("LeaderBoard");
		leaderboardButton.addActionListener(controller);
		leaderboardPanel.add(leaderboardButton);

	}

	public void printTekst(String message) {
		// TODO Auto-generated method stub
	}

	public void startScherm() {
		// TODO Auto-generated method stub
	}

	public void update(Observable arg0, Object arg1) {
		// TODO Auto-generated method stub
		
	}
	
	public String[] getConnection()	{
		throw new UnsupportedOperationException();
	}
	
	public String getChallenge()	{
		throw new UnsupportedOperationException();
	}
	
	public String getMessage()	{
		throw new UnsupportedOperationException();
	}
	
	public String[] getStartGame()	{
		throw new UnsupportedOperationException();
	}
}
