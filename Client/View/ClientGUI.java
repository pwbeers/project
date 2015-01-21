package View;

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
 * A ClientGUI that shows an graphical interface for the client/user to use.
 * @author peter
 */
public class ClientGUI implements View {

	private JFrame frmFour;
	private ActionListener controller;
	
	//JObjects to be called
	private JTextField connectionPortText;
	private JTextField connectionIPText;
	private JButton[] board; 
	private JTextField gameName;
	private JLabel message;

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
		for (int row = 5; row >= 0; row--) {
			for (int column = 0; column < 7; column++) {
				board[row * 7 + column] = new JButton(new ImageIcon(ClientGUI.class.getResource("/View/EmptyField.png")));
				board[row * 7 + column].setOpaque(false);
				board[row * 7 + column].setContentAreaFilled(false);
				board[row * 7 + column].setBorderPainted(false);
				board[row * 7 + column].setPreferredSize(new Dimension(75, 75));
				board[row * 7 + column].setActionCommand(Integer.toString(column));
				board[row * 7 + column].addActionListener(controller);
				boardButtons.add(board[row * 7 + column]);
			}
		}
		
		JPanel connectionPanel = new JPanel();
		connectionPanel.setBounds(35, 16, 715, 37);
		frmFour.getContentPane().add(connectionPanel);
		connectionPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		JLabel connectionPortLabel = new JLabel("   Port:");
		connectionPanel.add(connectionPortLabel);
		
		connectionPortText = new JTextField("2220");
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
		
		JButton gameStartGame = new JButton("Start Game");
		gameStartGame.addActionListener(controller);
		gameStartGame.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameStartGame);
		
		JButton gameEndGame = new JButton("End Game");
		gameEndGame.addActionListener(controller);
		gameEndGame.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameEndGame);
		
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
		
		JPanel messagePanel = new JPanel();
		messagePanel.setBounds(35, 49, 715, 27);
		frmFour.getContentPane().add(messagePanel);
		
		message = new JLabel("");
		message.setForeground(Color.RED);
		messagePanel.add(message);

	}

	public void printTekst(String message) {
		this.message.setText(message);
	}

	public void startScherm() {
		throw new UnsupportedOperationException();
	}

	public void update(Observable arg0, Object arg1) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Gives the arguments portnumber and ip adress to the caller. 
	 * @return length() of return == 2
	 */
	//@ ensures \result.length == 2;
	public String[] getConnection()	{
		String[] result = new String[2];
		result[0] = connectionPortText.getText();
		result[1] = connectionIPText.getText();
		return result;
	}
	
	public String getChallenge()	{
		throw new UnsupportedOperationException();
	}
	
	public String getMessage()	{
		throw new UnsupportedOperationException();
	}
	
	public String getStartGame()	{
		return gameName.getText();
	}
	
	/**
	 * Is called to give a hint, as given in column, to the gui.
	 * @param column
	 */
	public void hint(int column)	{
		//TODO
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Starts a leaderboard screen giving the param leaderboard as data.
	 * @param leaderboard
	 */
	public void printLeaderboard(String[] leaderboard)	{
		//TODO
		throw new UnsupportedOperationException();
	}
}
