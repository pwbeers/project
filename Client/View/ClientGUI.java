package View;

import javax.swing.JFrame;
import javax.swing.JPanel;
import java.awt.FlowLayout;
import javax.swing.BorderFactory;
import javax.swing.ButtonGroup;
import javax.swing.Icon;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JTextField;
import javax.swing.JButton;
import javax.swing.SwingConstants;
import javax.swing.JTextPane;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.SystemColor;
import java.util.Observable;
import java.util.Observer;
import javax.swing.ImageIcon;
import java.awt.event.ActionListener;
import java.awt.GridLayout;
import javax.swing.UIManager;
import javax.swing.JToggleButton;
import javax.swing.JSlider;
import javax.swing.text.BadLocationException;
import javax.swing.text.StyledDocument;

/**
 * A ClientGUI that shows an graphical interface for the client/user to use.
 * @author peter
 */
public class ClientGUI implements View,Observer {

	private JFrame frmFour;
	private ActionListener controller;
	private LeaderboardGUI leaderboard;
	
	private final Icon EMPTYFIELD = new ImageIcon(ClientGUI.class.getResource("/View/EmptyField.png"));
	private final Icon YELLOWFIELD = new ImageIcon(ClientGUI.class.getResource("/View/Geel.png"));
	private final Icon REDFIELD = new ImageIcon(ClientGUI.class.getResource("/View/Rood.png"));
	private final Icon HINTFIELD = new ImageIcon(ClientGUI.class.getResource("/View/HintButton.png"));
	
	//JObjects to be called
	private JTextField connectionPortText;
	private JTextField connectionIPText;
	private JButton[] board; 
	private JTextField gameName;
	private JLabel message;
	private JTextPane chatTextScreen;
	private StyledDocument chatDocument;
	private JButton challengeButton;
	private JTextField chatTextField;
	private JButton gameStartGame;
	private JButton gameEndGame;
	private JButton hintButton;
	private JButton leaderboardButton;
	private JButton connectionButton;
	private JToggleButton gameHumanButton;
	private JToggleButton gameAIButton;
	private JSlider gameAISlider;
	private JPanel boardButtons;

	/**
	 * Starts the ClientGUI and saves the given controller.
	 */
	public ClientGUI(ActionListener controller) {
		this.controller = controller;
		initialize();
		frmFour.setVisible(true);
		beforeConnectionScreen();
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
		
		challengeButton = new JButton("Challenge");
		challengeButton.addActionListener(controller);
		challengePanel.add(challengeButton, BorderLayout.SOUTH);
		
		JPanel boardPanel = new JPanel();
		boardPanel.setBackground(SystemColor.textHighlight);
		boardPanel.setBounds(35, 75, 715, 500);
		frmFour.getContentPane().add(boardPanel);
		boardPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		boardButtons = new JPanel();
		boardButtons.setForeground(UIManager.getColor("textHighlight"));
		boardButtons.setBackground(UIManager.getColor("textHighlight"));
		boardPanel.add(boardButtons);
		boardButtons.setOpaque(false);
		boardButtons.setLayout(new GridLayout(6, 7, 24, 7));
		
		//TODO netter maken
		board = new JButton[7*6];
		for (int row = 5; row >= 0; row--) {
			for (int column = 0; column < 7; column++) {
				board[row * 7 + column] = new JButton(EMPTYFIELD);
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
		
		connectionPortText = new JTextField("2200");
		connectionPanel.add(connectionPortText);
		connectionPortText.setColumns(10);
		
		JLabel connectionIPLabel = new JLabel("   IP address:");
		connectionIPLabel.setHorizontalAlignment(SwingConstants.RIGHT);
		connectionPanel.add(connectionIPLabel);
		
		connectionIPText = new JTextField("130.89.95.188");
		connectionPanel.add(connectionIPText);
		connectionIPText.setColumns(10);
		
		connectionButton = new JButton("Connect");
		connectionButton.addActionListener(controller);
		connectionPanel.add(connectionButton);
		
		JPanel chatPanel = new JPanel();
		chatPanel.setBounds(780, 229, 370, 197);
		frmFour.getContentPane().add(chatPanel);
		chatPanel.setLayout(new BorderLayout(0, 0));
		
		chatTextScreen = new JTextPane();
		chatPanel.add(chatTextScreen);
		chatTextScreen.setEditable(false);
		
		chatTextField = new JTextField();
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
		
		gameHumanButton = new JToggleButton("Human player");
		gameHumanButton.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameHumanButton);
		
		gameAIButton = new JToggleButton("AI speler");
		gameAIButton.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameAIButton);
		
		gameName = new JTextField();
		gameName.setText("Player_");
		gameName.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameName);
		gameName.setColumns(10);
		
		gameAISlider = new JSlider();
		gameAISlider.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameAISlider);
		
		gameStartGame = new JButton("Start Game");
		gameStartGame.addActionListener(controller);
		gameStartGame.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameStartGame);
		
		gameEndGame = new JButton("End Game");
		gameEndGame.addActionListener(controller);
		gameEndGame.setPreferredSize(new Dimension(160, 30));
		gamePanel.add(gameEndGame);
		
		JPanel hintPanel = new JPanel();
		hintPanel.setBounds(35, 591, 350, 37);
		frmFour.getContentPane().add(hintPanel);
		
		hintButton = new JButton("Hint");
		hintButton.addActionListener(controller);
		hintPanel.add(hintButton);
		
		JPanel leaderboardPanel = new JPanel();
		leaderboardPanel.setBounds(400, 591, 350, 37);
		frmFour.getContentPane().add(leaderboardPanel);
		
		leaderboardButton = new JButton("LeaderBoard");
		leaderboardButton.addActionListener(controller);
		leaderboardPanel.add(leaderboardButton);
		
		JPanel messagePanel = new JPanel();
		messagePanel.setBounds(35, 49, 715, 27);
		frmFour.getContentPane().add(messagePanel);
		
		message = new JLabel("");
		message.setForeground(Color.RED);
		messagePanel.add(message);

		ButtonGroup buttonGroup = new ButtonGroup();
		buttonGroup.add(gameHumanButton);
		gameHumanButton.setSelected(true);
		buttonGroup.add(gameAIButton);
		gameAIButton.setSelected(false);
	}

	public void printText(String message) {
		this.message.setText(message);
	}

	public void startScherm() {
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
		boolean goOn = true;
		for (int i = 0; i < board.length && goOn; i++) {
			if(Integer.parseInt(board[i].getActionCommand()) == column && board[i].getIcon().equals(EMPTYFIELD))	{
				board[i].setIcon(HINTFIELD);
				goOn = false;
			}
		}
	}
	
	/**
	 * Starts a leaderboard screen giving the data as an argument
	 * @param leaderboard
	 */
	public void printLeaderboard(String[] leaderboard)	{
		if(this.leaderboard == null)	{
			this.leaderboard = new LeaderboardGUI(leaderboard);
			this.leaderboard.start();	
		}
		else	{
			this.leaderboard.updateData(leaderboard);
		}
	}
	
	/**
	 * Opens a window in which the user can select to accept the
	 * challenge from the given player name or decline it.
	 * @return if the challenge is accepted then true is returned, else false
	 */
	public boolean challenged(String name)	{
		boolean accept = false;
		int result = JOptionPane.showConfirmDialog(null, name + " has challenged you. Do you accept?","Challenge!",JOptionPane.YES_NO_OPTION);
		if(result == JOptionPane.YES_OPTION)	{
			accept = true;
		}
		else if(result == JOptionPane.NO_OPTION)	{
			accept = false;
		}
		return accept;
	}
	
	/**
	 * Prints a message from the server on the gui screen
	 * @param message
	 */
	public void guiMessage(String message)	{
		chatDocument = chatTextScreen.getStyledDocument();
		try {
			chatDocument.insertString(0, message, null);
		} catch (BadLocationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * Updates the board with a new field
	 */
	public void update(Observable o, Object arg) {
		Integer[] changedField = (Integer[]) arg;
		int column = changedField[0];
		int row = changedField[1];
		int player = changedField[2];
		Icon icon;
		if(player == 1)	{
			icon = REDFIELD;
		}
		else	{
			icon = YELLOWFIELD;
		}
		board[column + 7 * row].setIcon(icon);
	}
	
	/**
	 * Sets the gui up to be ready to start a new game
	 */
	public void setNewGame()	{
		//challenge button on
		challengeButton.setEnabled(false);
		//chat function on
		chatTextField.setEnabled(false);
		//Start game is on
		gameStartGame.setEnabled(true);
		//End game is off
		gameEndGame.setEnabled(false);
		//Board is off
		for (int i = 0; i < board.length; i++) {
			board[i].setEnabled(false);
		}
		//hint is off
		hintButton.setEnabled(false);
	}
	
	/**
	 * Tells the gui the game has ended and the given player has won the game.
	 * @param name
	 * @return true if another game should be started, false if not.
	 */
	public boolean gameWinner(String player)	{
		boolean accept = false;
		int result = JOptionPane.showConfirmDialog(null, player + " has won the game! Would you like to play another game?", "WINNER!",JOptionPane.YES_NO_OPTION);
		if(result == JOptionPane.YES_OPTION)	{
			accept = true;
		}
		else if(result == JOptionPane.NO_OPTION)	{
			accept = false;
		}
		return accept;
	}
	
	/**
	 * Tells the gui that the connection with the server has been broken.
	 */
	public void connectionBroken()	{
		challengeButton.setEnabled(false);
		chatTextField.setEnabled(false);
		gameStartGame.setEnabled(false);
		gameEndGame.setEnabled(false);
		gameName.setEnabled(false);
		for (int i = 0; i < board.length; i++) {
			board[i].setEnabled(false);
		}
		hintButton.setEnabled(false);
		leaderboardButton.setEnabled(false);
		connectionButton.setEnabled(true);
		gameHumanButton.setEnabled(false);
		gameAIButton.setEnabled(false);
		gameAISlider.setEnabled(false);
	}
	
	/**
	 * Sets the gui up that only a connection can be made and all
	 * other buttons are disabled.
	 */
	public void beforeConnectionScreen()	{
		challengeButton.setEnabled(false);
		chatTextField.setEnabled(false);
		gameStartGame.setEnabled(false);
		gameEndGame.setEnabled(false);
		hintButton.setEnabled(false);
		gameHumanButton.setEnabled(false);
		gameAIButton.setEnabled(false);
		gameAISlider.setEnabled(false);
		gameName.setEnabled(false);
		leaderboardButton.setEnabled(false);
		for (int i = 0; i < board.length; i++) {
			board[i].setEnabled(false);
		}
	}
	
	/**
	 * Sets the gui up with the appropriate functionality after a 
	 * connection has been made.
	 */
	public void setConnectionScreen()	{
		challengeButton.setEnabled(true);
		chatTextField.setEnabled(true);
		gameStartGame.setEnabled(true);
		gameHumanButton.setEnabled(true);
		gameAIButton.setEnabled(true);
		gameAISlider.setEnabled(true);
		gameName.setEnabled(true);
		leaderboardButton.setEnabled(true);
		connectionButton.setEnabled(false);
		connectionIPText.setEnabled(false);
		connectionPortText.setEnabled(false);
	}
	
	/**
	 * Sets the gui up with the appropriate functionality after a 
	 * game has been started.
	 */
	public void gameStartScreen()	{
		gameStartGame.setEnabled(false);
		gameHumanButton.setEnabled(false);
		gameAIButton.setEnabled(false);
		gameAISlider.setEnabled(true);
		gameName.setEnabled(false);
		gameEndGame.setEnabled(true);
		hintButton.setEnabled(true);
		connectionButton.setEnabled(false);
		connectionIPText.setEnabled(false);
		connectionPortText.setEnabled(false);
		for (int i = 0; i < board.length; i++) {
			board[i].setEnabled(true);
			board[i].setIcon(EMPTYFIELD);
		}
	}
	
	/**
	 * Looks up if it is a human player or the articifical intelligence playing
	 * @return
	 */
	public boolean isHumanPlayer()	{
		return gameHumanButton.isSelected();
	}
}
