package View;

import javax.swing.JFrame;
import javax.swing.JPanel;
import java.awt.FlowLayout;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.JButton;
import javax.swing.SwingConstants;
import java.awt.BorderLayout;
import java.awt.Color;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Observable;
import java.awt.event.ActionListener;

import javax.swing.JTextArea;
import javax.swing.JScrollPane;
import javax.swing.text.DefaultCaret;


/**
 * A ServerGui that shows a graphical interface for the Server/user to use. Displays all the communication that takes place
 * and displays lists of connected clients and current games
 * @author Stephan
 */

public class ServerGui implements View {
	// ------------------ Instance variables ----------------

	private ActionListener controller; //The ServerController of the Server
	
	private JFrame serverFrame; //The Frame of the Gui
	private JTextField portTextField; //The TextField that contains the portnumber
	private JTextField manualInTextField; //the TextField for sending manual commands	
	private JTextArea mainTextArea; //The Text Area where all the communication is printed
	private JTextArea activePlayersTextArea; // The TextArea where the list of ActivePlayers is displayed
	private JTextArea currentGamesTextArea; //The TextArea where the list of CurrentGames is displayed
	private String inet; //The string that contains the IP address of the system

	// ------------------ Constructor ------------------------

	/**
	 * Initalizes the Gui and controller attribute.
	 * Finds the value for the ip address.
	 * Repaints and revalidates the GUI for proper displayment
	 * @param newController the ServerController that will handle the ActionEvents
	 */
	public ServerGui(ActionListener newController) {
		controller = newController;
		
		try {
			inet = InetAddress.getLocalHost().getHostAddress();
		} catch (UnknownHostException e) {
			inet = "000.00.00.0";
		}
		
		initialize();
		serverFrame.repaint();
		serverFrame.revalidate();
	}
	// ------------------ Queries --------------------------
	
	/**
	 * Returns the text in the textfield for the portnumber
	 * @return the text in the <code>portTextField</code>
	 */
	public String getPortNumber() {
		return portTextField.getText();
 
	}
	
	// ------------------ Commands --------------------------

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
		
		JScrollPane textScrollPane = new JScrollPane();
		textScrollPane.setBounds(10, 67, 500, 418);
		serverFrame.getContentPane().add(textScrollPane);
		
		JPanel textPanel = new JPanel();
		textScrollPane.setViewportView(textPanel);
		textPanel.setLayout(new BorderLayout(0, 0));
		

		mainTextArea = new JTextArea();
		mainTextArea.setLineWrap(true);
		textPanel.add(mainTextArea, BorderLayout.CENTER);
				
		DefaultCaret textCaret = (DefaultCaret)mainTextArea.getCaret();
		textCaret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);
				
		JPanel manualPanel = new JPanel();
		manualPanel.setBounds(10, 484, 500, 33);
		serverFrame.getContentPane().add(manualPanel);
				
		manualInTextField = new JTextField();
		manualInTextField.setEnabled(false);
		manualInTextField.setEditable(false);
		manualPanel.add(manualInTextField);
		manualInTextField.setColumns(30);
				
		JButton btnNewButton = new JButton("Send In");
		btnNewButton.setEnabled(false);
		manualPanel.add(btnNewButton);
		
		JPanel playerPanel = new JPanel();
		playerPanel.setBounds(529, 9, 345, 180);
		serverFrame.getContentPane().add(playerPanel);
		playerPanel.setLayout(null);
		
		JPanel playerLabelPanel = new JPanel();
		playerLabelPanel.setBounds(0, 0, 344, 23);
		playerPanel.add(playerLabelPanel);
		playerLabelPanel.setLayout(new BorderLayout(0, 0));
		
		JLabel activePlayersLabel = new JLabel("Active Players:");
		playerLabelPanel.add(activePlayersLabel, BorderLayout.NORTH);
		activePlayersLabel.setHorizontalAlignment(SwingConstants.CENTER);
		
		JScrollPane playersScrollPane = new JScrollPane();
		playersScrollPane.setBounds(0, 21, 345, 159);
		playerPanel.add(playersScrollPane);
		
		JPanel currentPlayerPanel = new JPanel();
		playersScrollPane.setViewportView(currentPlayerPanel);
		currentPlayerPanel.setLayout(new BorderLayout(0, 0));
		
		
		activePlayersTextArea = new JTextArea();
		activePlayersTextArea.setEditable(false);
		activePlayersTextArea.setLineWrap(true);
		currentPlayerPanel.add(activePlayersTextArea, BorderLayout.CENTER);
		
		DefaultCaret playerCaret = (DefaultCaret)activePlayersTextArea.getCaret();
		playerCaret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);
		
		JPanel gamePanel = new JPanel();
		gamePanel.setBounds(530, 236, 344, 180);
		serverFrame.getContentPane().add(gamePanel);
		gamePanel.setLayout(null);
		
		JPanel gameLabelPanel = new JPanel();
		gameLabelPanel.setBounds(0, 0, 342, 22);
		gamePanel.add(gameLabelPanel);
		gameLabelPanel.setLayout(null);
		
		JLabel currentGameLabel = new JLabel("Current Games:");
		currentGameLabel.setBounds(0, 0, 342, 14);
		gameLabelPanel.add(currentGameLabel);
		currentGameLabel.setHorizontalAlignment(SwingConstants.CENTER);
		
		JScrollPane currentGamesScrollPane = new JScrollPane();
		currentGamesScrollPane.setBounds(-2, 21, 344, 159);
		gamePanel.add(currentGamesScrollPane);
				
		JPanel currentGamePanel = new JPanel();
		currentGamesScrollPane.setViewportView(currentGamePanel);
		currentGamePanel.setLayout(new BorderLayout(0, 0));
				
		currentGamesTextArea = new JTextArea();
		currentGamesTextArea.setEditable(false);
		currentGamesTextArea.setLineWrap(true);
		currentGamePanel.add(currentGamesTextArea, BorderLayout.CENTER);
		
		DefaultCaret gameCaret = (DefaultCaret)currentGamesTextArea.getCaret();
		gameCaret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);

		
		JButton leaderBoardButton = new JButton("Leaderboard");
		leaderBoardButton.setEnabled(false);
		leaderBoardButton.addActionListener(controller);
		leaderBoardButton.setBounds(633, 494, 156, 23);
		serverFrame.getContentPane().add(leaderBoardButton);
		
		JPanel connectionsPanel = new JPanel();
		connectionsPanel.setBounds(10, 10, 500, 56);
		serverFrame.getContentPane().add(connectionsPanel);
		connectionsPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		
		JLabel portLabel = new JLabel("port:");
		connectionsPanel.add(portLabel);
		
		portTextField = new JTextField();
		portTextField.setText("2220");
		connectionsPanel.add(portTextField);
		portTextField.setColumns(10);
		
		JLabel adressLabel = new JLabel("Ip address:");
		connectionsPanel.add(adressLabel);
		
		JLabel addressValueLabel = new JLabel(inet);
		addressValueLabel.setHorizontalAlignment(SwingConstants.CENTER);
		connectionsPanel.add(addressValueLabel);
		
		JButton startButton = new JButton("Start");
		connectionsPanel.add(startButton);
		startButton.addActionListener(controller);
		
		JButton closeButton = new JButton("Close");
		connectionsPanel.add(closeButton);
		closeButton.addActionListener(controller);
		
		JButton refreshActivePlayersButton = new JButton("Refresh Players");
		refreshActivePlayersButton.setBounds(630, 200, 155, 23);
		serverFrame.getContentPane().add(refreshActivePlayersButton);
		refreshActivePlayersButton.addActionListener(controller);
		
		JButton refreshGamesButton = new JButton("Refresh Games");
		refreshGamesButton.setBounds(633, 441, 156, 23);
		serverFrame.getContentPane().add(refreshGamesButton);
		refreshGamesButton.addActionListener(controller);
	
	}
	
	/**
	 * Prints a message on the maintext area
	 * @param message the message to be created
	 */
	public synchronized void printText(String message){
		mainTextArea.append(message + "\n");		
	}
	
	/**
	 * Appends the ActivePlayers list
	 * @param player the player to be added
	 */
	public synchronized void appendActivePlayers(String player){
		activePlayersTextArea.append(player + "\n");
	}
	
	/**
	 * Appends the CurrentGames list
	 * @param game the game to be added
	 */
	public synchronized void appendCurrentGames(String game){
		currentGamesTextArea.append(game + "\n");	
	}
	
	/**
	 * Clears the ActivePlayers TextArea
	 */
	public synchronized void clearActivePlayers(){
		activePlayersTextArea.setText("refreshing...");
		activePlayersTextArea.setText("");
		
	}
	
	/**
	 * Clears the CurrentGames TextArea
	 */
	public synchronized void clearCurrentGames(){
		currentGamesTextArea.setText("refreshing...");
		currentGamesTextArea.setText("");
	}

	/**
	 * Unused method from the interface
	 */
	public void startScherm(){
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Unused method from the interface
	 */
	public void update(Observable arg0, Object arg1) {
		throw new UnsupportedOperationException();
	}


}