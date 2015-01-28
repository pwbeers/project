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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JTextArea;
import javax.swing.JScrollPane;
import javax.swing.text.DefaultCaret;


/**
 * A ServerGui that shows a graphical interface for the Server/user to use.
 * @author Stephan
 */

//TODO repaint
//TODO refresh buttons on lists

public class ServerGui implements View {

	private ActionListener controller;
	
	private JFrame serverFrame;
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
		
		try {
			inet = InetAddress.getLocalHost().getHostAddress();
		} catch (UnknownHostException e) {
			inet = "000.00.00.0";
		}
		
		initialize();
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
		
		JScrollPane scrollPane = new JScrollPane();
		scrollPane.setBounds(10, 67, 500, 450);
		serverFrame.getContentPane().add(scrollPane);
		
		JPanel textPanel = new JPanel();
		scrollPane.setViewportView(textPanel);
		textPanel.setLayout(new BorderLayout(0, 0));
		
		
		mainTextArea = new JTextArea();
		mainTextArea.setLineWrap(true);
		textPanel.add(mainTextArea, BorderLayout.CENTER);
		
		DefaultCaret caret = (DefaultCaret)mainTextArea.getCaret();
		caret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);

		
		JPanel manualPanel = new JPanel();
		textPanel.add(manualPanel, BorderLayout.SOUTH);
		
		textField = new JTextField();
		manualPanel.add(textField);
		textField.setColumns(30);
		
		JButton btnNewButton = new JButton("Send In");
		manualPanel.add(btnNewButton);
		
		JPanel currentPlayerPanel = new JPanel();
		currentPlayerPanel.setBounds(530, 11, 344, 180);
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
		currentGamePanel.setBounds(530, 236, 344, 180);
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
		leaderBoardButton.setEnabled(false);
		leaderBoardButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent arg0) {
			}
		});
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
		
		JButton refreshActivePlayersButton = new JButton("Refresh Players");
		refreshActivePlayersButton.setBounds(630, 200, 155, 23);
		serverFrame.getContentPane().add(refreshActivePlayersButton);
		
		JButton refreshGamesButton = new JButton("Refresh Games");
		refreshGamesButton.setBounds(633, 441, 156, 23);
		serverFrame.getContentPane().add(refreshGamesButton);
	
	}
	
	public synchronized void printText(String message){
		mainTextArea.append(message + "\n");		
	}
	
	public synchronized void appendActivePlayers(String player){
		activePlayersTextArea.append(player + "\n");
	}
	
	public synchronized void appendCurrentGames(String game){
		currentGamesTextArea.append(game + "\n");	
	}
	
	public synchronized void clearActivePlayers(){
		activePlayersTextArea.setText("refreshing...");
		activePlayersTextArea.setText("");
		
	}
	
	public synchronized void clearCurrentGames(){
		currentGamesTextArea.setText("refreshing...");
		activePlayersTextArea.setText("");
	}

	public void startScherm(){
		throw new UnsupportedOperationException();
	}
	
	public void update(Observable arg0, Object arg1) {
		throw new UnsupportedOperationException();
	}
}
