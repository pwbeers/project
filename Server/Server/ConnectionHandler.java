package Server;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Scanner;

import Error.Error;

/**
 * Manages a single TCP connection with a Player. It handles some of the logic
 * for client to client-user communication and  sends the commands through to 
 * the ServerController and GameController with which it doesn’t do anything itself. 
 * @author Stephan
 */
public class ConnectionHandler extends Thread {

	// ------------------ Instance variables ----------------
	private ServerController controller; //the current ServerController
	private Socket socket; //the socket of this particular connection
	private String nickName; //the nickname of the player connected to this handler
	private GameController gameController; //the gameController the connection is in, if there is one
	private String extensions; //the extensions supported by the Server
	
	private PrintWriter writer; //printwriter for writing back over the socket to the client
	private BufferedReader bufferedReader; //Bufferedreader for reading from the socket
	private Scanner scanner; //scanner for the switch reading the commands in a single line
	private String newLine; //a new line recieved on th esocket
	
	private boolean listenForCommands; //Flag for the while loop in run(), if this is set to false the class stops handling the communication and frees up its assets

	// ------------------ Constructor ------------------------
	/**
	 * Creates a BufferedReader connected to the inputstream of this socket.
	 * Creates a PrintWriter for writing to the Client.
	 * Retrieves the supported extensions from servercontroller
	 * Sends EXTENSIONS command to start communication
	 * Sets the Flag for the run() method to true
	 * Sets the gameController to null to allow checking if a MOVE command is correct
	 * Sets nickName to nickName Unknown
	 * @param controller //the current ServerController
	 * @param socket /the socket created by the ServerController
	 */
	public ConnectionHandler(ServerController newController, Socket newSocket) {
		controller = newController;
		socket = newSocket;
		extensions = controller.getExtensions();
		listenForCommands = true;
		gameController = null;
		nickName = "nickName unknown";
		
		//Create a Buffered Read and a PrintWriter
		try {
			bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
			writer = new PrintWriter(socket.getOutputStream(), true);
			
			//The client is waiting for the AMULET EXTENSIONS command to begin communication
			writeToClient("EXTENSIONS " + extensions);
		} catch (IOException e) {
			controller.writeToGUI("player" + nickName +" is being kicked");
			listenForCommands = false;
			//TODO handle this properly
			//TODO send error to error class
			/*getInPutStream throws an IOException if an I/O error occurs when creating 
			the input stream, the socket is closed, getOutPutStream throws one when creating
			the output stream or if the socket is not connected.*/
		}
		
	}

	// ------------------ Queries --------------------------
	/**
	 * Returns the current GameController if there is one
	 * @return the current Game Controller
	 */
	public GameController getGameController() {
		return gameController;
	}
	
	/**
	 * Returns the current NickName if there is one
	 * @return the current NickName
	 */
	public String getNickName() {
		return nickName;
	}
	
	public ServerController getController(){
		return controller;
	}
	// ------------------ Commands --------------------------
	/**
	 * Waits for a new line. When one is received sends it to the commandReader.
	 * Is only active when listenForCommands == true. If it is set to false the bufferedReader, 
	 * writer and socket are closed and the connection is removed from the ServerController
	 */
	public void run(){
		while (listenForCommands == true){
			try {
				//Wait for new Command.
				newLine = bufferedReader.readLine();
			}catch (IOException e) {
				//An I/O error occured in readLine() The thread is closed.
				listenForCommands = false;
				//TODO send error to error class
			}
			//Pass the newCommand to the commandReader.
			try {
			commandReader(newLine);
			}catch (Error commandError){
				//There was a violation of the AMULET guidlines. The connection needs to be severed.
				controller.writeToGUI("To [" + nickName + "]: " + commandError.getMessage());
				writeToClient(commandError.getMessage());
				listenForCommands = false;
			}
		}
		
		controller.writeToGUI("Player [" + nickName +"] is being kicked");
		//TODO do this properly
		/*if listenForCommands has been set to false the thread needs to be closed
		and the resources must be freed*/
		
		if (gameController != null){
			gameController.endGame();
			gameController = null;
		}
		
		controller.removeConnectionHandler(this);		
		
		try{
			bufferedReader.close();
			writer.close();
			socket.close();
		}catch (IOException e){
			//TODO send error to error class
			controller.writeToGUI("ERROR[FFFF00]: There was  a read(), ready(), mark(), reset(),"
					+ " or skip() invocation on a closed BufferedReader or an I/O error has occured"
					+ " while closing the socket in the  thread of "+ nickName);
			System.out.println("ERROR[FFFF00]: There was  a read(), ready(), mark(), reset(),"
					+ " or skip() invocation on a closed BufferedReader or an I/O error has occured"
					+ " while closing the socket in the  thread of "+ nickName);
		}
	}
	/**
	 * Sets the GameController attribute for referencing when in a game
	 * @param newGameController the current GameController
	 */
	public void setGameController(GameController newGameController) {
		gameController = newGameController;
	}

	/**
	 * Sets the NickName for this Player
	 * @param name the NickName
	 */
	public void setNickName(String name) {
		nickName = name;
	}
	
	/** Send a message to the client
	 * @param message the messeage to be send
	 */
	public void writeToClient(String message){
		writer.println(message + "\n");
		controller.writeToGUI("To [" + nickName + "]: " + message); //TODO remove this
	}
	
	/**
	 * Switches all the commands in the AMULET protocol to the right parts of the system using a switch
	 * 
	 * @param newCommand a new Command which has been detected
	 */
	public void commandReader(String newLine) throws Error{
		controller.writeToGUI(newLine);
		
		try {
			scanner = new Scanner(newLine);	
		} catch (NullPointerException e){
			throw new Error("ERROR COMMAND IS EMPTY YOU WILL BE TERMINATED ");
		}
		
		String command;
		ArrayList <String> arguments = new ArrayList<String>();		
		
		//Separate the AMULET command from the arguments and put them in an ArrayList.
		command = scanner.next();		
		controller.writeToGUI(command); //TODO remoive this
		
		int i = 0;
		while(scanner.hasNext()){			
			arguments.add(scanner.next());
			i++;
		}
		
		switch (command){
		case "EXTENSIONS":
			//The ServerController handles the logic for matching which extensions can be used 
			controller.matchExtensions(arguments, this);
			break;
		case "JOINREQ":
			//We now now the NickName of this client. This should also be be made known to the ServerController
			//TODO check if player is a security player and communicate this to ServerController
			nickName = arguments.get(0);
			controller.addConnectionHandler(nickName, this);
			if (!nickName.startsWith("Player_")){
				controller.addSecurityPlayer(this);
			}

			break;
		case "MOVE":
			/*We pass any Move commands through to the GameController.
			If there is no gameController the client is kicked
			GameController throws his own exceptions to kick the user*/
			if(gameController == null){
				throw new Error("ERROR YOU ARE NOT IN A GAME. YOUR CONNECTION WILL NOW BE TERMINATED");
			}else {
				//If newMove cannot be completed an error wil be thrown which is handled in the run method
				try {
					gameController.newMove(this, arguments);
				} catch (Error e){
					//move was wrong
				}
				break;
			}	
		case "DEBUG":
			controller.writeToGUI("[" +nickName+"]: DEBUG" + arguments);
			break;
		default:
			//Any other commands are illegal in AMULET and the connection will be severed
			throw new Error("ERROR COMMAND NOT RECOGNIZED. YOUR CONNECTION WILL NOW BE TERMINATED");
		}
	}
}