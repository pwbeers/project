package Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Scanner;

/**
 * Starts and keeps a connection running with a server and passes messages 
 * on over this connection.
 * @author peter
 */
public class ClientConnectionHandler extends Thread {

	private /*@ spec_public @*/ ClientController controller;
	private /*@ spec_public @*/ Socket socket;

	/*@public invariant controller != null; @*/ //class invariant
	/*@public invariant socket != null; @*/ //class invariant
	
	/**
	 * Makes a new ClientConnectionHandler on the given socket. Also saves
	 * the ClientController that is given. 
	 * @param socket is a socket on which the connection is kept
	 * @param controller is used to pass on messages from the server to the client
	 */
	//@ requires socket != null && controller != null;
	//@ ensures this.controller == controller && this.socket == socket;
	public ClientConnectionHandler(Socket socket, ClientController controller) {
		this.socket = socket;
		this.controller = controller;
	}

	/**
	 * Reads a received command and passes this on to the ClientController.
	 * @param line is the message received from a server
	 */
	//@ requires line != null;
	public void commandReader(String line) {
		Scanner scan = new Scanner(line);
		//TODO afvangen van geen lege command.next()
		ArrayList<String> command = new ArrayList<String>();
		while(scan.hasNext())	{
			command.add(scan.next());
		}
		switch(command.get(0))	{
			case "EXTENSIONS": 
				//TODO fouten in extensies afhandelen
				String[] extensions = new String[command.size()-1];
				for (int i = 1; i < command.size(); i++) {
					
					extensions[i - 1] = command.get(i);
				}
				controller.addServerExtensions(extensions);
				break;
			case "GAME": 
				//start game
				break;
			case "TURN": 
				
				break;
			case "MOVEUPDATE": 
				
				break;
			case "GAMEEND": 
				
				break;
			case "ERROR": 
				
				break;
			case "DEBUG": 
				
				break;
			case "LEADERBOARD": 
				//Later
				break;
			case "MESSAGE": 
				//Later
				break;
			case "BROADCAST": 
				//Later
				break;
			case "PLAYERUPDATE": 
				
				break;
			case "CHALLENGE": 
				//Later
				break;
			case "CHALLENGERESP": 
				//Later
				break;
			case "DISCONNECTED": 
				//Later
				break;
			case "AUTHENTICATE": 
				//Later
				break;
			case "JOIN": 
				//Later
				break;	
			default	:
				
				break;	
		}
		
	}

	/**
	 * Sends a message from the client to a server with the given message as the message.
	 * @param message is line of text to be send to the server
	 */
	//@ requires message != null;
	public void sendMessage(String message) {
		throw new UnsupportedOperationException();
	}
	
	public void run()	{
		while(true)	{
			try {
				BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
				commandReader(in.readLine());
			} catch (IOException e) {
				//TODO exception netjes afvangen
			}
		}
	}

}