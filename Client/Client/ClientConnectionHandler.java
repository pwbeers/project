package Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
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
	private BufferedReader in;
	private PrintWriter out;

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
		//TODO hier doen???
		try {
			out = new PrintWriter(socket.getOutputStream(),true);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * Reads a received command and passes this on to the ClientController.
	 * @param line is the message received from a server
	 */
	//@ requires line != null;
	public void commandReader(String line) throws Error	{
		System.out.println(line);
		Scanner scan = new Scanner(line);
		//TODO afvangen van geen lege command.next()
		ArrayList<String> command = new ArrayList<String>();
		while(scan.hasNext())	{
			command.add(scan.next());
		}
		scan.close();
		switch(command.get(0))	{
			case "EXTENSIONS": 
				String[] extensions = new String[command.size()-1];
				for (int i = 1; i < command.size(); i++) {
					if(command.get(i).equals("NONE") || command.get(i).equals("CHAT") || command.get(i).equals("CHALLENGE") || command.get(i).equals("LEADERBOARD"))	{
						extensions[i - 1] = command.get(i);
					}
					else	{
						throw new Error("Arguments after EXTENSIONS are illegal");
					}
				}
				controller.addServerExtensions(extensions);
				//TODO reageer door eigen extensies te versturen
				break;
			case "GAME": 
				if(command.size() == 2 && !command.get(1).equals(""))	{
					controller.startGame(command.get(1));
				}
				else	{
					throw new Error("Argument after GAME is illegal");
				}
				break;
			case "TURN": 
				controller.onTurn();
				break;
			case "MOVEUPDATE": 
				if(command.size() == 3 && (command.get(1).equals(getName()) || command.get(1).equals(controller.getOpponent())) && command.get(2).matches("[0-6]"))	{
					String[] arguments = new String[2];
					arguments[0] = command.get(1);
					arguments[1] = command.get(2);
					controller.serverMove(arguments);
				}
				else	{
					throw new Error("Argument after GAME is illegal");
				}
				break;
			case "GAMEEND": 
				if(command.size() == 3 && (command.get(1).equals(getName()) || command.get(1).equals(controller.getOpponent())) && command.get(2).matches("[0-6]"))	{
					String[] arguments = new String[2];
					arguments[0] = command.get(1);
					arguments[1] = command.get(2);
					controller.gameEnd(arguments);
				}
				else	{
					throw new Error("Argument after GAME is illegal");
				}
				break;
			case "ERROR": 
				//TODO netjes afhandelen van disconnect door server
				String error = command.get(1);
				for (int i = 2; i < command.size(); i++) {
					error = error + " " + command.get(i);
				}
				controller.error(error);
				break;
			case "DEBUG": 
				if(command.size() > 1)	{
					String debug = command.get(1);
					for (int i = 2; i < command.size(); i++) {
						debug = debug + " " + command.get(i);
					}
					controller.error(debug);
				}
				break;
			case "LEADERBOARD": 
				String[] leaderboard = new String[command.size()-1];
				for (int i = 0; i < command.size() - 1; i++) {
					leaderboard[i] = command.get(i+1);
				}
				controller.leaderboard(leaderboard);
				break;
			case "MESSAGE": 
				String message = "";
				for (int i = 1; i < command.size(); i++) {
					message = message + " " + command.get(i);
				}
				controller.message(message);
				break;
			case "BROADCAST": 
				String broadcast = "";
				for (int i = 1; i < command.size(); i++) {
					broadcast = broadcast + " " + command.get(i);
				}
				controller.broadcast(broadcast);
				break;
			case "PLAYERUPDATE": 
				String[] update = new String[command.size()-1];
				for (int i = 0; i < command.size() - 1; i++) {
					update[i] = command.get(i+1);
				}
				controller.update(update);
				break;
			case "CHALLENGE": 
				if(command.size() == 2)	{
					String challengePlayer = command.get(1);
					controller.challenged(challengePlayer);
				}
				else	{
					throw new Error("Argument after CHALLENGE is illegal");
				}
				break;
			case "CHALLENGERESP": 
				//Later
				break;
			case "DISCONNECTED": 
				//TODO Ends a game if being played with the player
				//TODO Removes the player out of the list
				break;
			case "AUTHENTICATE": 
				controller.authenticate();
				break;
			case "JOIN": 
				//TODO JOIN N en JOIN Y toepassen
				break;	
			default	:
				throw new Error("No such command, illegal command has been send");
		}
		
	}

	/**
	 * Sends a message from the client to a server with the given message as the message.
	 * @param message is line of text to be send to the server
	 */
	//@ requires message != null;
	public void sendMessage(String message) {
		out.println(message);
	}
	
	private void closeConnection(String message)	{
		sendMessage("DEBUG " + message);
		controller.connectionClosed(message);
		out.close();
		try {
			in.close();
			socket.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void run()	{
		while(true)	{
			try {
				in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
				String message = in.readLine();
				commandReader(message);
			} catch (Error e)	{
				closeConnection(e.getMessage());
			} catch (IOException e) {
				//TODO exception netjes afvangen, server heeft de verbinding verbroken
			}
		}
	}

}