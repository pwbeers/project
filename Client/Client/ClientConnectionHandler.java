package Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
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
		try {
			out = new PrintWriter(socket.getOutputStream(),true);
		} catch (IOException e) {
			closeConnection("problem with setting up an output connection to the server.");
		}
	}

	/**
	 * Reads a received command and passes this on to the ClientController.
	 * @param line is the message received from a server
	 */
	//@ requires line != null;
	public void commandReader(String line) throws Error	{
		//TODO verwijderen
		System.out.println("Server: " + line);
		Scanner scan = new Scanner(line);
		ArrayList<String> command = new ArrayList<String>();
		while(scan.hasNext())	{
			command.add(scan.next());
			}
		scan.close();
		if(!command.isEmpty())	{
			switch(command.get(0))	{
				case "EXTENSIONS": 
					List<String> extensions = new LinkedList<String>();
					for (int i = 1; i < command.size(); i++) {
						if(command.get(i).equals("NONE") || command.get(i).equals("CHAT") || command.get(i).equals("CHALLENGE") || command.get(i).equals("LEADERBOARD"))	{
							extensions.add(command.get(i));
						}
						else	{
							throw new Error("Arguments after EXTENSIONS are illegal: " + line);
						}
					}
					controller.addServerExtensions(extensions);
					break;
				case "GAME": 
					if(command.size() == 2 && !command.get(1).equals(""))	{
						controller.startGame(command.get(1));
					}
					else	{
						throw new Error("Argument after GAME is illegal: " + line);
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
						throw new Error("Argument after MOVEUPDATE is illegal: " + line);
					}
					break;
				case "GAMEEND": 
					if(command.size() == 3 && (command.get(1).equals(getName()) || command.get(1).equals(controller.getOpponent())) && command.get(2).matches("[0-6]"))	{
						String[] arguments = new String[2];
						arguments[0] = command.get(1);
						arguments[1] = command.get(2);
						controller.gameEnd(arguments);
					}
					else if(command.size() == 2 && command.get(1).equals("DRAW"))	{
						String[] argument = new String[1];
						argument[0] = command.get(1);
						controller.gameEnd(argument);
					}
					else if(command.size() == 1)	{
						controller.gameEnd(null);
					}
					else	{
						throw new Error("Argument after GAMEEND is illegal: " + line);
					}
					break;
				case "ERROR": 
					String error = command.get(1);
					for (int i = 2; i < command.size(); i++) {
						error = error + " " + command.get(i);
					}
					controller.guiMessage("Server error message: " + error);
					break;
				case "DEBUG": 
					if(command.size() > 1)	{
						String theBug = command.get(1);
						for (int i = 2; i < command.size(); i++) {
							theBug = theBug + " " + command.get(i);
						}
						controller.guiMessage("DEBUG: " + theBug);
					}
					break;
				case "LEADERBOARD": 
					throw new Error("The server was told that LEADERBOARD wasn't supported: " + line);
				case "MESSAGE": 
					if(command.size() > 1)	{
						String player = command.get(1);
						String message = "";
						for (int i = 2; i < command.size(); i++) {
							message = message + " " + command.get(i);
						}
						controller.message(player + "(personal): " + message);
					}
					break;
				case "BROADCAST": 
					if(command.size() > 1)	{
						String player = command.get(1);
						String broadcast = "";
						for (int i = 2; i < command.size(); i++) {
							broadcast = broadcast + " " + command.get(i);
						}
						controller.message(player + "(broadcast): " + broadcast);
					}
					break;
				case "PLAYERUPDATE": 
					if(command.size() > 1)	{
						String[] update = new String[command.size()-1];
						for (int i = 0; i < command.size() - 1; i++) {
							update[i] = command.get(i+1);
						}
						controller.update(update);
					}
					else	{
						controller.update(null);
					}
					break;
				case "CHALLENGE": 
					//TODO verder implementeren
					if(command.size() == 2)	{
						String challengePlayer = command.get(1);
						controller.challenged(challengePlayer);
					}
					else	{
						throw new Error("Argument after CHALLENGE is illegal: " + line);
					}
					break;
				case "CHALLENGERESP": 
					//TODO verder implementeren
					if(command.size() == 2)	{
						String responce = command.get(1);
						controller.message(responce);
					}
					else	{
						throw new Error("The responce on the challenge was missing: " + line);
					}
					break;
				case "DISCONNECTED": 
					//TODO onderdeel voor chat en challenge functie
					if(command.size() == 2)	{
						String disconnectedPlayer = command.get(1);
						controller.otherPlayerDisconnected(disconnectedPlayer);
					}
					else	{
						throw new Error("The player in the disconnect wasn't specified: " + line);
					}
					break;
				case "AUTHENTICATE": 
					throw new Error("The server was told that AUTHENTICATE wasn't supported: " + line);
				case "JOIN": 
					throw new Error("The server was told that JOIN wasn't supported: " + line);
				default	:
					throw new Error("No such command, illegal command has been send: " + line);
			}
		}
		else	{
			throw new Error("A command was not given by the server");
		}
	}

	/**
	 * Sends a message from the client to a server with the given message as the message.
	 * @param message is line of text to be send to the server
	 */
	//@ requires message != null;
	public void sendMessage(String message) {
		//TODO verwijderen
		System.out.println("Client: " + message);
		out.println(message);
	}
	
	public void closeConnection(String message)	{
		try {
			sendMessage("DEBUG " + message);
			out.close();
			in.close();
			socket.close();
		} catch (IOException e) {
			//Nothing is to be done here.
		}
		controller.connectionClosed(message);
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
				String message = "The connection has been broken by the server";
				out.close();
				controller.connectionClosed(message);
			} 
		}
	}

}