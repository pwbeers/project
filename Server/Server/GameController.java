package Server;

import java.util.ArrayList;
import java.util.List;

import Model.Game;
import Model.Model;
import Error.Error;

public class GameController {

	// ------------------ Instance variables ----------------
	private ServerController controller;
	private Model game; //the game that this controller uses
	private ConnectionHandler player1; //The ConnectionHandler object of Player 1
	private ConnectionHandler player2; //The ConnectionHandler object of Player 2
	private final int PLAYER1 = 1; //The Integer representation of Player 1
	private final int PLAYER2 = 2; //The Integer representation of Player 2

	// ------------------ Constructor ------------------------
	/**
	 * Starts a new Game with two players.
	 * Fills the Instance Variables
	 * @param player1
	 * @param player2
	 */
	
	public GameController(ConnectionHandler newPlayer1, ConnectionHandler newPlayer2) {
		controller = newPlayer1.getController();
		player1 = newPlayer1;
		player2 = newPlayer2;
		startGame();
	}
	
	// ------------------ Queries --------------------------
	/**
	 * Returns the Integer representation of the ConnectionHandler Object
	 * because the Game class uses integers.
	 * @param player the player to be converted
	 * @return <code> 1 || 2 </code>
	 */
	public int convertHandlerToInt(ConnectionHandler player){
		if(player == player1){
			return PLAYER1;
		}else {
			return PLAYER2;
		}
	}
	
	public List<ConnectionHandler> getPlayers(){
		List<ConnectionHandler> players = new ArrayList<ConnectionHandler>();
		players.add(player1);
		players.add(player2);
		return players;
	}
	// ------------------ Commands --------------------------
	/**
	 * Creates a new Game object
	 * It sends the AMULET GAME commands to the players and the TURN command to player1
	 */
	public void startGame() {
		game = new Game();
		
		player1.writeToClient("GAME " + player2.getNickName());
		player2.writeToClient("GAME " + player1.getNickName());
		
		player1.writeToClient("TURN");
		
		//TODO add turn waitingtime guard.
		}

	/**
	 * Handles the AMULET protocol for doing a move
	 * If the player isn't on turn or the move is illegal
	 * It pulls the integer of the column of the move from the AMULET arguments list it is handed by 
	 * the ConnectionHandler that calls the method and parses it to a String. It uses the convertHandlertoInt method 
	 * to convert the ConnectionHandler reference into an integer representation of the player. 
	 * This is needed because the Game Model uses integers 1 & 2 to keep track of players and not 
	 * ConnectionHandler references.
	 * 
	 * @param connectionHandler
	 * @param arguments
	 */
	//TODO handle game ending here
	public void newMove(ConnectionHandler playerHandler, ArrayList<String> arguments) {

		//Isolate the String of the column of the move
		String columnString = arguments.get(0);
		System.out.println("ColumnString from " + playerHandler.getNickName() + " :" + columnString);
		//parse from String to Integer
		int column = Integer.parseInt(columnString);
		System.out.println("ColumnInt from " + playerHandler.getNickName() + " :" + column);
		
		//Convert the handler object to the Integer representation
		int player = convertHandlerToInt(playerHandler);
		System.out.println("Player on turn :" + player);
		
		
		//Check if player is on turn
		if (game.onTurn(player) == false){
			controller.writeToGUI("Player [" + playerHandler.getNickName() + "] has send a MOVE command while"
					+ " they were not on turn. Their Game will be ended");
			playerHandler.writeToClient("ERROR YOU ARE NOT ON TURN. THE CONNECTION WILL BE TERMINATED.");
			endGame(playerHandler);
		}

		//Check if move is legal
		if(column > 6 || column < 0 || game.isLegalMove(column) == false){
			controller.writeToGUI("Player [" + playerHandler.getNickName() + "] has send a MOVE command while"
					+ " they were not on turn. Their Game will be ended");
			playerHandler.writeToClient("ERROR ILLEGAL MOVE. THE CONNECTION WILL BE TERMINATED.");
			endGame(playerHandler);
		}
		
		/*There are three possibilities that can occur, either:
		 * 0: the game doesn't end and the next player needs to do a move
		 * 1: this was a winning move
		 * 2: there is no winner
		 */
		switch(game.doMove(column, player)){
		case 0: //The Game continues. The players need to be notified of a new move 
			//and a new turn needs to be assigned
			broadcastToPlayers("MOVEUPDATE " + playerHandler.getNickName() + " " +columnString);
			controller.writeToGUI("MOVEUPDATE " + playerHandler.getNickName() + " " +columnString);
			System.out.println("MOVEUPDATE " + playerHandler.getNickName() + " " +columnString);
			assignTurn(player);
			break;
		case 1:
			//send gameend to both players with nickname of playerHandler
			broadcastToPlayers("GAMEEND " + playerHandler.getNickName() + " " + column);
			controller.writeToGUI("GAMEEND " + playerHandler.getNickName() + " " + column);
			System.out.println("GAMEEND " + playerHandler.getNickName() + " " + column);
			break;
		case 2:
			//send gameEnd to bothplayers with no nicjname
			broadcastToPlayers("GAMEEND DRAW");
			controller.writeToGUI("GAMEEND DRAW");
			System.out.println("GAMEEND DRAW");
			break;
		
		}
	}

	/**
	 * Sends the AMULET TURN command to the player that is not the player that is represented by
	 * the player parameter
	 * @param player the player that was on turn, but is no longer
	 */
	private void assignTurn(int player) {
		if(player == 1){
			player2.writeToClient("TURN");
			controller.writeToGUI(player2.getNickName() + " is on turn");
			System.out.println(player2.getNickName() + " is on turn");
		}else {
			player1.writeToClient("TURN");
			controller.writeToGUI(player1.getNickName() + " is on turn");
			System.out.println(player1.getNickName() + " is on turn");
		}
	}

	/**
	 * Send an AMULET command to both the players of this GameController.
	 * @param broadcast the message of the broadcast
	 */
	private void broadcastToPlayers(String broadcast) {
		player1.writeToClient(broadcast);
		player2.writeToClient(broadcast);
	}
	
	public void endGame(ConnectionHandler clientToBeTerminated){
		//TODO Send endgame to both participants 
		broadcastToPlayers("GAMEEND");		
		/*The player that has been kicked isn't in the connections map. To kick him from the server all we need to do is
		not put him back into the connections map from the games map.*/

		if(player1 == clientToBeTerminated){
			player1.kick();
			controller.addConnectionHandler(player2.getNickName(), player2);
		}else {
			player2.kick();
			controller.addConnectionHandler(player1.getNickName(), player1);
		}
		controller.updateActivePlayers();
		controller.deleteGame(this);
	}

}