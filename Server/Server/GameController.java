package Server;

import java.util.ArrayList;

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
	// ------------------ Commands --------------------------
	/**
	 * Creates a new Game object
	 * Sends AMULET TURN command to player1
	 */
	public void startGame() {
		game = new Game();
		player1.writeToClient("GAME " + player2.getNickName());
		controller.writeToGUI("GAME " + player2.getNickName());
		player2.writeToClient("GAME " + player1.getNickName());
		controller.writeToGUI("GAME " + player1.getNickName());
		player1.writeToClient("TURN");
		controller.writeToGUI("TURN " + player1.getNickName());
		}

	/**
	 * Handles the AMULET protocol for doing a move
	 * If the player isn't on turn or the move is illegal
	 * @param connectionHandler
	 * @param arguments
	 */
	public void newMove(ConnectionHandler playerHandler, ArrayList<String> arguments) throws Error {
		controller.writeToGUI("Move recieved from " + playerHandler.getNickName());

		String columnString = arguments.get(0);
		//Convert from String to Integer
		int column = Integer.parseInt(columnString);
		
		//Convert the handler object to the Integer representation
		int player = convertHandlerToInt(playerHandler);
		
		//Check if player is on turn
		if (game.onTurn(player) == false){
			broadcastToPlayers("GAMEEND");
			controller.writeToGUI("GAMEEND");
			throw new Error("ERROR YOU ARE NOT ON TURN. THE CONNECTION WILL BE TERMINATED.");
		}

		//Check if move is legal
		if(game.isLegalMove(column) == false){
			broadcastToPlayers("GAMEEND");
			controller.writeToGUI("GAMEEND"); //TODO remove this
			throw new Error("ERROR ILLEGAL MOVE. THE CONNECTION WILL BE TERMINATED.");
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
			assignTurn(player);
			break;
		case 1:
			//send gameend to both players with nickname of playerHandler
			broadcastToPlayers("GAMEEND " + playerHandler.getNickName());
			controller.writeToGUI("GAMEEND " + playerHandler.getNickName());
			break;
		case 2:
			//send gameEnd to bothplayers with no nicjname
			broadcastToPlayers("GAMEEND DRAW");
			controller.writeToGUI("GAMEEND DRAW");
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
			System.out.println(player2.getNickName() + " is on turn");
		}else {
			player1.writeToClient("TURN");
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

}