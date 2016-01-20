package qwirkle;

import java.io.IOException;

import ss.week5.tictactoe.ComputerPlayer;
import ss.week5.tictactoe.HumanPlayer;
import ss.week5.tictactoe.Mark;
import ss.week5.tictactoe.Strategy;
import ui.*;
import networking.*;

public class Qwirkle {
	
	private static UI ui;
	private Board board;
	private Bag bag;
	private Player[] players;
	
	public Qwirkle() {
		board = new Board(); // I think???
		//bag = new Bag(); Singleplayer only???
	}

	/**
	 * Starts the game.
	 * @param args
	 */
	public static void main(String[] args) {
		Qwirkle game = new Qwirkle();
		ui = new TUI(game);
		ui.startup();
		// TODO Auto-generated method stub 

	}
	
	/**
	 * Starts a singleplayer game.
	 */
	public void startSingleplayer() {
		bag = new Bag();
		String[] playersA = ui.getPlayers();
		for (int i = 0; i < playersA.length; i++) {
			if (playersA[i].startsWith("AI ")) {
				String strat = "qwirkle." 
          			  + playersA[i].replaceFirst("AI ", "") + "Strategy";
          	try {
          		Class.forName(strat);
          		Behaviour behaviour = (Behaviour) Class.forName(strat).newInstance();
              	players[i] = new AIPlayer(behaviour);
          	} catch (ClassNotFoundException e) {
          		System.out.println("Strategy doesn't exist.");
          	} catch (InstantiationException | IllegalAccessException e) {
          		System.out.println("Error with class acces");
				} 
			} else {
				players[i] = new HumanPlayer(playersA[i]);
			}
		}
			
			
			//players[i] = new HumanPlayer(playersA[i]);
		}
		// TODO implement
	}
	
	/**
	 * Starts a multiplayer game.
	 */
	public void startMultiplayer() {
		try {
			Client client = new Client(ui.getHost(), ui.getPort());
			
			//------------------------------------------------------------------------------
			//For testing purposes only
			client.sendMessage("QUIT");
			//------------------------------------------------------------------------------
					
			
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// TODO implement
		
		
	}

}
