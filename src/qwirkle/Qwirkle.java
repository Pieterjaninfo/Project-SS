package qwirkle;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import ui.*;
import networking.*;

public class Qwirkle {
	
	private static UI ui;
	private Board board;
	private Bag bag;
	private List<Player> players = new ArrayList<Player>();
	
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
		addPlayers();
		// TODO give tiles to players
		// TODO determine first player from list of players.
		// TODO make first move
		// TODO let the next players make the move in the order of the list
		// while the game is not over.
	}

	/*
	 * Calls the UI to get the amount and names (and behaviours for AiPlayers).
	 */
	private void addPlayers() {
		int playerCount = ui.getPlayerCount();
		for (int i = 0; i < playerCount; i++) {
			String player = ui.getPlayer(i);
			while (true) {
				if (player.startsWith("AI ")) {
					String strat = "qwirkle." 
	          			  + player.replaceFirst("AI ", "") + "Behaviour";
					try {
		          		Class.forName(strat);
		          		Behaviour behaviour = (Behaviour) Class.forName(strat).newInstance();
		              	players.add(new AIPlayer(behaviour));
		              	break;
		          	} catch (ClassNotFoundException e) {
		          		ui.showMessage(String.format("Strategy of player %d doesn't exist.", 
		          				  i + 1));
		          		player = ui.getPlayer(i);
		          	} catch (InstantiationException | IllegalAccessException e) {
		          		ui.showMessage(String.format("Error with class acces"));
					}
				} else {
					players.add(new HumanPlayer(player, this));
					break;
				}
			}
		}
	}
	
	/**
	 * Starts a multiplayer game.
	 */
	public void startMultiplayer() {
		try {
			Client client = new Client(ui.getHost(), ui.getPort());
			client.begin(ui);
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
	
	public void sendMessage(String msg) {
		ui.showMessage(msg);
	}

}
