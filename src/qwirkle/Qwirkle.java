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
		          		ui.showError(String.format("Strategy of player %d doesn't exist.", i + 1));
		          		player = ui.getPlayer(i);
		          	} catch (InstantiationException | IllegalAccessException e) {
		          		ui.showError(String.format("Error with class acces"));
					}
				} else {
					players.add(new HumanPlayer(player));
					break;
				}
			}
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
