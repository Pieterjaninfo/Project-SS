package qwirkle;

import java.io.IOException;

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
			players[i] = new HumanPlayer(playersA[i]);
		}
		// TODO implement
	}
	
	/**
	 * Starts a multiplayer game.
	 */
	public void startMultiplayer() {
		try {
			Client client = new Client(ui.getHost(), ui.getPort());
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// TODO implement
	}

}
