package qwirkle;

import java.io.IOException;

import ui.*;
import networking.*;

public class Qwirkle {
	
	private static UI ui;
	private Board board;
	
	public Qwirkle() {
		board = new Board(); // I think??
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
	
	public void startSingleplayer() {
		// TODO implement
	}
	
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
