package qwirkle;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import ui.*;
import networking.*;

public class Qwirkle implements Runnable{
	
	private static UI ui;
	private Board board;
	private Bag bag;
	private List<Player> players = new ArrayList<Player>();
	
	public Qwirkle() {
		board = new Board(); // I think???
		//bag = new Bag(); Singleplayer only???
	}

	/**
	 * Constructor used for the server that receives a list of clients and starts the game with these players.
	 * @param clients
	 */
	public Qwirkle(List<ClientHandler> clients) {
		for (ClientHandler client : clients) {
			players.add(new SocketPlayer(client.getName(), this));
		}
		board = new Board();
		bag = new Bag();
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
		// give tiles to players
		for (Player player : players) {
			player.setStartingHand(bag.giveStartingHand()); // TODO Add setStartinghand to Player
		}
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
		              	players.add(new AIPlayer(behaviour, board));
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
	 * Starts a multiplayer game for client.
	 */
	public void startMultiplayer() {
		try {
			Client client = new Client(ui.getHost(), ui.getPort());
			client.begin(ui);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void sendMessage(String msg) {
		ui.showMessage(msg);
	}

	/**
	 * Controller for the server game.
	 */
	@Override
	public void run() {
		for (Player player : players) {
			player.setStartingHand(bag.giveStartingHand());
		}
		
		// TODO determine first player...
		// TODO let first player make move
		// TODO let next player make move...etc...
		
		
		// TODO Auto-generated method stub
		
	}
	
	public Player determineFirstMove() {
		int startSize = 0;
		Player startingPlayer;
		for (Player player : players) {
			int playerStartSize = player.largestStartSize();
			if (playerStartSize > startSize) {
				startSize = playerStartSize;
				startingPlayer = player;
			}
		}
		return startingPlayer;
	}

}
