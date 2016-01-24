package qwirkle;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ui.*;
import networking.*;
import networking.Error;

public class Qwirkle implements Runnable{
	
	private static UI ui;
	private Board board;
	private Bag bag;
	private List<Player> players = new ArrayList<Player>();
	private Map<Player, ClientHandler> clientPlayerMap = new HashMap<Player, ClientHandler>();
	private List<ClientHandler> clients;
	private Player currentPlayer;
	private Boolean firstMove;
	
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
			Player player = new ServerSocketPlayer(client.getName(), this);
			players.add(player);
			clientPlayerMap.put(player, client);
		}
		this.clients = clients;
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
			player.setStartingHand(bag.giveStartingHand());
		}
		currentPlayer = determineFirstMove();
		do {
			ui.showBoard();
			ui.showHand(currentPlayer.getHand());
			currentPlayer.determineMove();

			currentPlayer = players.get((players.indexOf(currentPlayer) + 1) 
					  % players.size());			
			
		} while (true);
		// TODO while the game is not over.
	}

	/**
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
		currentPlayer = determineFirstMove();
		//clientPlayerMap.get(currentPlayer).gameBroadcast(clients, );
		firstMove = true;
		clientPlayerMap.get(currentPlayer).turn(clients, currentPlayer.getName());
		
		// TODO let next player make move...etc...
		
		
		// TODO Auto-generated method stub
		
	}
	
	public Player determineFirstMove() {
		int startSize = 0;
		Player startingPlayer = null;
		for (Player player : players) {
			int playerStartSize = player.largestStartSize();
			if (playerStartSize > startSize) {
				startSize = playerStartSize;
				startingPlayer = player;
			}
		}
		return startingPlayer;
	}
	
	public void makeMove() {
		currentPlayer.determineMove();
		firstMove = false;
	}
	/**
	 * Makes the trade move if the player can make the trade and if it isn't the first turn.
	 * @param handTiles String from protocol that contains the tilecodes of the tiles being traded.
	 */
	public void tradeMove(String handTiles) {
		if (firstMove) {
			clientPlayerMap.get(currentPlayer).error(Error.TRADE_FIRST_TURN);
		}
		String[] tileString = handTiles.split(" ");
		List<Tile> tileList = new ArrayList<Tile>();
		for (String a: tileString) {
			tileList.add(codeToTile(a));
		}		
		if (bag.canTradeTiles(tileList)) {
			bag.tradeTiles(tileList);
		} else {
			clientPlayerMap.get(currentPlayer).error(Error.MOVE_INVALID);
		}
	}
	
	public Tile codeToTile(String tile) {
		int tileCode = Integer.parseInt(tile);
		int shape = tileCode % 6;
		int color = (tileCode - shape) / 6;
		Shape shapeEnum = Shape.toEnum(shape);
		Color colorEnum = Color.toEnum(color);
		return new Tile(colorEnum, shapeEnum);
	}

	public String tileToCode(Tile tile) {
		return String.format("%d", tile.getColor().toInt() * 6 + tile.getShape().toInt());
	}
}
