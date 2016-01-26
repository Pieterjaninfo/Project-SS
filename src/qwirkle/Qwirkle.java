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
	private Boolean firstMove = true;
	
	public Qwirkle() {
		board = new Board(); // I think???
		//bag = new Bag(); Singleplayer only???
	}

	/**
	 * Constructor used for the server that receives a list of 
	 * clients and starts the game with these players.
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
			ui.showMessage("Player " + currentPlayer.getName());
			ui.showBoard(board.getAllTiles());
			ui.showHand(currentPlayer.getHand());
			makeMove();
			
			currentPlayer = players.get((players.indexOf(currentPlayer) + 1) 
					  % players.size());
			firstMove = false;
		} while (!gameOver()); //other method name??
		// TODO Show scores.
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
	
	/**
	 * Prints the message to the ui.
	 * @param msg The message to be printed
	 */
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
		firstMove = true;
		do {
			clientPlayerMap.get(currentPlayer).turn(clients);
			if (board.canPlaceATile(currentPlayer.getHand())) {
				clientPlayerMap.get(currentPlayer).pass();
			}
			// TODO if player can't play send pass.
			try {
				this.wait(); // TODO might not work test needed
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			currentPlayer = players.get((players.indexOf(currentPlayer) + 1) 
					  % players.size());
		} while (!gameOver()); 
		//TODO send the scores for each player.
		clientPlayerMap.get(currentPlayer).gameEnd();
	}
	
	
	/**
	 * Determines the player that can make the first move.
	 * @return
	 */
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
	
	/**
	 * makes the move for the current player.
	 */
	public void makeMove() {
		while (true) {
			Move move = currentPlayer.determineMove();	
			if (move == null) {
				if (!firstMove) {
					return;
				}
				ui.showMessage("Can't trade first move");
			} else if (currentPlayer.tilesInHand(move) && bag.canTradeTiles(move.getTileList())) {
				ui.showMessage("You don't have some of the tiles you tried to place!");
			} else if (board.checkMove(move)) {
				board.doMove(move);
				currentPlayer.removeTile(move.getTileList());
				currentPlayer.addTile(bag.getTiles(move.getTileList().size()));
				break;
			} else {
				ui.showMessage("Incorrect move!");
			}
		}
		firstMove = false;
	}
	/**
	 * Makes move for the current player.
	 * @param move The move in the for of the string, as determined in the protocol.
	 */
	public void makeMove(String move) {
		Move moves = new Move();
		String[] moveArray = move.split(" ");
		for (String move1 : moveArray) {
			Tile tile = codeToTile(move1.split("@")[0]);
			int x = Integer.parseInt(move1.split("@")[1].split(",")[0]);
			int y = Integer.parseInt(move1.split("@")[1].split(",")[1]);
			moves.addTile(tile, x, y);
		}
		if (!currentPlayer.tilesInHand(moves) && bag.canTradeTiles(moves.getTileList())) {
			clientPlayerMap.get(currentPlayer).error(Error.MOVE_TILES_UNOWNED);
		} else if (board.checkMove(moves)) {
			board.doMove(moves);
			currentPlayer.removeTile(moves.getTileList());
			List<Tile> newTiles = bag.getTiles(moves.getTileList().size());
			currentPlayer.addTile(newTiles);
			clientPlayerMap.get(currentPlayer).movePutOk(clients, moves.toCode());
			
			String drawString = "";
			for (Tile a : newTiles) {
				drawString = String.format("%s %s", drawString, a.toCodedString());
			}
			clientPlayerMap.get(currentPlayer).drawTile(drawString);
			this.notifyAll(); // TODO might not work test needed
		} else {
			clientPlayerMap.get(currentPlayer).error(Error.MOVE_INVALID);
		}
	}
	
	/**
	 * Makes the trade move if the player can make the trade and if it isn't the first turn.
	 * Sends the correct messages to the clienthandler to be send to the clients.
	 * @param handTiles String from protocol that contains the tilecodes of the tiles being traded.
	 */
	public void tradeMove(String handTiles) {
		if (firstMove) {
			clientPlayerMap.get(currentPlayer).error(Error.TRADE_FIRST_TURN);
			return;
		}
		String[] tileString = handTiles.split(" ");
		List<Tile> tileList = new ArrayList<Tile>();
		for (String a: tileString) {
			tileList.add(codeToTile(a));
		}		
		if (bag.canTradeTiles(tileList)) {
			currentPlayer.removeTile(tileList);
			List<Tile> newTiles = bag.tradeTiles(tileList);
			currentPlayer.addTile(newTiles);
			clientPlayerMap.get(currentPlayer).moveTradeOk(clients, newTiles.size());
			
			String newTileString = "";
			for (Tile a : newTiles) {
				newTileString = String.format("%s %s", newTileString, a.toCodedString());
			}
			clientPlayerMap.get(currentPlayer).drawTile(newTileString);
			this.notifyAll(); // TODO might not work test needed
		} else {
			clientPlayerMap.get(currentPlayer).error(Error.MOVE_INVALID);
		}
	}
	
	public void tradeMove(List<Tile> tradeTiles) {
		if (firstMove) {
			return;
		}
		if (bag.canTradeTiles(tradeTiles)) {
			currentPlayer.removeTile(tradeTiles);
			currentPlayer.addTile(bag.tradeTiles(tradeTiles));
		}
	}
	
	/**
	 * Converts the tilecode as used in the protocol to a Tile.
	 * @param tile The tilecode as used in the protocol
	 * @return a Tile
	 */
	public Tile codeToTile(String tile) {
		int tileCode = Integer.parseInt(tile);
		int shape = tileCode % 6;
		int color = (tileCode - shape) / 6;
		Shape shapeEnum = Shape.toEnum(shape);
		Color colorEnum = Color.toEnum(color);
		return new Tile(colorEnum, shapeEnum);
	}

	/**
	 * Converts a Tile to the tilecode as used in the protocol.
	 * @param tile The Tile to be converted
	 * @return a string
	 */
	public String tileToCode(Tile tile) {
		return String.format("%d", tile.getColor().toInt() * 6 + tile.getShape().toInt());
	}
	
	public String readLine(String msg) {
		return ui.readLine(msg);
	}
	
	public boolean gameOver() {
		if (bag.getSize() == 0) {
			if (!board.canPlaceATile(currentPlayer.getHand())) {
				// Nested statements to decrease the amount 
				// of times the canPlaceTile function will be called
				return true;	
			} else if (currentPlayer.getHand().isEmpty()) {
				return true;
			}
		} 
		return false;
	}
}
