package qwirkle;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

public class HumanPlayer implements Player {
	
	private String name;
	private Qwirkle game;
	protected List<Tile> hand;
	private int score;
	private static final String MOVE_REGEX = 
			  "^([0-5][x,s,o,*,c,d]@-?\\d{1,3},-?\\d{1,3})" +
			  "( [0-5][x,s,o,*,c,d]@\\d{1,3},\\d{1,3})*$";
	private static final String TRADE_REGEX = 
			  "^([0-5][x,s,o,*,c,d])( [0-5][x,s,o,*,c,d])*$";

	public HumanPlayer(String name, Qwirkle game) {
		this.name = name;
		this.game = game;
		this.score = 0;
		this.hand = new ArrayList<Tile>();
	}
	
	@Override
	public String getName() {
		return name;
	}

	@Override
	public List<Tile> getHand() {
		return hand;
	}

	@Override
	public Move determineMove() {
		while (true) {
			String firstInput = game.readLine("Type 'move' to make a move.\n" +
					  "Type 'trade' to trade tiles");
			if (firstInput.equals("move")) {
				Move moves = new Move();
				String input = game.readLine("Enter the tiles and location you want to place\n" +
						  " in the format tile@x,y tile@x,y etc.");
				while (!input.matches(MOVE_REGEX)) {
					input = game.readLine("Incorrect format, please try again!");
				}
				String[] tiles = input.split(" ");
				for (String move : tiles) {
					String tileString = move.split("@")[0];
					Shape shape = Shape.charToEnum(tileString.charAt(1));
					Color color = Color.toEnum(Character.digit(tileString.charAt(0), 10));
					
					Tile tile = new Tile(color, shape);
					int x = Integer.parseInt(move.split("@")[1].split(",")[0]);
					int y = Integer.parseInt(move.split("@")[1].split(",")[1]);
					moves.addTile(tile, x, y);
				}
				return moves;

			} else if (firstInput.equals("trade")) {
				String input = game.readLine("Enter the tilecodes with a space between the codes.");

				while (!input.matches(TRADE_REGEX)) {
					input = game.readLine("Incorrect format, please try again!");
				}
				List<Tile> tradeIn = new ArrayList<Tile>();
				String[] tiles = input.split(" ");
				for (String tileString : tiles) {
					Shape shape = Shape.charToEnum(tileString.charAt(1));
					Color color = Color.toEnum(Character.digit(tileString.charAt(0), 10));
					Tile tile = new Tile(color, shape);
					tradeIn.add(tile);
				}
				game.tradeMove(tradeIn);

				return null;
			} else if (firstInput.equals("exit")) {
				System.exit(0);
			}
		}
	}

	@Override
	public int getScore() {
		return score;
	}
	
	@Override
	public void setStartingHand(List<Tile> startingHand) {
		hand = startingHand;
	}

	@Override
	public int largestStartSize() {
		List<Tile> list = new ArrayList<Tile>();
		list.addAll(this.getHand());
		for (int i = 0; i < getHand().size(); i++) {
			for (int j = 0; j < getHand().size(); j++) {
				if (i != j && hand.get(i).equals(hand.get(j)) && list.contains(hand.get(i))){
					list.remove(hand.get(j));					
				}
			}
		}
		/*
		for (Tile a : hand) {
			System.out.println("hand: " + a.toString());
		}
		for (Tile b : list) {
			System.out.println("list: " + b.toString());
		}*/
		int[] a = new int[12];
		for (Tile tile : list) {
			if (tile.getShape() == Shape.CROSS) {
				a[0] += 1;
			} else if (tile.getShape() == Shape.SQUARE) {
				a[1] += 1;
			} else if (tile.getShape() == Shape.CIRCLE) {
				a[2] += 1;
			} else if (tile.getShape() == Shape.DIAMOND) {
				a[3] += 1;
			} else if (tile.getShape() == Shape.STAR) {
				a[4] += 1;
			} else if (tile.getShape() == Shape.CLOVER) {
				a[5] += 1;
			}
			if (tile.getColor() == Color.RED) {
				a[6] += 1;
			} else if (tile.getColor() == Color.ORANGE) {
				a[7] += 1;
			} else if (tile.getColor() == Color.YELLOW) {
				a[8] += 1;
			} else if (tile.getColor() == Color.GREEN) {
				a[9] += 1;
			} else if (tile.getColor() == Color.BLUE) {
				a[10] += 1;
			} else if (tile.getColor() == Color.PURPLE) {
				a[11] += 1;
			}
		}
		int largest = 0;
		for (int i = 0; i < 12; i++) {
			if (largest < a[i]) {
				largest = a[i];
			}
		}
		
		return largest;
	}

	@Override
	public boolean tilesInHand(Move move) {
		List<Tile> moveTiles = move.getTileList();
		Vector<Tile> handV = new Vector<Tile>(getHand());
		for (Tile moveTile : moveTiles) {
			if (handV.contains(moveTile)) {
				handV.remove(moveTile);
			} else {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public void addTile(List<Tile> tiles) {
		getHand().addAll(tiles);
	}

	/**
	 * Removes specified tiles from the hand.
	 * Tiles have to be in the hand
	 */
	@Override
	public void removeTile(List<Tile> tiles) {
		List<Tile> temp = new ArrayList<Tile>();
		for (Tile tile : tiles) {
			for (int i = 0; i < 6; i++) {
				if (getHand().get(i).equals(tile)) {
					temp.add(getHand().get(i));
				}
			}
		}
		getHand().removeAll(temp);
	}

	@Override
	public void addScore(Move move) {
		// TODO Auto-generated method stub
		
	}
}
