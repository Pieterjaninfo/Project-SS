package qwirkle;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

public class HumanPlayer implements Player {
	
	private String name;
	private Qwirkle game;
	protected List<Tile> hand;
	private int score;
	private static final String MOVE_REGEX = "^([0-5][x,s,o,*,c,d]@\\d{1,3},\\d{1,3})( [0-5][x,s,o,*,c,d]@\\d{1,3},\\d{1,3})*$";

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
		// TODO ask user what he wants to do, trade or do a move
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
					Shape shape = Shape.charToEnum(tileString.charAt(0));
					Color color = Color.toEnum(tileString.charAt(1));
					Tile tile = new Tile(color, shape);
					int x = Integer.parseInt(move.split("@")[1].split(",")[0]);
					int y = Integer.parseInt(move.split("@")[1].split(",")[1]);
					moves.addTile(tile, x, y);
				}
				return moves;

			} else if (firstInput.equals("trade")){
				// TODO do trade:
				
				break;
			}
		}
		
		
		return null;
	}

	@Override
	public int getScore() {
		return score;
	}

	@Override
	public void setStartingHand(List<Tile> startingHand) {
		// TODO Auto-generated method stub
		
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
	

	/*
	 * Niet lezen en schrijven naar system.output maar de Qwirkle.java aanroepen
	 * dezelfde game van Qwirkle krijgen
	 * 
	 * Zodra move is aangemaakt, dan 
	 * 
	 * 
	 * dDtermine move vraagt wat keuze is
	 * make move -> geef aan move -> 
	 */
}
