package qwirkle;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

public class AIPlayer implements Player {

	//@ private invariant behaviour != null;
	private Behaviour behaviour;
	//@ private invariant hand != null;
	private List<Tile> hand;
	//@ private invariant board != null;
	private Board board;
	//@ private invariant score >= 0;
	private int score;
	
	//@ requires behaviour != null;
	//@ requires b != null;
	public AIPlayer(Behaviour behaviour, Board b) {
		this.behaviour = behaviour;
		this.board = b;
		this.hand = new ArrayList<Tile>();
		this.score = 0;
	}
	
	/**
	 * Returns the name of the behaviour.
	 */
	@Override
	/*@ pure */ public String getName() {
		return behaviour.getName();
	}

	/**
	 * Returns the tiles of the hand of the AI Player.
	 * @return a list of tiles with type Tile
	 */
	@Override
	/*@ pure */ public List<Tile> getHand() {
		return hand;
	}

	/**
	 * Determines a move to be taken done by the corresponding behaviour.
	 * @return a move that can be taken
	 */
	@Override
	public Move determineMove() {
		return behaviour.determineMove(board, hand);
	}
	
	//@ ensures \result >= 0;
	@Override
	/*@ pure */ public int getScore() {
		return score;
	}
	
	@Override
	/*@ pure */ public int largestStartSize() {
		List<Tile> list = new ArrayList<Tile>();
		list.addAll(this.getHand());
		for (int i = 0; i < getHand().size(); i++) {
			for (int j = 0; j < getHand().size(); j++) {
				if (i != j && hand.get(i).equals(hand.get(j)) && list.contains(hand.get(i))) {
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
	
	//@ ensures getHand() == startingHand;
	@Override
	public void setStartingHand(List<Tile> startingHand) {
		hand = startingHand;
	}

	//@ requires move != null;
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

	//@ requires tiles != null;
	@Override
	public void addTile(List<Tile> tiles) {
		getHand().addAll(tiles);
	}

	//@ requires tiles != null;
	@Override
	public void removeTile(List<Tile> tiles) {
		getHand().removeAll(tiles);
	}
	
	//@ requires move != null;
	@Override
	public void addScore(Move move) {
		int result = 0;
		List<Tile> moveTiles = move.getTileList();
		
		for (Tile moveTile : moveTiles) {
			result += moveTile.getHorizPattern().getPoints();
			result += moveTile.getVertPattern().getPoints();
		}
		updateScore(result);
		
	}
	
	/*
	 * Increments the current score by the value given.
	 */
	//@ ensures extra >= 0;
	private void updateScore(int extra) {
		this.score += extra;
	}
}
