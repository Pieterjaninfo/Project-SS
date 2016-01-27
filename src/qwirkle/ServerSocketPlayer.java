package qwirkle;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

public class ServerSocketPlayer implements Player {
	
	//private Qwirkle game;
	private String playerName;
	private List<Tile> hand;
	private int score;
	
	public ServerSocketPlayer(String name, Qwirkle game) {
		//this.game = game;
		this.playerName = name;
		this.score = 0;
	}

	@Override
	public String getName() {
		return playerName;
	}

	@Override
	public List<Tile> getHand() {
		return hand;
	}

	@Override
	public Move determineMove() {
		return null;
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
				if (i != j && hand.get(i).equals(hand.get(j)) && list.contains(hand.get(i))) {
					list.remove(hand.get(j));					
				}
			}
		}
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
		List<Tile> had = new ArrayList<Tile>();
		int i = 0;
		for (Tile moveTile : moveTiles) {
			for (Tile handVTiles : handV) {
				if (moveTile.equals(handVTiles) && !had.contains(handVTiles)) {
					had.add(handVTiles);
					i++;
				}
			}
		}
		return i == moveTiles.size();
	}

	@Override
	public void addTile(List<Tile> tiles) {
		getHand().addAll(tiles);
	}

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

	/**
	 * Add the amount of points rewarded for doing the move to the player score.
	 * @param move The move you did for the points
	 */
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
