package qwirkle;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Bag {

	List<Tile> tiles;
	
	public Bag() {
		tiles = new ArrayList<Tile>();
		fillBag();
	}
	
	/**
	 * Returns all the tiles in the bag.
	 * @return a list of tiles with type Tile
	 */
	public List<Tile> getTiles() {
		return tiles;
	}
	
	/**
	 * Returns how many tiles there are in the bag.
	 */
	//@ ensures \result >= 0;
	public int getSize() {
		return tiles.size();
	}
	
	/**
	 * Returns a random tile from the bag.
	 * @return a random tile with type Tile.
	 */
	public Tile getRandomTile() {
		List<Tile> copiedTiles = new ArrayList<Tile>(tiles);
		Collections.shuffle(copiedTiles);
		Tile aRandomTile = copiedTiles.get(0);
		return aRandomTile;
	}
	
	/**
	 * Checks if the player is allowed to trade tiles.
	 * @return
	 */
	//@ requires handTiles != null;
	public boolean canTradeTiles(List<Tile> handTiles) {
		return false;
	}
	
	/**
	 * Does the trade and returns true if the trade was successful.
	 * @return true if the trade was successful
	 */
	//@ requires handTiles != null;
	public List<Tile> tradeTiles(List<Tile> handTiles) {
		return null;
	}
	
	/*
	 * Fills the bag with all the tiles.
	 */
	private void fillBag() {
		for (Color color : Color.values()) {
			for (Shape shape : Shape.values()) {
				for (int i = 0; i < 3; i++) {
					tiles.add(new Tile(color, shape));
				}
			}
		}
	}
	
	public void giveStartingHand() {
		List<Tile> startingTiles = new ArrayList<>();
		
		for (int i = 0; i < 6; i++) {
			
		}
	}
	
}
