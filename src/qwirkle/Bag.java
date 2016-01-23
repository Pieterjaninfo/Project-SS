package qwirkle;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class Bag {

	List<Tile> tiles;
	
	public Bag() {
		tiles = new ArrayList<Tile>();
		fillBag();
	}
	
	//-------------------------------- Queries -------------------------------------
	
	/**
	 * Returns all the tiles in the bag.
	 * @return a List of tiles with type Tile
	 */
	//@ ensures getSize() > 0 ==> tiles != null;
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
	 * @return a random tile with type Tile
	 */
	//@ ensures 
	public Tile getRandomTile() {
		Random r = new Random();
		return tiles.get(r.nextInt(getSize()));
	}
	
	/**
	 * Checks if the player is allowed to trade tiles.
	 * @return true if the player is allowed to make the trade
	 */
	//@ requires handTiles != null;
	public boolean canTradeTiles(List<Tile> handTiles) {
		// TODO if it is the first turn -> \result == false;
		return getSize() >= handTiles.size();
	}
	
	//----------------------------- Commands --------------------------------
	
	/**
	 * Adds the tiles from the given list to the bag and returns the same amount of tiles in a list.
	 * @return a List of tiles with type Tile
	 */
	//@ requires handTiles != null;
	public List<Tile> tradeTiles(List<Tile> handTiles) {
		List<Tile> bagTilesToHand = new ArrayList<Tile>();
		
		if (canTradeTiles(handTiles)) {

			for (int i = 0; i < handTiles.size(); i++) {
				Tile aRandomTile = getRandomTile();
				bagTilesToHand.add(aRandomTile);
				tiles.remove(aRandomTile);	
			}
			
			for (Tile handTile : handTiles) {
				tiles.add(handTile);	
			}
		}
		return bagTilesToHand;
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
	
	/**
	 * Prepares and returns the starting hand for a player and removes these tiles from the bag.
	 * @return a List of starting tiles with type Tile
	 */
	//@ ensures \result.size() == 6;
	//@ ensures \result != null;
	public List<Tile> giveStartingHand() {
		List<Tile> startingTiles = new ArrayList<>();
		for (int i = 0; i < 6; i++) {
			Tile aRandomTile = getRandomTile();
			startingTiles.add(aRandomTile);
			tiles.remove(aRandomTile);
		}
		return startingTiles;
	}
	
}
