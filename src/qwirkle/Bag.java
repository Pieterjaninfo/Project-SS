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
	
	//-------------------------------- Queries -------------------------------------
	
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
	//@ ensures 
	public Tile getRandomTile() {
		/*List<Tile> copiedTiles = new ArrayList<Tile>(tiles);
		Collections.shuffle(copiedTiles);
		Tile aRandomTile = copiedTiles.get(0);
		return aRandomTile;*/
		
		Collections.shuffle(tiles);
		return tiles.get(0);
	}
	
	/**
	 * Checks if the player is allowed to trade tiles.
	 * @return true if the player is allowed to make the trade
	 */
	//@ requires handTiles != null;
	public boolean canTradeTiles(List<Tile> handTiles) {

		/*if (handTiles.size() > getSize()) {
			return false;
		}
		// TODO if it is the first turn -> \result == false;
		
		return true;*/
		
		return getSize() >= handTiles.size();
	}
	
	//----------------------------- Commands --------------------------------
	
	/**
	 * Does the trade and returns true if the trade was successful.
	 * @return true if the trade was successful
	 */
	//@ requires handTiles != null;
	public List<Tile> tradeTiles(List<Tile> handTiles) {
		
		
		//TODO think about how to communicate with players' hand AND what order this should be executed first
		// I'm actually thinking of having setters or something like that in the player class.
		
		List<Tile> deckTilesToHand = new ArrayList<Tile>();
		
		if (canTradeTiles(handTiles)) {
			// TODO put handTiles (from hand) in the bag
			
			
			for (int i = 0; i < handTiles.size(); i++) {
				deckTilesToHand.add(getRandomTile());
			}
		}
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
	
	/**
	 * Prepares the starting hand and gives it to the player.
	 */
	public void giveStartingHand() {
		List<Tile> startingTiles = new ArrayList<>();
		for (int i = 0; i < 6; i++) {
			startingTiles.add(getRandomTile());
		}
		
		// TODO give startingTiles to player
	}
	
}
