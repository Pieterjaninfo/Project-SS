package qwirkle;

import java.util.HashMap;
import java.util.Map;

public class Move {

	//@ private invariant points != null;
	private int points;
	//@private invariant tileList != null;
	private Map<Integer, Map<Integer, Tile>> tileList;
	
	
	public Move() {
		this.tileList = new HashMap<Integer, Map<Integer, Tile>>();
		points = 0;
	}
	
	/**
	 * Retrieves the amount of points for doing a move.
	 * @return the amount of points
	 */
	public int getPoints() {
		return points;
	}
	
	/**
	 * Adds the specified tile at the specified coordinates.
	 * @param tile the tile you want to add
	 * @param x the x coordinate
	 * @param y the y coordinate
	 */
	public void addTile(Tile tile, int x, int y) {
		if (!tileList.containsKey(x)) {
			tileList.put(x, new HashMap<Integer, Tile>());
		}
		tileList.get(x).put(y, tile);
	}
	
	
	public Map<Integer, Map<Integer, Tile>> getTiles() {
		return tileList;
	}
	
}
