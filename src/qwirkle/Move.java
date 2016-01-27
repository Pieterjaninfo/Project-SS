package qwirkle;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Move {
	
	//@ private invariant points >= 0;
	private int points;
	//@ private invariant tileList != null;
	private Map<Integer, Map<Integer, Tile>> tileList;
	
	
	public Move() {
		this.tileList = new HashMap<Integer, Map<Integer, Tile>>();
		points = 0;
	}
	
	/**
	 * Retrieves the amount of points for doing a move.
	 * @return the amount of points
	 */
	//@ ensures \result >= 0;
	/*@ pure */ public int getPoints() {
		return points;
	}

	//@ ensures \result != null;
	/*@ pure */ public Map<Integer, Map<Integer, Tile>> getTiles() {
		return tileList;
	}
	
	/**
	 * Adds the specified tile at the specified coordinates.
	 * @param tile The tile you want to add
	 * @param x The x coordinate
	 * @param y The y coordinate
	 */
	//@ requires tile != null;
	public void addTile(Tile tile, int x, int y) {
		if (!tileList.containsKey(x)) {
			tileList.put(x, new HashMap<Integer, Tile>());
		}
		tileList.get(x).put(y, tile);
	}
	
	/**
	 * Returns a list with all the tiles from the move.
	 * @return a list of tiles with type Tile
	 */
	//@ensures \result != null;
	public List<Tile> getTileList() {
		List<Tile> result = new ArrayList<Tile>();
		Collection<Map<Integer, Tile>> map = getTiles().values();
		for (Map<Integer, Tile> a : map) {
			for (Tile tile : a.values()) {
				result.add(tile);
			}
		}
		return result;
	}

	public String toCode() {
		String result = "";
		for (Integer x : getTiles().keySet()) {
			for (Integer y : getTiles().get(x).keySet()) {
				String temp = String.format("%s@%d,%d",
						  getTiles().get(x).get(y).toCodedString(), x, y);
				result = String.format("%s %s", result, temp);
			}
		}
		return result;		
	}
	
	public String toMoveServerCode(Qwirkle game) {
		String result = "";
		for (Integer x : getTiles().keySet()) {
			for (Integer y : getTiles().get(x).keySet()) {
				String temp = String.format("%s@%d,%d",
						  game.tileToCode(getTiles().get(x).get(y)), x, y);
				result = String.format("%s %s", result, temp);
			}
		}
		return result;		
	}
}
