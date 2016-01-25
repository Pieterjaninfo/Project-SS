package qwirkle;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Move {

	// TODO better fucking JML needed ;c
	
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
	//@ ensures points >= 0;
	/*@ pure */ public int getPoints() {
		return points;
	}

	/*@ pure */ public Map<Integer, Map<Integer, Tile>> getTiles() {
		return tileList;
	}
	
	/**
	 * Adds the specified tile at the specified coordinates.
	 * @param tile The tile you want to add
	 * @param x The x coordinate
	 * @param y The y coordinate
	 */
	//@ \forall Tile t; ??????????????????????
	public void addTile(Tile tile, int x, int y) {
		if (!tileList.containsKey(x)) {
			tileList.put(x, new HashMap<Integer, Tile>());
		}
		tileList.get(x).put(y, tile);
	}
	
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

}
