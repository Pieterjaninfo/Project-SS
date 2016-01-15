package qwirkle;

import java.util.HashMap;
import java.util.Map;

public class Board {

	private Map<Integer, Map<Integer, Tile>> board;
	
	public Board() {
		this.board = new HashMap<Integer, Map<Integer, Tile>>();
	}
	
	/**
	 * Check is the board contains a tile on the given coordinate.
	 * @param x the x coordinate
	 * @param y the y coordinate
	 * @return true if there exists a tile on the given coordinate.
	 */
	public boolean containsTile(int x, int y) {
		return board.containsKey(x) && board.get(x).containsKey(y);
	}
	
	/**
	 * Checks ????????????????????
	 * @return
	 */
	public boolean isValidMove() {
		return false;
	}
	
	public void doMove() {
		
	}
}
