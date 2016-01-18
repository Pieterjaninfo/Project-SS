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
	/**
	 * Checks if the move is allowed to be made, and if it is allowed, it does the move.
	 */
	public void doMove(Move move) {
		Map<Integer, Map<Integer, Tile>> shallowBoardCopy = new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer key : board.keySet()) {
			Map<Integer, Tile> valueMap = new HashMap<Integer, Tile>(board.get(key));
			shallowBoardCopy.put(key, valueMap);
		}
		
		boolean running = true;
		
		Map<Integer, Map<Integer, Tile>> placedTiles = move.getTiles();
		for (Integer x : placedTiles.keySet()) {
			for (Integer y : placedTiles.get(x).keySet()) {
				if (containsTile(x, y)) {
					running = false;
				}
			}
		}
		if (!running) {
			//System.out.println("Move is not valid");
			return;
		}
		
		
		
		
		
	}
}
