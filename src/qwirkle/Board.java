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
		checkDoMove(move);
	}

	
	public Map<Integer, Map<Integer, Tile>> makeBoardCopy() {
		Map<Integer, Map<Integer, Tile>> shallowBoardCopy = new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer key : board.keySet()) {
			Map<Integer, Tile> valueMap = new HashMap<Integer, Tile>(board.get(key));
			shallowBoardCopy.put(key, valueMap);
		}
		return shallowBoardCopy;
	}
	
	private boolean checkDoMove(Move move) {
		Map<Integer, Map<Integer, Tile>> shallowBoardCopy = makeBoardCopy();
		
		if (!isPlaceFree(move)) {
			return false;
		}
		
		Map<Integer, Map<Integer, Tile>> placedTiles = move.getTiles();
		for (Integer x : placedTiles.keySet()) {
			for (Integer y : placedTiles.get(x).keySet()) {
				Tile thisTile = placedTiles.get(x).get(y);
				
				//Horizontal patterns
				Tile leftTile = getTile(x - 1, y);
				Tile rightTile = getTile(x + 1, y);
				//Vertical patterns
				Tile upTile = getTile(x, y + 1);
				Tile downTile = getTile(x, y - 1);				
				
				if (leftTile != null) {
				//check blablabla	
				}
				
				
			}
		
		}
		return true;
	}
	
	
	

	private boolean isPlaceFree(Move move) {
		Map<Integer, Map<Integer, Tile>> placedTiles = move.getTiles();
		for (Integer x : placedTiles.keySet()) {
			for (Integer y : placedTiles.get(x).keySet()) {
				if (containsTile(x, y)) {
					return false;
				}
			}
		}
		return true;
	}
	
	
	public Tile getTile(int x, int y) {
		Tile tile = null;
		if (containsTile(x, y)) {
			tile = board.get(x).get(y);
		}
		return tile;
	}
	
	public boolean canPlaceTile(Tile tile, int x, int y) {
		
		
		
		return false;
	}
	
	
}
