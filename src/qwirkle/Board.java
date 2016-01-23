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
	 * @param x The x coordinate
	 * @param y The y coordinate
	 * @return true if there exists a tile on the given coordinate.
	 */
	//@ requires x != null;
	//@ requires y != null;
	public boolean containsTile(int x, int y) {
		return board.containsKey(x) && board.get(x).containsKey(y);
	}
	
	/**
	 * Checks ????????????????????
	 * @return
	 */
	public boolean isValidMove() {
		// TODO method may not be required
		return false;
	}
	
	/**
	 * Checks if the move is allowed to be made, and if it is allowed, it does the move.
	 */
	//@ requires move != null;
	public void doMove(Move move) {
		if (checkDoMove(move)) {
			// TODO method not finished
			
			// TODO 
		}
			
		
	}

	/**
	 * Makes a shallow board copy of the board.
	 * @return the shallow board copy
	 */
	public Map<Integer, Map<Integer, Tile>> makeBoardCopy() {
		Map<Integer, Map<Integer, Tile>> shallowBoardCopy = 
				  new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer key : board.keySet()) {
			Map<Integer, Tile> valueMap = new HashMap<Integer, Tile>(board.get(key));
			shallowBoardCopy.put(key, valueMap);
		}
		return shallowBoardCopy;
	}
	
	/**
	 * Checks if the move is allowed to be done.
	 * @param move The move you want to do
	 * @return true if the move is allowed to be done, else returns false
	 */
	//@ requires move != null;
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
				// TODO implement
				}
				
				//TODO finish this method
				
			}
		
		}
		return true;
	}
	
	/**
	 * Returns all tiles that are placed on the board.
	 * @return all tiles on the board
	 */
	public Map<Integer, Map<Integer, Tile>> getAllTiles() {
		return board;
	}
	
	/**
	 * Checks if there are no tiles on the coordinates where the move wants to put the tiles.
	 * @param move The move you want to do
	 * @return true if all the tile spots are free
	 */
	//@ requires move != null;
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
	
	/**
	 * Returns the tile on the given x and y coordinate, 
	 * 	  or null when there is no tile on the given coordinate.
	 * @param x The x coordinate
	 * @param y The y coordinate
	 * @return the tile on the coordinate, or null if there isn't a tile there
	 */
	//@ requires x != null;
	//@ requires y != null;
	public Tile getTile(int x, int y) {
		Tile tile = null;
		if (containsTile(x, y)) {
			tile = board.get(x).get(y);
		}
		return tile;
	}
	
	/**
	 * Checks if the tile is allowed to be placed on the given coordinates.
	 * @param tile The tile you want to place
	 * @param x The x coordinate where you want to place the tile
	 * @param y The y coordinate where you want to place the tile
	 * @return true if the tile is allowed to be placed
	 */
	//@ requires tile != null;
	//@ require x != null;
	//@ requires y != null;
	public boolean canPlaceTile(Tile tile, int x, int y) {
		// TODO if board is empty -> true
		if (getBoardSize() <= 0) {
			return true;
		}
		
		if (containsTile(x, y)) {
			return false;
		}
		 
		// TODO check if can merge with vertPattern-> 
		
		// TODO then check if can merge with horizPattern ->true
		return false;
	}
	
	/**
	 * Returns the amount of tiles that are currently placed on the board.
	 * @return the amount of tiles on the board
	 */
	public int getBoardSize() {
		return board.size();
	}
	
	
}
