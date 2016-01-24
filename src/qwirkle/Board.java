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
		
		if (placedTiles.size() == 1) {
			//move consists only of one tile
			for (Integer x : placedTiles.keySet()) {
				for (Integer y : placedTiles.get(x).keySet()) {
					Tile thisTile = placedTiles.get(x).get(y);
					
					//Horizontal patterns
					Tile leftTile = getTile(x - 1, y);
					Tile rightTile = getTile(x + 1, y);
					
					//check if individual tile can be merged with left side
					if (leftTile != null) {
						if (leftTile.getHorizPattern() != null) {
							// left tile is in a pattern
							if (!leftTile.getHorizPattern().canAddTile(thisTile)) {
								return false;
							} 
						} else {
							//left tile has no pattern
							if (leftTile.equals(leftTile)) {
								return false;
							}
						}	
					}
					//check if individual tile can be merged with right side
					if (rightTile != null) {
						if (rightTile.getHorizPattern() != null) {
							// right tile is in a pattern
							if (!rightTile.getHorizPattern().canAddTile(thisTile)) {
								return false;
							}
						} else {
							// right tile has no pattern
							if (rightTile.equals(thisTile)) {
								return false;
							}
						}
					}
					//check if tile can merge with both left and right side
					if (leftTile != null && rightTile != null) {
							
						Pattern leftPattern = leftTile.getHorizPattern();
						Pattern rightPattern = rightTile.getHorizPattern();
						if (leftPattern != null && rightPattern != null) {
							// there is left and right pattern
							if (!leftPattern.canMerge(rightPattern) || 
									  leftPattern.getSize() + rightPattern.getSize() > 5) {
								return false;
							}
						} else if (leftPattern != null) {
							// there is only left pattern
							if (!leftPattern.canAddTile(rightTile) || 
									  leftPattern.getSize() > 4) {
								return false;
							}
						} else if (rightPattern != null) {
							// there is only right pattern
							if (!rightPattern.canAddTile(leftTile) || 
									  rightPattern.getSize() > 4) {
								return false;
							}
						} else {
							// both tiles have no pattern
							if (leftTile.equals(rightTile)) {
								return false;
							}
						}
		
					}
					// HORIZONTAL PATTERN SHOULD BE MERGABLE NOW
					
					
					//Vertical patterns
					Tile upTile = getTile(x, y + 1);
					Tile downTile = getTile(x, y - 1);
					
					// check if individual tile can be merged with upper tile
					if (upTile != null) {
						if (upTile.getVertPattern() != null) {
							// upper tile is in a pattern
							if (!upTile.getVertPattern().canAddTile(thisTile)) {
								return false;
							}
						} else {
							// upper tile has no pattern
							if (upTile.equals(thisTile)) {
								return false;
							}
						}
					}
					
					// check if individual tile can be merged with lower tile
					if (downTile != null) {
						if (downTile.getVertPattern() != null) {
							// lower tile is in a pattern
							if (!downTile.getVertPattern().canAddTile(thisTile)) {
								return false;
							}
						} else {
							// lower tile has no pattern
							if (downTile.equals(thisTile)) {
								return false;
							}
						}
					}
					
					//check if tile can be merged with both upper and lower side
					if (upTile != null && downTile != null) {
						
						Pattern upPattern = upTile.getVertPattern();
						Pattern downPattern = downTile.getVertPattern();
						if (upPattern != null && downPattern != null) {
							// there is upper and lower pattern
							if (!upPattern.canMerge(downPattern) || 
									  upPattern.getSize() + downPattern.getSize() > 5) {
								return false;
							}
						} else if (upPattern != null) {
							// there is only upper pattern
							if (!upPattern.canAddTile(downTile) || upPattern.getSize() > 4) {
								return false;
							}
						} else if (downPattern != null) {
							// there is only lower pattern
							if (!downPattern.canAddTile(upTile) || downPattern.getSize() > 4) {
								return false;
							}
						} else {
							// both tiles have no pattern
							if (upTile.equals(downTile)) {
								return false;
							}
						}	
					}
					
					// VERTICAL PATTERN SHOULD BE MERGABLE NOW
		
				}
			}
			return true;			
		} else {
			// move consists of multiple tiles to be placed
			
			// TODO check if can create COLORPATTERN or SHAPEPATTERN with tiles in placedTiles
			
			/* TODO check if same X or same Y 
			 *		-> same x: check individual horizPattern (duplicate code)
			 * 		-> same y: check individual vertPattern (duplicate code)
			 */
			
			/* TODO no gaps in between given move tiles -- for loop/ placedTiles or containsTile
			 * 		-> horizPattern : no gaps between lowest and highest X
			 *		-> vertPattern  : no gaps between lowest and highest Y
			 *      			=> plus difference in value !> 5
			 */
			
			
			/* TODO check if pattern can be merged
			 * i.e.: 
			 * 			-> horizPattern: check if connected row !>6 && belong to same pattern 
			 * 	 
			 * 			-> vertPattern:  check if connected row !>6 && belong to same pattern
			 *
			 * i'm thinking:
			 *  		-> horizPattern: go left until 
			 *  
			 *  	tiles to the left of lowestX
			 *   for (int i = lowestX; getTile(i - 1, y) != null; i --) {
			 *   	if (board.containsTile( i - 1, y) {
			 *   		List<Tile>.add(getTile(i-1,y);
			 *   	}
			 *   }
			 *   
			 *   tiles between lowestX and highestX
			 *   for (int i = lowestX; i < higestX; i++) {
			 *   	if (board.containsTile(i +1,y)) {
			 *   		List<Tile>.add(getTile(i+1,y));
			 *   	}
			 *   }
			 *   
			 *   tiles to the right of highestX
			 *   for(int i = highestX; getTile(i+1,y) != null; i++) {
			 *   	if (board.containsTile(i - 1,y) {
			 *   		List<Tile>.add(getTile(i-1,y));
			 *  	}
			 *   }
			 *   
			 *   That's all there is to it. pretty easy if you ask me ;D
			 *
			 */
			
			
			
		}
		
		//below this is fucking garbageroneez
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
