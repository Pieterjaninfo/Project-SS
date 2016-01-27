package qwirkle;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
//import java.util.Set;

public class Board {

	//@ private invariant board != null;
	private Map<Integer, Map<Integer, Tile>> board;
	
	public Board() {
		this.board = new HashMap<Integer, Map<Integer, Tile>>();
	}
	
	//@ requires board != null;
	//@ ensures getAllTiles() == board;
	public Board(Map<Integer, Map<Integer, Tile>> board) {
		this.board = board;
	}
	
	/**
	 * Check is the board contains a tile on the given coordinate.
	 * @param x The x coordinate
	 * @param y The y coordinate
	 * @return true if there exists a tile on the given coordinate.
	 */
	/*@ pure */ public boolean containsTile(int x, int y) {
		return board.containsKey(x) && board.get(x).containsKey(y);
	}
	
	/**
	 * Placed the given tile on the board at the given coordinate.
	 * @param tile The tile you want to place
	 * @param x The x coordinate
	 * @param y The y coordinate
	 */
	//@ requires tile != null;
	public void placeTile(Tile tile, int x, int y) {
		if (!board.containsKey(x)) {
			board.put(x, new HashMap<Integer, Tile>());
		}
		board.get(x).put(y, tile);
	}
	
	/**
	 * Returns all tiles that are placed on the board.
	 * @return all tiles on the board
	 */
	/*@ pure */ public Map<Integer, Map<Integer, Tile>> getAllTiles() {
		return board;
	}
	
	/**
	 * Checks if there are no tiles on the coordinates where the move wants to put the tiles.
	 * @param move The move you want to do
	 * @return true if all the tile spots are free
	 */
	//@ requires move != null;
	/*@ pure */ private boolean isPlaceFree(Move move) {
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
	public Tile getTile(int x, int y) {
		Tile tile = null;
		if (containsTile(x, y)) {
			tile = board.get(x).get(y);
		}
		return tile;
	}
	
	
	/**
	 * Returns the amount of tiles that are currently placed on the board.
	 * @return the amount of tiles on the board
	 */
	//@ ensures \result >= 0;
	/*@ pure */ public int getBoardSize() {
		return getTileList().size();
	}
	
	/**
	 * Returns a list with all the tiles from the board.
	 * @return a list of tiles with type Tile
	 */
	//@ensures \result != null;
	public List<Tile> getTileList() {
		List<Tile> result = new ArrayList<Tile>();
		Collection<Map<Integer, Tile>> map = getAllTiles().values();
		for (Map<Integer, Tile> a : map) {
			for (Tile tile : a.values()) {
				result.add(tile);
			}
		}
		return result;
	}
	
	
	
	
	/**
	 * Check if a tile from the hand can be placed and if so it return true.
	 * @param tilesList The hand you want to check
	 * @return true if the player can place a tile
	 */
	//@ requires tilesList != null;
	public boolean canPlaceATile(List<Tile> tilesList) {
		//loop through all tiles
		for (Integer x : board.keySet()) {
			for (Integer y : board.get(x).keySet()) {
				
				//loop through all tiles in hand
				for (Tile tile : tilesList) {
					
					
					//check left, right, above and below the board tile
					if (canPlaceTile(tile, x - 1, y) || canPlaceTile(tile, x + 1, y) || 
							  canPlaceTile(tile, x, y + 1) || canPlaceTile(tile, x, y - 1)) {
						return true;
					}
				}
			}
		}
		return false;
	}
	
	/**
	 * Checks if any of the tiles in the move is connected to the tiles on the board. 
	 * @return true if at least one move tile is connected to the board
	 */
	//@ requires move != null;
	public boolean isMoveConnected(Move move) {
		//check if one tile of move is connected
		boolean result = false;
		//loop through all moves
		for (Integer x : move.getTiles().keySet()) {
			for (Integer y : move.getTiles().get(x).keySet()) {
				if (containsTile(x - 1, y) || containsTile(x + 1, y) 
						  || containsTile(x, y - 1) || containsTile(x, y + 1)) {
					result = true;	
				}
			}
		}
		
		return result;
	}
	
	
	
	/* TODO the methods below contain a lot of duplicate code, 
	 * these sub-codes need to be put in methods, e.g. in a separate class called
	 * BoardChecker.java
	 */
	
	
	/**
	 * Checks if the move is allowed to be made, and if it is allowed, it does the move.
	 */
	//@ requires move != null;
	public void doMove(Move move) {
		if (checkMove(move)) {
			
			Map<Integer, Map<Integer, Tile>> moveTilesMap = move.getTiles();
			System.out.println(moveTilesMap); //TODO remove
			//System.out.println(moveTilesMap.size()); //TODO remove
			
			if (moveTilesMap.keySet().size() == 1) {
				for (Integer x : moveTilesMap.keySet()) {
					//System.out.println(moveTilesMap.get(x).keySet()); //TODO remove
					if (moveTilesMap.get(x).keySet().size() == 1) {
						//move contains one tile
						for (Integer y : moveTilesMap.get(x).keySet()) {
							Tile thisTile = moveTilesMap.get(x).get(y);
							//System.out.println(thisTile); //TODO remove
							if (canPlaceTile(thisTile, x, y)) { // not even needed
								
								System.out.println("MOVE REACHED 1 TILE 1X 1Y"); //TODO remove
								
								//place tile on board
								placeTile(thisTile, x, y);
								
								
								//----duplicateable code: placing horizPatterns--------
								//Horizontal patterns
								Tile leftTile = getTile(x - 1, y);
								Tile rightTile = getTile(x + 1, y);

								//merge tile with both left and right side
								if (leftTile != null && rightTile != null) {
									
									Pattern leftPattern = leftTile.getHorizPattern();
									Pattern rightPattern = rightTile.getHorizPattern();
									if (leftPattern != null && rightPattern != null) {
										// there is left and right pattern - merge these
										leftPattern.merge(rightPattern);
										leftPattern.addTile(thisTile);
										thisTile.setHorizPattern(leftPattern);
									} else if (leftPattern != null) {
										// there is only left pattern
										leftPattern.addTile(thisTile);
										leftPattern.addTile(rightTile);
										thisTile.setHorizPattern(leftPattern);
										rightTile.setHorizPattern(leftPattern);
									} else if (rightPattern != null) {
										// there is only right pattern
										rightPattern.addTile(thisTile);
										rightPattern.addTile(leftTile);
										thisTile.setHorizPattern(rightPattern);
										leftTile.setHorizPattern(rightPattern);
									} else {
										// both tiles have no pattern
										if (leftTile.getColor() == thisTile.getColor()) {
											// color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(leftTile);
											colorPattern.addTile(rightTile);
											thisTile.setHorizPattern(colorPattern);
											leftTile.setHorizPattern(colorPattern);
											rightTile.setHorizPattern(colorPattern);
										} else {
											// shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(leftTile);
											shapePattern.addTile(rightTile);
											thisTile.setHorizPattern(shapePattern);
											leftTile.setHorizPattern(shapePattern);
											rightTile.setHorizPattern(shapePattern);
										}
									}
					
								} else if (leftTile != null) {
									//only a tile to the left
									Pattern leftPattern = leftTile.getHorizPattern();
									if (leftPattern != null) {
										// left tile is in a pattern
										leftPattern.addTile(thisTile);
										thisTile.setHorizPattern(leftPattern);
									} else {
										// left tile has no pattern
										
										if (leftTile.getColor() == thisTile.getColor()) {
											//color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(leftTile);
											thisTile.setHorizPattern(colorPattern);
											leftTile.setHorizPattern(colorPattern);
										} else {
											//shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(leftTile);
											thisTile.setHorizPattern(shapePattern);
											leftTile.setHorizPattern(shapePattern);
										}
									}
								} else if (rightTile != null) {
									//only a tile to the right
									Pattern rightPattern = rightTile.getHorizPattern();
									if (rightPattern != null) {
										// right tile is in a pattern
										rightPattern.addTile(thisTile);
										thisTile.setHorizPattern(rightPattern);
									} else {
										// right tile has no pattern
										if (rightTile.getColor() == thisTile.getColor()) {
											//color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(rightTile);
											thisTile.setHorizPattern(colorPattern);
											rightTile.setHorizPattern(colorPattern);
										} else {
											//shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(rightTile);
											thisTile.setHorizPattern(shapePattern);
											rightTile.setHorizPattern(shapePattern);
										}
									}
								}
								
								// HORIZONTAL PATTERN SHOULD BE MERGED NOW
								
								
								//Vertical patterns
								Tile upTile = getTile(x, y + 1);
								Tile downTile = getTile(x, y - 1);
								
								//check if tile can be merged with both upper and lower side
								if (upTile != null && downTile != null) {
									//there are upper and lower tiles
									Pattern upPattern = upTile.getVertPattern();
									Pattern downPattern = downTile.getVertPattern();
									if (upPattern != null && downPattern != null) {
										// there is upper and lower pattern
										upPattern.merge(downPattern);
										upPattern.addTile(thisTile);
										thisTile.setVertPattern(upPattern);
									} else if (upPattern != null) {
										// there is only upper pattern
										upPattern.addTile(thisTile);
										upPattern.addTile(downTile);
										thisTile.setVertPattern(upPattern);
										downTile.setVertPattern(upPattern);
									} else if (downPattern != null) {
										// there is only lower pattern
										downPattern.addTile(thisTile);
										downPattern.addTile(upTile);
										thisTile.setVertPattern(downPattern);
										upTile.setVertPattern(downPattern);
									} else {
										// both tiles have no pattern
										if (thisTile.getColor() == upTile.getColor()) {
											//color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(upTile);
											colorPattern.addTile(downTile);
											thisTile.setVertPattern(colorPattern);
											upTile.setVertPattern(colorPattern);
											downTile.setVertPattern(colorPattern);
										} else {
											//shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(upTile);
											shapePattern.addTile(downTile);
											thisTile.setVertPattern(shapePattern);
											upTile.setVertPattern(shapePattern);
											downTile.setVertPattern(shapePattern);
										}
									}	
								} else if (upTile != null) {
									//only upper tile
									Pattern upPattern = upTile.getVertPattern();
									if (upPattern != null) {
										//upper tile is in a pattern
										upPattern.addTile(thisTile);
										thisTile.setVertPattern(upPattern);
									} else {
										//upper tile is not in a pattern
										if (upTile.getColor() == thisTile.getColor()) {
											//color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(upTile);
											thisTile.setVertPattern(colorPattern);
											upTile.setVertPattern(colorPattern);
										} else {
											//shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(upTile);
											thisTile.setVertPattern(shapePattern);
											upTile.setVertPattern(shapePattern);
										}
									}
								} else if (downTile != null) {
									//only lower tile
									Pattern downPattern = downTile.getVertPattern();
									if (downPattern != null) {
										//down tile is in a pattern
										downPattern.addTile(thisTile);
										thisTile.setVertPattern(downPattern);
									} else {
										//down tile has no pattern
										if (downTile.getColor() == thisTile.getColor()) {
											//color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(downTile);
											thisTile.setVertPattern(colorPattern);
											downTile.setVertPattern(colorPattern);
										} else {
											//shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(downTile);
											thisTile.setVertPattern(shapePattern);
											downTile.setVertPattern(shapePattern);
										}
									}
								}
								
								// VERTICAL PATTERN SHOULD BE MERGED NOW
								 
							} //can place tile
							
						} //for each y value
						
					} else {
						//move contains one X, multiple Y (vertPattern)
						
						System.out.println("REACHED MOVE CONTAINSMORE TILES ONE X MULT Y"); //TODO REMOVE
						// place all the tiles in Move on the board
						for (Integer y : moveTilesMap.get(x).keySet()) {
							placeTile(moveTilesMap.get(x).get(y), x, y);
						}
						
						
						//horizPattern
						for (Integer y : moveTilesMap.get(x).keySet()) {
							Tile thisTile = moveTilesMap.get(x).get(y);
							
							//TODO reuse duplicated code after implemented in boardChecker.java
							
							//--------duplicated code: set horizPattern -----------------------
							//Horizontal patterns
							Tile leftTile = getTile(x - 1, y);
							Tile rightTile = getTile(x + 1, y);

							//merge tile with both left and right side
							if (leftTile != null && rightTile != null) {
								
								Pattern leftPattern = leftTile.getHorizPattern();
								Pattern rightPattern = rightTile.getHorizPattern();
								if (leftPattern != null && rightPattern != null) {
									// there is left and right pattern - merge these
									leftPattern.merge(rightPattern);
									leftPattern.addTile(thisTile);
									thisTile.setHorizPattern(leftPattern);
								} else if (leftPattern != null) {
									// there is only left pattern
									leftPattern.addTile(thisTile);
									leftPattern.addTile(rightTile);
									thisTile.setHorizPattern(leftPattern);
									rightTile.setHorizPattern(leftPattern);
								} else if (rightPattern != null) {
									// there is only right pattern
									rightPattern.addTile(thisTile);
									rightPattern.addTile(leftTile);
									thisTile.setHorizPattern(rightPattern);
									leftTile.setHorizPattern(rightPattern);
								} else {
									// both tiles have no pattern
									if (leftTile.getColor() == thisTile.getColor()) {
										// color pattern
										ColorPattern colorPattern = 
												  new ColorPattern(thisTile.getColor());
										colorPattern.addTile(thisTile);
										colorPattern.addTile(leftTile);
										colorPattern.addTile(rightTile);
										thisTile.setHorizPattern(colorPattern);
										leftTile.setHorizPattern(colorPattern);
										rightTile.setHorizPattern(colorPattern);
									} else {
										// shape pattern
										ShapePattern shapePattern = 
												  new ShapePattern(thisTile.getShape());
										shapePattern.addTile(thisTile);
										shapePattern.addTile(leftTile);
										shapePattern.addTile(rightTile);
										thisTile.setHorizPattern(shapePattern);
										leftTile.setHorizPattern(shapePattern);
										rightTile.setHorizPattern(shapePattern);
									}
								}
				
							} else if (leftTile != null) {
								//only a tile to the left
								Pattern leftPattern = leftTile.getHorizPattern();
								if (leftPattern != null) {
									// left tile is in a pattern
									leftPattern.addTile(thisTile);
									thisTile.setHorizPattern(leftPattern);
								} else {
									// left tile has no pattern
									
									if (leftTile.getColor() == thisTile.getColor()) {
										//color pattern
										ColorPattern colorPattern = 
												  new ColorPattern(thisTile.getColor());
										colorPattern.addTile(thisTile);
										colorPattern.addTile(leftTile);
										thisTile.setHorizPattern(colorPattern);
										leftTile.setHorizPattern(colorPattern);
									} else {
										//shape pattern
										ShapePattern shapePattern = 
												  new ShapePattern(thisTile.getShape());
										shapePattern.addTile(thisTile);
										shapePattern.addTile(leftTile);
										thisTile.setHorizPattern(shapePattern);
										leftTile.setHorizPattern(shapePattern);
									}
								}
							} else if (rightTile != null) {
								//only a tile to the right
								Pattern rightPattern = rightTile.getHorizPattern();
								if (rightPattern != null) {
									// right tile is in a pattern
									rightPattern.addTile(thisTile);
									thisTile.setHorizPattern(rightPattern);
								} else {
									// right tile has no pattern
									if (rightTile.getColor() == thisTile.getColor()) {
										//color pattern
										ColorPattern colorPattern = 
												  new ColorPattern(thisTile.getColor());
										colorPattern.addTile(thisTile);
										colorPattern.addTile(rightTile);
										thisTile.setHorizPattern(colorPattern);
										rightTile.setHorizPattern(colorPattern);
									} else {
										//shape pattern
										ShapePattern shapePattern = 
												  new ShapePattern(thisTile.getShape());
										shapePattern.addTile(thisTile);
										shapePattern.addTile(rightTile);
										thisTile.setHorizPattern(shapePattern);
										rightTile.setHorizPattern(shapePattern);
									}
								}
							}
							
							// HORIZONTAL PATTERN SHOULD BE MERGED NOW
						}
					
						//vertPattern
						
						//create a list of all y values
						List<Integer> ys = new ArrayList<Integer>();
						ys.addAll(moveTilesMap.get(x).keySet());
						
						// check for shape or color pattern in hand
						Shape shape1 = moveTilesMap.get(x).get(ys.get(0)).getShape();
						Color color1 = moveTilesMap.get(x).get(ys.get(0)).getColor();
						
						Shape shape2 = moveTilesMap.get(x).get(ys.get(1)).getShape();

						//check what is the highest and lowest y-value
						Integer lowestY = Collections.min(moveTilesMap.get(x).keySet());
						Integer highestY = Collections.max(moveTilesMap.get(x).keySet());
						
					
						//all tiles on board for pattern with move tiles
						List<Tile> tilesOnBoard = new ArrayList<Tile>();
						
						//tiles below lowestY
						for (int i = lowestY; getTile(x, i - 1) != null; i--) {
						    tilesOnBoard.add(getTile(x, i - 1));
						}
						
						//tiles between lowestY and highestY
						for (int i = lowestY; i + 1 < highestY; i++) {
					    	if (containsTile(x, i + 1)) {
					    		tilesOnBoard.add(getTile(x, i + 1));
					    	}
						}
						
					   // tiles to the right of highestY
					    for (int i = highestY; getTile(x, i + 1) != null; i++) {
					    	tilesOnBoard.add(getTile(x, i - 1));
					    }
						
						boolean isShapePattern = false;
						if (shape1 == shape2) {
							//only shape in common
							isShapePattern = true;
						}
						
						if (isShapePattern) {
							//shape pattern
							ShapePattern movePattern = new ShapePattern(shape1);
							for (int i = 0; i < ys.size(); i++) {
								movePattern.addTile(moveTilesMap.get(x).get(ys.get(i)));
							}
							
							//add all tiles to movePattern
							for (Tile tile : tilesOnBoard) {
								Pattern tilePattern = tile.getVertPattern();
								if (tilePattern != null) {
									// tile has a vertPattern
									movePattern.merge(tilePattern);
								} else {
									// tile has no vertPattern
									movePattern.addTile(tile);
								}
							}
							
							//set horizPattern of boardTiles
							for (Tile tile : tilesOnBoard) {
								tile.setHorizPattern(movePattern);
							}
							
						} else {
							//color pattern
							ColorPattern movePattern = new ColorPattern(color1);
							for (int i = 0; i < ys.size(); i++) {
								movePattern.addTile(moveTilesMap.get(x).get(ys.get(i)));
							}
							
							//add all tiles to movePattern
							for (Tile tile : tilesOnBoard) {
								Pattern tilePattern = tile.getVertPattern();
								if (tilePattern != null) {
									// tile has a vertPattern
									movePattern.merge(tilePattern);
								} else {
									// tile has no vertPattern
									movePattern.addTile(tile);
								}
							}
							
							//set vertPattern of boardTiles
							for (Tile tile : tilesOnBoard) {
								tile.setVertPattern(movePattern);
							}
							
							
							
						
						
						// MOVE HAS BEEN DONE AND TILE PATTERNS HAVE BEEN SET

						
						}
						
					}
					
				
				} // for each x value
				
				// MOVE WITH ALL TILES HAVING THE SAME X SHOULD BE CORRECTLY PLACED NOW
			
			} else {
				//move contains multiple X and one Y (horizPattern)
				System.out.println("REACHED MOVE CONTAINSMORE TILES MULT X ONE Y"); //TODO REMOVE
				
				// place all the tiles in Move on the board
				for (Integer x : moveTilesMap.keySet()) {
					for (Integer y : moveTilesMap.get(x).keySet()) {
						placeTile(moveTilesMap.get(x).get(y), x, y);
					}
				}
				
				
				//TODO reuse duplicated code after implemented in boardChecker.java
				//vertPattern
				for (Integer x : moveTilesMap.keySet()) {
					for (Integer y : moveTilesMap.get(x).keySet()) {
						Tile thisTile = moveTilesMap.get(x).get(y);
						
						//Vertical patterns
						Tile upTile = getTile(x, y + 1);
						Tile downTile = getTile(x, y - 1);
						
						//check if tile can be merged with both upper and lower side
						if (upTile != null && downTile != null) {
							//there are upper and lower tiles
							Pattern upPattern = upTile.getVertPattern();
							Pattern downPattern = downTile.getVertPattern();
							if (upPattern != null && downPattern != null) {
								// there is upper and lower pattern
								upPattern.merge(downPattern);
								upPattern.addTile(thisTile);
								thisTile.setVertPattern(upPattern);
							} else if (upPattern != null) {
								// there is only upper pattern
								upPattern.addTile(thisTile);
								upPattern.addTile(downTile);
								thisTile.setVertPattern(upPattern);
								downTile.setVertPattern(upPattern);
							} else if (downPattern != null) {
								// there is only lower pattern
								downPattern.addTile(thisTile);
								downPattern.addTile(upTile);
								thisTile.setVertPattern(downPattern);
								upTile.setVertPattern(downPattern);
							} else {
								// both tiles have no pattern
								if (thisTile.getColor() == upTile.getColor()) {
									//color pattern
									ColorPattern colorPattern = 
											  new ColorPattern(thisTile.getColor());
									colorPattern.addTile(thisTile);
									colorPattern.addTile(upTile);
									colorPattern.addTile(downTile);
									thisTile.setVertPattern(colorPattern);
									upTile.setVertPattern(colorPattern);
									downTile.setVertPattern(colorPattern);
								} else {
									//shape pattern
									ShapePattern shapePattern = 
											  new ShapePattern(thisTile.getShape());
									shapePattern.addTile(thisTile);
									shapePattern.addTile(upTile);
									shapePattern.addTile(downTile);
									thisTile.setVertPattern(shapePattern);
									upTile.setVertPattern(shapePattern);
									downTile.setVertPattern(shapePattern);
								}
							}	
						} else if (upTile != null) {
							//only upper tile
							Pattern upPattern = upTile.getVertPattern();
							if (upPattern != null) {
								//upper tile is in a pattern
								upPattern.addTile(thisTile);
								thisTile.setVertPattern(upPattern);
							} else {
								//upper tile is not in a pattern
								if (upTile.getColor() == thisTile.getColor()) {
									//color pattern
									ColorPattern colorPattern = 
											  new ColorPattern(thisTile.getColor());
									colorPattern.addTile(thisTile);
									colorPattern.addTile(upTile);
									thisTile.setVertPattern(colorPattern);
									upTile.setVertPattern(colorPattern);
								} else {
									//shape pattern
									ShapePattern shapePattern = 
											  new ShapePattern(thisTile.getShape());
									shapePattern.addTile(thisTile);
									shapePattern.addTile(upTile);
									thisTile.setVertPattern(shapePattern);
									upTile.setVertPattern(shapePattern);
								}
							}
						} else if (downTile != null) {
							//only lower tile
							Pattern downPattern = downTile.getVertPattern();
							if (downPattern != null) {
								//down tile is in a pattern
								downPattern.addTile(thisTile);
								thisTile.setVertPattern(downPattern);
							} else {
								//down tile has no pattern
								if (downTile.getColor() == thisTile.getColor()) {
									//color pattern
									ColorPattern colorPattern = 
											  new ColorPattern(thisTile.getColor());
									colorPattern.addTile(thisTile);
									colorPattern.addTile(downTile);
									thisTile.setVertPattern(colorPattern);
									downTile.setVertPattern(colorPattern);
								} else {
									//shape pattern
									ShapePattern shapePattern = 
											  new ShapePattern(thisTile.getShape());
									shapePattern.addTile(thisTile);
									shapePattern.addTile(downTile);
									thisTile.setVertPattern(shapePattern);
									downTile.setVertPattern(shapePattern);
								}
							}
						} // ----end of duplicate code------
						
						// VERTICAL PATTERN SHOULD BE MERGED NOW
						
						
					}
				}
						
					
				//horizPattern
						
				//make list of all x values and get the only y value
				List<Integer> xs = new ArrayList<Integer>();
				xs.addAll(moveTilesMap.keySet());
				
				List<Integer> ysTemp = new ArrayList<Integer>();
				ysTemp.addAll(moveTilesMap.get(xs.get(0)).keySet());
				
				Integer y = ysTemp.get(0);

				//horizPattern
				
				Shape shape1 = moveTilesMap.get(xs.get(0)).get(y).getShape();
				Color color1 = moveTilesMap.get(xs.get(0)).get(y).getColor();
				Shape shape2 = moveTilesMap.get(xs.get(1)).get(y).getShape();
				

				//check what is the highest and lowest x-value
				Integer lowestX = Collections.min(moveTilesMap.keySet());
				Integer highestX = Collections.max(moveTilesMap.keySet());
				
				//all tiles on board for pattern with move tiles
				List<Tile> tilesOnBoard = new ArrayList<Tile>();	
				
				//tiles below lowestX
				for (int i = lowestX; getTile(i - 1, y) != null; i--) {
				    tilesOnBoard.add(getTile(i - 1, y));
				}
				
			    //tiles between lowestX and highestX
				for (int i = lowestX; i < highestX; i++) {
			    	if (containsTile(i + 1, y)) {
			    		tilesOnBoard.add(getTile(i + 1, y));
			    	}
			    }
				
			    //tiles to the right of highestX
			    for (int i = highestX; getTile(i + 1, y) != null; i++) {
			    	tilesOnBoard.add(getTile(i + 1, y));
			    }
				
				
				boolean isShapePattern = false;
				if (shape1 == shape2) {
					//only shape in common
					isShapePattern = true;
				}
				
				//check which patternList is filled and fill it up
				if (isShapePattern) {
					//shape pattern
					ShapePattern movePattern = new ShapePattern(shape1);
					for (int i = 0; i < xs.size(); i++) {
						movePattern.addTile(moveTilesMap.get(xs.get(i)).get(y));
					}
					
					//add all tiles to movePattern
					for (Tile tile : tilesOnBoard) {
						Pattern tilePattern = tile.getHorizPattern();
						if (tilePattern != null) {
							// tile has a horizPattern
							movePattern.merge(tilePattern);
						} else {
							// tile has no horizPattern
							movePattern.addTile(tile);
						}
					}
					
					//set horizPattern of boardTiles
					for (Tile tile : tilesOnBoard) {
						tile.setHorizPattern(movePattern);
					}
					
					
				} else {
					//color pattern
					ColorPattern movePattern = new ColorPattern(color1);
					for (int i = 0; i < xs.size(); i++) {
						movePattern.addTile(moveTilesMap.get(xs.get(i)).get(y));
					}
					
					//add all tiles to movePattern
					for (Tile tile : tilesOnBoard) {
						Pattern tilePattern = tile.getHorizPattern();
						if (tilePattern != null) {
							// tile has a horizPattern
							movePattern.merge(tilePattern);
						} else {
							// tile has no horizPattern
							movePattern.addTile(tile);
						}
					}
					
					//set horizPattern of boardTiles
					for (Tile tile : tilesOnBoard) {
						tile.setHorizPattern(movePattern);
					}
					
				
				
				//MOVE HAS BEEN DONE AND TILE PATTERNS HAVE BEEN SET

				}
			}
		} //check do move
	}

	
	/**
	 * Checks if the move is allowed to be done.
	 * @param move The move you want to do
	 * @return true if the move is allowed to be done, else returns false
	 */
	//@ requires move != null;
	public boolean checkMove(Move move) {
		//Map<Integer, Map<Integer, Tile>> shallowBoardCopy = makeBoardCopy();
		
		if (!isPlaceFree(move)) {
			return false;
		}
		
		// TODO place all duplicate codes in a sub-method in a class called BoardChecker.java!
		
		Map<Integer, Map<Integer, Tile>> placedTiles = move.getTiles();
		
		
		
		//check if at least one tile is connected when there are tiles on the board
		if (getBoardSize() > 0 && isMoveConnected(move)) {
			return false;
		}
		
		
		if (placedTiles.size() == 1) {
			// move contains tiles with only one x value
			for (Integer x : placedTiles.keySet()) {
				if (placedTiles.get(x).keySet().size() == 1) {
					
					// move contains only one tile
					for (Integer y : placedTiles.get(x).keySet()) {
						
						
						//!! make a new method new individual horizontal !!
						Tile thisTile = placedTiles.get(x).get(y);
						
						//TODO reuse duplicated code after implemented in boardChecker.java
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
								if (leftTile.equals(thisTile) 
										  || leftTile.getColor() != thisTile.getColor() 
										    && leftTile.getShape() != thisTile.getShape()) {
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
								if (rightTile.equals(thisTile) 
										  || rightTile.getColor() != thisTile.getColor() 
										    && rightTile.getShape() != thisTile.getShape()) {
									return false;
								}
							}
						}
						
						//!! check CombinedTiles horizontal!!
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
								if (leftTile.equals(rightTile) 
										  || rightTile.getColor() != leftTile.getColor() 
										    && rightTile.getShape() != leftTile.getShape()) {
									return false;
								}
							}
			
						}
						// HORIZONTAL PATTERN SHOULD BE MERGABLE NOW
						
						//TODO reuse duplicated code after implemented in boardChecker.java
						//Vertical patterns
						Tile upTile = getTile(x, y + 1);
						Tile downTile = getTile(x, y - 1);
						
						//!! check individual vertical
						// check if individual tile can be merged with upper tile
						if (upTile != null) {
							if (upTile.getVertPattern() != null) {
								// upper tile is in a pattern
								System.out.println("UPTILE VERTPATTERN 1X MULT Y"); //TODO REMOVE
								if (!upTile.getVertPattern().canAddTile(thisTile)) {
									return false;
								}
							} else {
								// upper tile has no pattern
								if (upTile.equals(thisTile) 
										  || upTile.getColor() != thisTile.getColor() 
										    && upTile.getShape() != thisTile.getShape()) {
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
								if (downTile.equals(thisTile)
										  || downTile.getColor() != thisTile.getColor()
										    && downTile.getShape() != thisTile.getShape()) {
									return false;
								}
							}
						}
						
						//!!check combinedTiles vertical!!
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
								if (upTile.equals(downTile) 
										  || upTile.getColor() != downTile.getColor() 
										    && upTile.getShape() != downTile.getShape()) {
									return false;
								}
							}	
						}
						
						// VERTICAL PATTERN SHOULD BE MERGABLE NOW
			
					}
					return true;
				
				} else {
					//move consist of tiles with one X and multiple Y (thus vertPattern)
					List<Integer> ys = new ArrayList<Integer>();
					ys.addAll(placedTiles.get(x).keySet());
					
					// check for shape or color pattern in hand
					Shape shape1 = placedTiles.get(x).get(ys.get(0)).getShape();
					Color color1 = placedTiles.get(x).get(ys.get(0)).getColor();
					
					Shape shape2 = placedTiles.get(x).get(ys.get(1)).getShape();
					Color color2 = placedTiles.get(x).get(ys.get(1)).getColor();
					List<Shape> shapeList = new ArrayList<Shape>();
					List<Color> colorList = new ArrayList<Color>();
					
					if (shape1 == shape2 && color1 == color2 
							  || shape1 != shape2 && color1 != color2) {
						//no shape or color in common OR shape and color are equal
						return false;
					} else {
						//either have a shape or a color in common
						if (shape1 == shape2) {
							//only shape in common
							colorList.add(color1);
							colorList.add(color2);
						} else {
							//only color in common
							shapeList.add(shape1);
							shapeList.add(shape2);
						}
					}
					
					if (shapeList.isEmpty()) {
						//shape pattern
						for (int i = 2; i < ys.size(); i++) {
							Color colorI = placedTiles.get(x).get(ys.get(i)).getColor(); 
							if (!colorList.contains(colorI)) {
								// list does not contain that color yet
								colorList.add(colorI);
							} else {
								// list contains color therefore cannot make a pattern
								return false;
							}
						}
					} else {
						//color pattern
						for (int i = 2; i < ys.size(); i++) {
							Shape shapeI = placedTiles.get(x).get(ys.get(i)).getShape();
							if (!shapeList.contains(shapeI)) {
								// list does not contain that shape yet
								shapeList.add(shapeI);
							} else {
								// list contains that shape therefore cannot make a pattern
								return false;
							}
						}
					}
					
					// THERE EXISTS EITHER A SHAPE OR COLOR PATTERN IN THE HAND
					
					
					//check what is the highest and lowest y-value
					Integer lowestY = Collections.min(placedTiles.get(x).keySet());
					Integer highestY = Collections.max(placedTiles.get(x).keySet());
					
					//check if difference y-difference is not too high
					if (Math.abs(highestY - lowestY) > 5) {
						return false;
					}
					
					
					//check for gaps between the lowest and highest y-value
					for (int i = lowestY + 1; i < highestY; i++) {
						if (!containsTile(x, i) && !placedTiles.get(x).containsKey(i)) {
							return false;
						}
					}
					
					// THE PLACED TILES ARE CONNECTED, THUS NO GAPS
					
					
					
					//TODO reuse duplicated code after implemented in boardChecker.java
					//check if the individual tiles can merge with vertical patterns
					//--------------start duplicate code - checkVertPattern----------------------
					for (Integer y : placedTiles.get(x).keySet()) {
						Tile thisTile = placedTiles.get(x).get(y);
						
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
								if (upTile.equals(thisTile) 
										  || upTile.getColor() != thisTile.getColor() 
										    && upTile.getShape() != thisTile.getShape()) {
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
								if (downTile.equals(thisTile) 
										  || downTile.getColor() != thisTile.getColor() 
										    && downTile.getShape() != thisTile.getShape()) {
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
								if (upTile.equals(downTile) 
										  || upTile.getColor() != downTile.getColor() 
										    && upTile.getShape() != downTile.getShape()) {
									return false;
								}
							}	
						}
						
						// VERTICAL PATTERN SHOULD BE MERGABLE NOW
						
					} //(end duplicate code!!!!!!!!!!!!)--------------------------------------
					
					
					//check which patternList is filled and make it into a Pattern
					if (shapeList.isEmpty()) {
						//colorList is filled so shape pattern
						ShapePattern movePattern = new ShapePattern(shape1);
						for (int i = 0; i < ys.size(); i++) {
							movePattern.addTile(placedTiles.get(x).get(ys.get(i)));
						}
						
						// ALL MOVE TILES ARE IN A SHAPEPATTERN
						
						//TODO reuse duplicated code after implemented in boardChecker.java
						
						//--------------------vertical pattern DUPLICATE-----------------------
						for (Integer y : placedTiles.get(x).keySet()) {
							//Vertical patterns
							//--Tile thisTile = placedTiles.get(x).get(y);
							Tile upTile = getTile(x, y + 1);
							Tile downTile = getTile(x, y - 1);
							
							// check if movePattern can be merged with upper tile
							if (upTile != null) {
								if (upTile.getVertPattern() != null) {
									// upper tile is in a pattern
									if (!upTile.getVertPattern().canMerge(movePattern)) {
										return false;
									}
								} else {
									// upper tile has no pattern
									if (!movePattern.canAddTile(upTile)) {
										return false;
									}
								}
							}
							
							// check if movePattern can be merged with lower tile
							if (downTile != null) {
								if (downTile.getVertPattern() != null) {
									// lower tile is in a pattern
									if (!downTile.getVertPattern().canMerge(movePattern)) {
										return false;
									}
								} else {
									// lower tile has no pattern
									if (movePattern.canAddTile(downTile)) {
										return false;
									}
								}
							}
							
							//check if movePattern can be merged with both upper and lower side
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
									if (!upPattern.canAddTile(downTile) 
											  || upPattern.getSize() > 4) {
										return false;
									}
								} else if (downPattern != null) {
									// there is only lower pattern
									if (!downPattern.canAddTile(upTile) 
											  || downPattern.getSize() > 4) {
										return false;
									}
								} else {
									// both tiles have no pattern
									if (upTile.equals(downTile) 
											  || upTile.getColor() != downTile.getColor() 
											    && upTile.getShape() != downTile.getShape()) {
										return false;
									}
								}	
							}

						
						} //------------------end duplicate code------------------------
						
						//TODO reuse duplicated code after implemented in boardChecker.java
						
						//----------start duplicate code ------------------------
						

							
						//all tiles on board for pattern with move tiles
						List<Tile> tilesOnBoard = new ArrayList<Tile>();	
						
						//tiles below lowestY
						for (int i = lowestY; getTile(x, i - 1) != null; i--) {
						    tilesOnBoard.add(getTile(x, i - 1));
						}
						
						//tiles between lowestY and highestY
						for (int i = lowestY; i + 1 < highestY; i++) {
					    	if (containsTile(x, i + 1)) {
					    		tilesOnBoard.add(getTile(x, i + 1));
					    	}
						}
						
					   // tiles to the right of highestY
					    for (int i = highestY; getTile(x, i + 1) != null; i++) {
					    	tilesOnBoard.add(getTile(x, i - 1));
					    }
						
					    // check if movePatttern is mergeable tiles on deck
					    for (Tile boardTile : tilesOnBoard) {
					    	if (!movePattern.canAddTile(boardTile)) {
					    		return false;
					    	}
					    	movePattern.addTile(boardTile);
					    }
						
						//--------end duplicate code------------------------------------
						
						// VERTICAL PATTERN SHOULD BE MERGABLE NOW
						
					} else {
						//shapeList is filled so color pattern
						ColorPattern movePattern = new ColorPattern(color1);
						for (int i = 0; i < ys.size(); i++) {
							movePattern.addTile(placedTiles.get(x).get(ys.get(i)));
						}
						
						// ALL MOVE TILES ARE IN A COLOR PATTERN
						
						//TODO reuse duplicated code after implemented in boardChecker.java
						
						//--------------duplicate code vertical pattern-----------------
						for (Integer y : placedTiles.get(x).keySet()) {
							//Vertical patterns
							//--Tile thisTile = placedTiles.get(x).get(y);
							Tile upTile = getTile(x, y + 1);
							Tile downTile = getTile(x, y - 1);
							
							// check if movePattern can be merged with upper tile
							if (upTile != null) {
								if (upTile.getVertPattern() != null) {
									// upper tile is in a pattern
									if (!upTile.getVertPattern().canMerge(movePattern)) {
										return false;
									}
								} else {
									// upper tile has no pattern
									if (!movePattern.canAddTile(upTile)) {
										return false;
									}
								}
							}
							
							// check if movePattern can be merged with lower tile
							if (downTile != null) {
								if (downTile.getVertPattern() != null) {
									// lower tile is in a pattern
									if (!downTile.getVertPattern().canMerge(movePattern)) {
										return false;
									}
								} else {
									// lower tile has no pattern
									if (movePattern.canAddTile(downTile)) {
										return false;
									}
								}
							}
							
							//check if movePattern can be merged with both upper and lower side
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
									if (!upPattern.canAddTile(downTile) 
											  || upPattern.getSize() > 4) {
										return false;
									}
								} else if (downPattern != null) {
									// there is only lower pattern
									if (!downPattern.canAddTile(upTile) 
											  || downPattern.getSize() > 4) {
										return false;
									}
								} else {
									// both tiles have no pattern
									if (upTile.equals(downTile) 
											  || upTile.getColor() != downTile.getColor() 
											    && upTile.getShape() != downTile.getShape()) {
										return false;
									}
								}	
							}
						} //-------------------------end duplicate code -----------------------
						
						//TODO reuse duplicated code after implemented in boardChecker.java
						
						//----------------------duplicateable code------------------------------
						
						
						//all tiles on board for pattern with move tiles
						List<Tile> tilesOnBoard = new ArrayList<Tile>();	
						
						//tiles below lowestY
						for (int i = lowestY; getTile(x, i - 1) != null; i--) {
						    tilesOnBoard.add(getTile(x, i - 1));
						}
						
					   //tiles between lowestY and highestY
						for (int i = lowestY; i + 1 < highestY; i++) {
					    	if (containsTile(x, i + 1)) {
					    		tilesOnBoard.add(getTile(x, i + 1));
					    	}
						}
						
					   // tiles to the right of highestY
					    for (int i = highestY; getTile(x, i + 1) != null; i++) {
					    	tilesOnBoard.add(getTile(x, i - 1));
					    }
						
					    // check if movePatttern is mergeable tiles on deck
					    for (Tile boardTile : tilesOnBoard) {
					    	if (!movePattern.canAddTile(boardTile)) {
					    		return false;
					    	}
					    	movePattern.addTile(boardTile);
					    }
						
						
						//------------------------end of duplicate code--------------------------
						
						// VERTICAL PATTERN SHOULD BE MERGABLE NOW
					    //which means both patterns are mergeable
					
					}
				}
				return true;
			}			
		} else {
			// move tiles have multiple X's
			
			//check if there is only one y-value and store this value
			Integer y = null;
			for (Integer x : placedTiles.keySet()) {
				List<Integer> ys = new ArrayList<Integer>();
				ys.addAll(placedTiles.get(x).keySet());
				y = ys.get(0);
				
				for (Integer x2 : placedTiles.keySet()) {
					List<Integer> ys2 = new ArrayList<Integer>();
					ys2.addAll(placedTiles.get(x2).keySet());
					Integer y2 = ys2.get(0);
					
					if (y2 != y || ys.size() > 1 || ys2.size() > 1) {	
						return false;
					}
				}
			}
			
			//quick check if y is valid
			if (y == null) {
				return false;
			}
			
			// ALL TILES SHOULD HAVE DIFFERENT X'S WITH THE SAME Y-VALUE (horizPattern)
			
			//TODO USEFULL FOR DOMOVE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
			
			//check for shape or color pattern in hand
			List<Integer> xs = new ArrayList<Integer>();
			xs.addAll(placedTiles.keySet());
			
			Shape shape1 = placedTiles.get(xs.get(0)).get(y).getShape();
			Color color1 = placedTiles.get(xs.get(0)).get(y).getColor();
			
			Shape shape2 = placedTiles.get(xs.get(1)).get(y).getShape();
			Color color2 = placedTiles.get(xs.get(1)).get(y).getColor();
			List<Shape> shapeList = new ArrayList<Shape>();
			List<Color> colorList = new ArrayList<Color>();
			
			if (shape1 == shape2 && color1 == color2 
					  || shape1 != shape2 && color1 != color2) {
				//no shape or color in common OR shape and color are equal
				//could've used tile.equals(tile) here but would cause more declaration
				return false;
			} else {
				//either have a shape or a color in common
				if (shape1 == shape2) {
					//only shape in common
					colorList.add(color1);
					colorList.add(color2);
				} else {
					//only color in common
					shapeList.add(shape1);
					shapeList.add(shape2);
				}	
			}
			
			//check which patternList is filled and fill it up
			if (shapeList.isEmpty()) {
				//shape pattern
				for (int i = 2; i < xs.size(); i++) {
					Color colorI = placedTiles.get(xs.get(i)).get(y).getColor(); 
					if (!colorList.contains(colorI)) {
						// list does not contain that color yet
						colorList.add(colorI);
					} else {
						// list contains color therefore cannot make a pattern
						return false;
					}
				}
			} else {
				//color pattern
				for (int i = 2; i < xs.size(); i++) {
					Shape shapeI = placedTiles.get(xs.get(i)).get(y).getShape();
					if (!shapeList.contains(shapeI)) {
						// list does not contain that shape yet
						shapeList.add(shapeI);
					} else {
						// list contains that shape therefore cannot make a pattern
						return false;
					}
				}
			}
			
			// THERE EXISTS EITHER A SHAPE OR COLOR PATTERN IN THE HAND
			
			//check what is the highest and lowest x-value
			Integer lowestX = Collections.min(placedTiles.keySet());
			Integer highestX = Collections.max(placedTiles.keySet());
			
			//check if difference x-difference is not too high
			if (Math.abs(highestX - lowestX) > 5) {
				return false;
			}
			
			
			//check for gaps between the lowest and highest x-value
			for (int i = lowestX + 1; i < highestX; i++) {
				if (!containsTile(i, y) && !placedTiles.containsKey(i)) {
					return false;
				}
			}
			
			// THE PLACED TILES ARE CONNECTED, THUS NO GAPS
			
			//TODO reuse duplicated code after implemented in boardChecker.java
			
			//------------------------check horizontalPattern DUPLICATE----------------------
			//check if individual tiles can be merged with horizontal patterns
			for (Integer x : placedTiles.keySet()) {
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
						if (leftTile.equals(thisTile) 
								  || leftTile.getColor() != thisTile.getColor() 
								    && leftTile.getShape() != thisTile.getShape()) {
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
						if (rightTile.equals(thisTile) 
								  || rightTile.getColor() != thisTile.getColor() 
								    && rightTile.getShape() != thisTile.getShape()) {
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
						if (leftTile.equals(rightTile) || 
								  rightTile.getColor() != leftTile.getColor() 
								  && rightTile.getShape() != leftTile.getShape()) {
							return false;
						}
					}
				}
			} //-----------------end of duplicate code----------------------------------
		
			
			// HORIZONTAL PATTERN SHOULD BE MERGABLE NOW
			
			
			
			//check which patternList is fully filled and make it into a Pattern
			if (shapeList.isEmpty()) {
				//colorList is filled so shape pattern
				ShapePattern movePattern = new ShapePattern(shape1);
				for (int i = 0; i < xs.size(); i++) {
					movePattern.addTile(placedTiles.get(xs.get(i)).get(y));
				}
				
				// ALL MOVE TILES ARE IN A SHAPEPATTERN
				
				
				for (Integer x : placedTiles.keySet()) {
					//Vertical patterns
					//--Tile thisTile = placedTiles.get(x).get(y);
					Tile upTile = getTile(x, y + 1);
					Tile downTile = getTile(x, y - 1);
					
					// check if movePattern can be merged with upper tile
					if (upTile != null) {
						if (upTile.getVertPattern() != null) {
							// upper tile is in a pattern
							if (!upTile.getVertPattern().canMerge(movePattern)) {
								return false;
							}
						} else {
							// upper tile has no pattern
							if (!movePattern.canAddTile(upTile)) {
								return false;
							}
						}
					}
					
					// check if movePattern can be merged with lower tile
					if (downTile != null) {
						if (downTile.getVertPattern() != null) {
							// lower tile is in a pattern
							if (!downTile.getVertPattern().canMerge(movePattern)) {
								return false;
							}
						} else {
							// lower tile has no pattern
							if (movePattern.canAddTile(downTile)) {
								return false;
							}
						}
					}
					
					//check if movePattern can be merged with both upper and lower side
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
							if (!upPattern.canAddTile(downTile) 
									  || upPattern.getSize() > 4) {
								return false;
							}
						} else if (downPattern != null) {
							// there is only lower pattern
							if (!downPattern.canAddTile(upTile) 
									  || downPattern.getSize() > 4) {
								return false;
							}
						} else {
							// both tiles have no pattern
							if (upTile.equals(downTile)
									  || upTile.getColor() != downTile.getColor() 
									    && upTile.getShape() != downTile.getShape()) {
								return false;
							}
						}
					}
				}
					
				//TODO reuse duplicated code after implemented in boardChecker.java
				
				//---------------------duplicatable code------------------------------
				
				
				//all tiles on board for pattern with move tiles
				List<Tile> tilesOnBoard = new ArrayList<Tile>();	
				
				//tiles below lowestX
				for (int i = lowestX; getTile(i - 1, y) != null; i--) {
				    tilesOnBoard.add(getTile(i - 1, y));
				}
				
			   //tiles between lowestX and highestX
				for (int i = lowestX; i < highestX; i++) {
			    	if (containsTile(i + 1, y)) {
			    		tilesOnBoard.add(getTile(i + 1, y));
			    	}
			    }
				
			   // tiles to the right of highestX
			    for (int i = highestX; getTile(i + 1, y) != null; i++) {
			    	tilesOnBoard.add(getTile(i + 1, y));
			    }
				
			    // check if movePatttern is mergeable tiles on deck
			    for (Tile boardTile : tilesOnBoard) {
			    	if (!movePattern.canAddTile(boardTile)) {
			    		return false;
			    	}
			    	movePattern.addTile(boardTile);
			    }
				
				
				
				
				//---------------------end of duplicate code---------------------------
				
				// VERTICAL PATTERN SHOULD BE MERGABLE NOW
				//which means that both patterns are mergeable
				
				
				
				
				
			} else {
				//colorList is empty so ColorPattern
				ColorPattern movePattern = new ColorPattern(color1);
				for (int i = 0; i < xs.size(); i++) {
					movePattern.addTile(placedTiles.get(xs.get(i)).get(y));
				}
				
				// ALL MOVE TILES ARE IN A COLORPATTERN
				
				
				for (Integer x : placedTiles.keySet()) {
					//Vertical patterns
					//--Tile thisTile = placedTiles.get(x).get(y);
					Tile upTile = getTile(x, y + 1);
					Tile downTile = getTile(x, y - 1);
					
					// check if movePattern can be merged with upper tile
					if (upTile != null) {
						if (upTile.getVertPattern() != null) {
							// upper tile is in a pattern
							if (!upTile.getVertPattern().canMerge(movePattern)) {
								return false;
							}
						} else {
							// upper tile has no pattern
							if (!movePattern.canAddTile(upTile)) {
								return false;
							}
						}
					}
					
					// check if movePattern can be merged with lower tile
					if (downTile != null) {
						if (downTile.getVertPattern() != null) {
							// lower tile is in a pattern
							if (!downTile.getVertPattern().canMerge(movePattern)) {
								return false;
							}
						} else {
							// lower tile has no pattern
							if (movePattern.canAddTile(downTile)) {
								return false;
							}
						}
					}
					
					//check if movePattern can be merged with both upper and lower side
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
							if (!upPattern.canAddTile(downTile) 
									  || upPattern.getSize() > 4) {
								return false;
							}
						} else if (downPattern != null) {
							// there is only lower pattern
							if (!downPattern.canAddTile(upTile) 
									  || downPattern.getSize() > 4) {
								return false;
							}
						} else {
							// both tiles have no pattern
							if (upTile.equals(downTile) 
									  || upTile.getColor() != downTile.getColor() 
									    && upTile.getShape() != downTile.getShape()) {
								return false;
							}
						}
					}
				}
				
				
				//TODO reuse duplicated code after implemented in boardChecker.java
				
				//---------duplicate code-------------------------------------------------
				
				//all tiles on board for pattern with move tiles
				List<Tile> tilesOnBoard = new ArrayList<Tile>();	
				
				//tiles below lowestX
				for (int i = lowestX; getTile(i - 1, y) != null; i--) {
				    tilesOnBoard.add(getTile(i - 1, y));
				}
				
			   //tiles between lowestX and highestX
				for (int i = lowestX; i < highestX; i++) {
			    	if (containsTile(i + 1, y)) {
			    		tilesOnBoard.add(getTile(i + 1, y));
			    	}
			    }
				
			   // tiles to the right of highestX
			    for (int i = highestX; getTile(i + 1, y) != null; i++) {
			    	tilesOnBoard.add(getTile(i + 1, y));
			    }
				
			    // check if movePatttern is mergeable tiles on deck
			    for (Tile boardTile : tilesOnBoard) {
			    	if (!movePattern.canAddTile(boardTile) 
			    			  || movePattern.getSize() + tilesOnBoard.size() > 6) {
			    		return false;
			    	}
			    	movePattern.addTile(boardTile);
			    }

				//----------------end of duplicate code------------------------
				
				// VERTICAL PATTERN SHOULD BE MERGABLE NOW
				//which means that both patterns are mergeable
					
		
			}	
		}
		
		return true;
	}
	
	
	
	/**
	 * Checks if the tile is allowed to be placed on the given coordinates.
	 * @param tile The tile you want to place
	 * @param x The x coordinate where you want to place the tile
	 * @param y The y coordinate where you want to place the tile
	 * @return true if the tile is allowed to be placed
	 */
	//@ requires tile != null;
	public boolean canPlaceTile(Tile tile, int x, int y) {
		if (getBoardSize() == 0) {
			return true;
		}
		
		if (containsTile(x, y)) {
			return false;
		}
		
		//TODO reuse duplicated code after implemented in boardChecker.java
		
		//---------------duplicate code----------------------------
		Tile thisTile = tile;
		
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
				if (leftTile.equals(thisTile) 
						  || leftTile.getColor() != thisTile.getColor() 
						    && leftTile.getShape() != thisTile.getShape()) {
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
				if (rightTile.equals(thisTile) 
						  || rightTile.getColor() != thisTile.getColor() 
						    && rightTile.getShape() != thisTile.getShape()) {
					return false;
				}
			}
		}
		
		//!! check CombinedTiles horizontal!!
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
				if (leftTile.equals(rightTile) 
						  || rightTile.getColor() != leftTile.getColor() 
						    && rightTile.getShape() != leftTile.getShape()) {
					return false;
				}
			}

		}
		
		//HORIZONTAL PATTERN SHOULD BE MERGEABLE NOW
		
		
		//TODO reuse duplicated code after implemented in boardChecker.java
		
		//------duplicate code: single tile in VertPattern------------------
		
		//Vertical patterns
		Tile upTile = getTile(x, y + 1);
		Tile downTile = getTile(x, y - 1);
		
		//!! check individual vertical
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
		
		//!!check combinedTiles vertical!!
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

	
		return true;

	}
	
	
	
}
