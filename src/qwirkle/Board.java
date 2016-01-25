package qwirkle;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Board {

	private Map<Integer, Map<Integer, Tile>> board;
	
	public Board() {
		this.board = new HashMap<Integer, Map<Integer, Tile>>();
	}
	
	// TODO remove 
	public Board(Map<Integer, Map<Integer, Tile>> board) {
		this.board = board;
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
	 * Placed the given tile on the board at the given coordinate.
	 * @param tile The tile you want to place
	 * @param x The x coordinate
	 * @param y The y coordinate
	 */
	public void placeTile(Tile tile, int x, int y) {
		if (!board.containsKey(x)) {
			board.put(x, new HashMap<Integer, Tile>());
		}
		board.get(x).put(y, tile);
	}
	
	/**
	 * Checks if the move is allowed to be made, and if it is allowed, it does the move.
	 */
	//@ requires move != null;
	public void doMove(Move move) {
		if (checkMove(move)) {
			
			Map<Integer, Map<Integer, Tile>> moveTilesMap = move.getTiles();
			
			
			if (moveTilesMap.size() == 1) {
				for (Integer x : moveTilesMap.keySet()) {
					if (moveTilesMap.get(x).keySet().size() == 1) {
						//move contains one tile
						for (Integer y : moveTilesMap.get(x).keySet()) {
							Tile thisTile = moveTilesMap.get(x).get(y);
							
							if (canPlaceTile(thisTile, x, y)) {
								//Horizontal patterns
								Tile leftTile = getTile(x - 1, y);
								Tile rightTile = getTile(x + 1, y);
								
								
								//place tile on board
								placeTile(thisTile, x, y);
								
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
									} else if (rightPattern != null) {
										// there is only right pattern
										rightPattern.addTile(thisTile);
										rightPattern.addTile(leftTile);
										thisTile.setHorizPattern(rightPattern);
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
									
									Pattern upPattern = upTile.getVertPattern();
									Pattern downPattern = downTile.getVertPattern();
									if (upPattern != null && downPattern != null) {
										// there is upper and lower pattern
										upPattern.merge(downPattern);
										upPattern.addTile(thisTile);
									} else if (upPattern != null) {
										// there is only upper pattern
										upPattern.addTile(thisTile);
										upPattern.addTile(downTile);
									} else if (downPattern != null) {
										// there is only lower pattern
										downPattern.addTile(thisTile);
										downPattern.addTile(upTile);
									} else {
										// both tiles have no pattern
										if (thisTile.getColor() == upTile.getColor()) {
											//color pattern
											ColorPattern colorPattern = 
													  new ColorPattern(thisTile.getColor());
											colorPattern.addTile(thisTile);
											colorPattern.addTile(upTile);
											colorPattern.addTile(downTile);
										} else {
											//shape pattern
											ShapePattern shapePattern = 
													  new ShapePattern(thisTile.getShape());
											shapePattern.addTile(thisTile);
											shapePattern.addTile(upTile);
											shapePattern.addTile(downTile);
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
						
					} //check y values size
				} // for each x value
				// MOVE WITH SINGLE TILE SHOULD BE PLACED CORRECTLY NOW
			} else {
				//move contains more tiles
				
				if (moveTilesMap.size() == 1) {
					//move contains one X, multiple Y
					// TODO make 
				
				} else {
					//move contains multiple Y
					
					//TODO check if multiple Y-> false;
				}
			}
		}//check do move
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
	public boolean checkMove(Move move) {
		Map<Integer, Map<Integer, Tile>> shallowBoardCopy = makeBoardCopy();
		
		if (!isPlaceFree(move)) {
			return false;
		}
		
		
		// TODO place all these in sub-methods in a new method called BoardChecker.java
		
		Map<Integer, Map<Integer, Tile>> placedTiles = move.getTiles();
		
		
		//TODO different check needed DONE
		if (placedTiles.size() == 1) {
			// move contains tiles with only one x value
			for (Integer x : placedTiles.keySet()) {
				if (placedTiles.get(x).keySet().size() == 1) {
					// move contains only one tile
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
								if (leftTile.equals(thisTile) || leftTile.getColor() != thisTile.getColor() 
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
								if (rightTile.equals(thisTile) || rightTile.getColor() != thisTile.getColor() 
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
								if (leftTile.equals(rightTile) || rightTile.getColor() != leftTile.getColor() 
										  && rightTile.getShape() != leftTile.getShape()) {
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
					return true;
				}
			}			
		} else {
			// move consists of multiple tiles to be placed
			
			if (placedTiles.size() == 1) {
				// move tiles have the same X (thus vertPattern)
				for (Integer x : placedTiles.keySet()) {
					//Integer[] ys = (Integer[]) placedTiles.get(x).keySet().toArray();
					List<Integer> ys = new ArrayList<Integer>();
					
					ys.addAll(placedTiles.get(x).keySet());
					
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
					
					
					//check if the individual tiles can merge with horizontal patterns 
					//(start duplicate code!!!!!!!!!!!!)
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
					} //(end duplicate code!!!!!!!!!!!!)
					
					
					if (shapeList.isEmpty()) {
						//colorList is filled so shape pattern
						ShapePattern movePattern = new ShapePattern(shape1);
						for (int i = 0; i < ys.size(); i++) {
							movePattern.addTile(placedTiles.get(x).get(ys.get(i)));
						}
						
						// ALL MOVE TILES ARE IN A SHAPEPATTERN
						
						
						for (Integer y : placedTiles.get(x).keySet()) {
							//Vertical patterns
							Tile thisTile = placedTiles.get(x).get(y);
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
									if (upTile.equals(downTile)) {
										return false;
									}
								}	
							}
							
							//TODO extra check for if (more than) 3 tiles placed
							
							// VERTICAL PATTERN SHOULD BE MERGABLE NOW
						
							
						
						
						}
						return true;
						
						
						
						
					} else {
						//shapeList is filled so color pattern
						ColorPattern movePattern = new ColorPattern(color1);
						for (int i = 0; i < ys.size(); i++) {
							movePattern.addTile(placedTiles.get(x).get(ys.get(i)));
						}
						
						// ALL MOVE TILES ARE IN A COLOR PATTERN
						
						
						for (Integer y : placedTiles.get(x).keySet()) {
							//Vertical patterns
							Tile thisTile = placedTiles.get(x).get(y);
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
									if (upTile.equals(downTile)) {
										return false;
									}
								}	
							}
							
							//TODO extra check for if (more than) 3 tiles placed
							
							// VERTICAL PATTERN SHOULD BE MERGABLE NOW
						
						}
						return true;
						
					}
				
						
				} //this curly brace is connected with the only x value
				
			} else {
				// move tiles have multiple X's
				
				//check if there is only one y-value and store this value
				Integer y;
				for (Integer x : placedTiles.keySet()) {
					Integer[] ys = (Integer[]) placedTiles.get(x).keySet().toArray();
					y = ys[0];
					
					for (Integer x2 : placedTiles.keySet()) {
						Integer[] ys2 = (Integer[]) placedTiles.get(x).keySet().toArray();
						Integer y2 = ys2[0];
						
						//not sure if length check is needed ????????????????????/
						if (y2 != y || ys.length > 1 || ys2.length > 1) {	
							return false;
						}
					}	
				}
				
				// THERE SHOULD ALL DIFFERENT X'S WITH THE SAME Y-VALUE (horizPattern)
				
				for (Integer x : placedTiles.keySet()) {
					
				}
				
				
				
				
				
			}
			
			// TODO all tiles in move must have same X or Y -> x: horizPattern, y: vertPattern
			
			
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
		if (getBoardSize() <= 0) {
			return true;
		}
		
		if (containsTile(x, y)) {
			return false;
		}
		
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

	
		return true;

	}
	
	/**
	 * Returns the amount of tiles that are currently placed on the board.
	 * @return the amount of tiles on the board
	 */
	public int getBoardSize() {
		return board.size();
	}
	
	
}
