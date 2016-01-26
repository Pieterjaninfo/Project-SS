package qwirkle;

import java.util.ArrayList;
import java.util.List;

public class ColorPattern implements Pattern {

	//@ private invariant tiles != null;
	private List<Tile> tiles;
	//@ private invariant color != null;
	private Color color;
	//@ private invariant shapes != null;
	private List<Shape> shapes;
	
	//@ requires color != null;
	public ColorPattern(Color color) {
		this.color = color;
		this.tiles = new ArrayList<Tile>();
		this.shapes = new ArrayList<Shape>();
	}
	
	//----------------------- Queries -----------------------------

	/**
	 * Checks if the pattern can be merged into the current pattern.
	 * @return true if the pattern can be merged into the current pattern.
	 */
	//@ requires pattern != null;
	@Override
	public boolean canMerge(Pattern pattern) {
		if (equals(pattern) && ((ColorPattern) pattern).getColors() == color) {
			List<Shape> patternShapes = ((ColorPattern) pattern).getShapes();
			for (Shape shape : patternShapes) {
				if (shapes.contains(shape)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks if the tile can be added to the Color Pattern.
	 * @return true if the tile can be added to the Color Pattern.
	 */
	//@ requires tile != null;
	@Override
	public boolean canAddTile(Tile tile) {
		return tile.getColor() == this.color && !shapes.contains(tile.getShape());
	}

	/**
	 * Retrieves the amount of points for doing the move.
	 * @return the amount of points
	 */
	//@ ensures \result >= 0;
	@Override
	public int getPoints() {
		int result = 0;
		
		if (shapes.size() == 6) {
			result = shapes.size() * 2;
		} else {
			result = shapes.size();
		}
		return result;
	}

	/**
	 * Check if the pattern is equal to the color pattern.
	 * @param pattern The pattern you want to compare
	 * @return true if the pattern is a color pattern
	 */
	//@ requires pattern != null;
	@Override
	public boolean equals(Pattern pattern) {
		return pattern instanceof ColorPattern;
	}

	/**
	 * Returns the list of all tiles in the color pattern.
	 * @return the list of tiles with type Tile
	 */
	//@ ensures \result != null;
	/*@ pure */ public List<Tile> getTiles() {
		return tiles;
	}

	/**
	 * Returns the color of the Color Pattern.
	 * @return the color of type Color
	 */
	//@ ensures \result != null;
	/*@ pure */ public Color getColors() {
		return color;
	}

	/**
	 * Returns the list of all the shapes of the tiles in the Color Pattern.
	 * @return a list of shapes with type Shape
	 */
	//@ ensures \result != null;
	/*@ pure */ public List<Shape> getShapes() {
		return shapes;
	}
	
	/**
	 * Returns the amount of tiles in the Color Pattern.
	 */
	//@ ensures \result >= 0;
	@Override
	/*@ pure */ public int getSize() {
		return tiles.size();
	}
	
	//----------------------- Commands -------------------------

	
	/**
	 * Adds the tile to the Color Pattern if it is possible.
	 * @param tile The tile you want to add to the color pattern
	 */
	//@ requires tile != null;
	@Override
	public void addTile(Tile tile) {
		if (canAddTile(tile)) {
			tiles.add(tile);
			shapes.add(tile.getShape());
		}
	}
	
	/**
	 * Merges the given color pattern correctly with the current color pattern.
	 * @param pattern The pattern you want to merge into this pattern
	 */
	//@ requires pattern != null;
	@Override
	public void merge(Pattern pattern) {
		if (canMerge(pattern)) {
			List<Tile> patternTiles = ((ColorPattern) pattern).getTiles();
			Tile aTile = patternTiles.get(0);
			boolean isVertPattern = false;
			
			
			//old:  if (aTile.getVertPattern() != null)
			if (aTile.getVertPattern() == this) {
				isVertPattern = true;
			}

			for (Tile tile : patternTiles) {		
				addTile(tile);
				if (isVertPattern) {
					tile.setVertPattern(pattern);
				} else {
					tile.setHorizPattern(pattern);
				}
			}
		}
	}

}
