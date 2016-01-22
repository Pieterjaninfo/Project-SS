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
	@Override
	public boolean canAddTile(Tile tile) {
		/*if (tile.getColor() == this.color) {
			for (Shape shape : shapes) {
				if (tile.getShape() == shape) {
					return false;
				}
			}
		}
		return true;*/
		return tile.getColor() == this.color && !shapes.contains(tile.getShape());
	}

	/**
	 * Retrieves the amount of points for doing the move.
	 * @return the amount of points
	 */
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
	@Override
	public boolean equals(Pattern pattern) {
		return pattern instanceof ColorPattern;
	}

	/**
	 * Returns the list of all tiles in the color pattern.
	 * @return the list of tiles with type Tile
	 */
	public List<Tile> getTiles() {
		return tiles;
	}

	/**
	 * Returns the color of the Color Pattern.
	 * @return the color of type Color
	 */
	public Color getColors() {
		return color;
	}

	/**
	 * Returns the list of all the shapes of the tiles in the Color Pattern.
	 * @return a list of shapes with type Shape
	 */
	public List<Shape> getShapes() {
		return shapes;
	}
	
	//----------------------- Commands -------------------------

	
	/**
	 * Adds the tile to the Color Pattern if it is possible.
	 * @param tile The tile you want to add to the color pattern
	 */
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
