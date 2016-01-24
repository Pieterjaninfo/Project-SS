package qwirkle;

import java.util.ArrayList;
import java.util.List;

public class ShapePattern implements Pattern {

	//@ private invariant tiles != null;
	private List<Tile> tiles;
	//@ private invariant shape != null;
	private Shape shape;
	//@ private invariant colors != null;
	private List<Color> colors;
	
	
	public ShapePattern(Shape shape) {
		this.shape = shape;
		this.tiles = new ArrayList<Tile>();
		this.colors = new ArrayList<Color>();
	}
	
	//----------------------- Queries -----------------------------
	
	/**
	 * Returns the shape of the Shape Pattern.
	 * @return the shape of type Shape
	 */
	public Shape getShapes() {
		return shape;
	}
	
	/**
	 * Returns the list of all the colors of the tiles in the Shape Pattern.
	 * @return a list of colors with type Color
	 */
	public List<Color> getColors() {
		return colors;
	}
	
	/**
	 * Returns the list of all tiles in the Shape Pattern.
	 * @return the list of tiles with type Tile
	 */
	public List<Tile> getTiles() {
		return tiles;
	}
	
	/**
	 * Checks if the pattern can be merged into the current pattern.
	 * @return true if the pattern can be merged into the current pattern.
	 */
	@Override
	public boolean canMerge(Pattern pattern) {
		if (equals(pattern) && ((ShapePattern) pattern).getShapes() == shape) {
			List<Color> patternColors = ((ShapePattern) pattern).getColors();
			for (Color color : patternColors) {
				if (colors.contains(color)) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * Checks if the tile can be added to the Shape Pattern.
	 * @return true if the tile can be added to the Shape Pattern.
	 */
	@Override
	public boolean canAddTile(Tile tile) {
		return tile.getShape() == shape && !colors.contains(tile.getColor());
	}

	/**
	 * Retrieves the amount of points for doing the move.
	 * @return the amount of points
	 */
	@Override
	public int getPoints() {
		int result = 0;
		
		if (colors.size() == 6) {
			result = colors.size() * 2;
		} else {
			result = colors.size();
		}
		return result;
	}

	/**
	 * Check if the pattern is equal to the Shape Pattern.
	 * @param pattern The pattern you want to compare
	 * @return true if the pattern is a Shape Pattern
	 */
	@Override
	public boolean equals(Pattern pattern) {
		return pattern instanceof ShapePattern;
	}
	
	/**
	 * Returns the amount of tiles in the Shape Pattern.
	 */
	@Override
	public int getSize() {
		return tiles.size();
	}

	//----------------------- Commands -------------------------
	
	/**
	 * Merges the given Shape Pattern correctly with the current Shape Pattern.
	 * @param pattern The pattern you want to merge into this pattern
	 */
	@Override
	public void merge(Pattern pattern) {
		if (canMerge(pattern)) {
			List<Tile> patternTiles = ((ShapePattern) pattern).getTiles();
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

	/**
	 * Adds the tile to the Shape Pattern if it is possible.
	 * @param tile The tile you want to add to the Shape Pattern
	 */
	@Override
	public void addTile(Tile tile) {
		if (canAddTile(tile)) {
			tiles.add(tile);
			colors.add(tile.getColor());
		}
	}
	
	
	
}
