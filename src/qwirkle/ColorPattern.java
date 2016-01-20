package qwirkle;

import java.util.List;

public class ColorPattern implements Pattern {

	// contains all the tiles in the pattern
	private List<Tile> tiles;
	// contains all different shapes
	private Color color;
	// contains all shapes of the tiles
	private List<Shape> shapes;
	
	
	public ColorPattern() {
		
	}

	/**
	 * Checks if the pattern can be merged into the current pattern.
	 * @return true if the pattern can be merged into the current pattern.
	 */
	@Override
	public boolean canMerge(Pattern pattern) {
		if (equals(pattern) && ((ColorPattern) pattern).getColors() == color) {
			List<Tile> patternTiles = ((ColorPattern) pattern).getTiles();
			
			for (Tile onePatternTile : patternTiles) {
				for (Tile thisTile : tiles) {
					if (onePatternTile.getShape() == thisTile.getShape()) {
						return false;
					}
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
	//@ requires tile != null;
	public boolean canAdd(Tile tile) {
		if (tile.getColor() == color) {
			for (Tile oneTile : tiles) {
				if (tile.getShape() == oneTile.getShape()) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Retrieves the amount of points for doing the move.
	 * @return the amount of points.
	 */
	@Override
	public int getPoints() {
		return tiles.size();
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
	 * Merges the given color pattern with the current color pattern.
	 * @param pattern
	 */
	@Override
	public void merge(Pattern pattern) {
		// TODO Auto-generated method stub
		
	}
	
	/**
	 * Returns the list of all tiles in the color pattern.
	 * @return the list of tiles with type Tile
	 */
	public List<Tile> getTiles() {
		return tiles;
	}
	
	/**
	 * Returns the list of all the colors of the tiles in the color pattern.
	 * @return a list of colors with type Color
	 */
	public Color getColors() {
		return color;
	}
}
