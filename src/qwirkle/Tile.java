package qwirkle;

public class Tile {

	Pattern vertPattern;
	Pattern horizPattern;
	Color color;
	Shape shape;
	
	
	public Tile(Color color, Shape shape) {
		vertPattern = null;
		horizPattern = null;
		this.color = color;
		this.shape = shape;
	}
	
	
	public boolean equals(Tile tile) {
		return false;
	}
	
	/**
	 * Returns the vertical pattern of the tile.
	 * @return the vertical pattern
	 */
	public Pattern getVertPattern() {
		return vertPattern;
	}
	
	/**
	 * Returns the horizontal pattern of the tile.
	 * @return the horizontal pattern
	 */
	public Pattern getHorizPattern() {
		return horizPattern;
	}
	
	
	
	
}
