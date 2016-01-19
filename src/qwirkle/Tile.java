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
	
	/**
	 * Checks if the color and the shape are equal, if so it returns true, else it return false.
	 * @param tile The tile you want to compare
	 * @return true if the tile shape and color are equal
	 */
	public boolean equals(Tile tile) {
		return tile.getShape() == shape && tile.getColor() == color; 
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
	
	public Color getColor() {
		return color;
	}
	
	public Shape getShape() {
		return shape;
	}
	
	public void setVertPattern(Pattern vertP) {
		this.vertPattern = vertP;
	}
	
	public void setHorizPattern(Pattern horizP) {
		this.horizPattern = horizP;
	}
	
}
