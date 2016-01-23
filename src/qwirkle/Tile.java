package qwirkle;

public class Tile {

	Pattern vertPattern;
	Pattern horizPattern;
	//@ private invariant color != null;
	Color color;
	//@ private invariant shape != null;
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
	//@ requires tile != null;
	public boolean equals(Tile tile) {
		return tile.getShape() == shape && tile.getColor() == color; 
	}
	
	/**
	 * Returns the vertical pattern of the tile.
	 * @return the vertical pattern
	 */
	/*@ pure */ public Pattern getVertPattern() {
		return vertPattern;
	}
	
	/**
	 * Returns the horizontal pattern of the tile.
	 * @return the horizontal pattern
	 */
	/*@ pure */ public Pattern getHorizPattern() {
		return horizPattern;
	}
	
	/**
	 * Returns the color of the tile.
	 */
	//@ ensures \result != null;
	/*@ pure */ public Color getColor() {
		return color;
	}
	
	/**
	 * Returns the shape of the tile.
	 */
	//@ ensures \result != null;
	/*@ pure */ public Shape getShape() {
		return shape;
	}
	
	/**
	 * Sets the vertical pattern of the tile.
	 * @param vertP The vertical pattern that the tile will have
	 */
	//@ requires vertP != null;
	//@ ensures \getVertPattern() == vertP;
	public void setVertPattern(Pattern vertP) {
		this.vertPattern = vertP;
	}
	
	/**
	 * Sets the horizontal pattern of the tile.
	 * @param horizP The horizontal pattern that the tile will have
	 */
	//@ requires horizP != null;
	//@ ensures \getHorizPattern() == horizP;
	public void setHorizPattern(Pattern horizP) {
		this.horizPattern = horizP;
	}
	
	public String toString() {
		return String.format("Shape: %s,Color: %s", shape, color);
	}
	
}
