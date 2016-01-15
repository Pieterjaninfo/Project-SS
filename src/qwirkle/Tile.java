package qwirkle;

public class Tile {

	Pattern vertPattern;
	Pattern horizPattern;
	
	
	public Tile() {
		vertPattern = null;
		horizPattern = null;
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
