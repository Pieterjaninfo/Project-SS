package qwirkle;

public interface Pattern {

	/**
	 * Checks if the tile is allowed to be merged within two patterns.
	 * @return true if tile is allowed to be merged within two patterns
	 */
	public boolean canMerge(Pattern pattern);
	
	/**
	 * Checks if the tile can be added to the pattern. 
	 * @return true if tile is can be added to the pattern.
	 */
	public boolean canAdd(Tile tile);
	
	/**
	 * Returns the amount of points when placing a tile.
	 * @return
	 */
	public int getPoints();
	
	/**
	 * Checks if the two instances are equal.
	 * @param pattern the pattern you want to check
	 * @return true if the instances are equal
	 */
	public boolean equals(Pattern pattern);
	
	/**
	 * Merges the given pattern with the current pattern.
	 * @param pattern has to be merged
	 */
	public void merge(Pattern pattern);

}
