package qwirkle;

public interface Pattern {

	// TODO better JML code - also for ColorPattern and ShapePattern
	
	/**
	 * Checks if the tile is allowed to be merged within two patterns.
	 * @return true if tile is allowed to be merged within two patterns
	 */
	//@ requires pattern != null;
	/*@ pure */ public boolean canMerge(Pattern pattern);
	
	/**
	 * Checks if the tile can be added to the pattern. 
	 * @return true if tile is can be added to the pattern.
	 */
	//@ requires tile != null;
	/*@ pure */ public boolean canAddTile(Tile tile);
	
	/**
	 * Returns the amount of points for the tiles or pattern added onto another pattern.
	 * @return the amount of points
	 */
	//@ ensures \result >= 0;
	/*@ pure */ public int getPoints();
	
	/**
	 * Checks if the two instances are equal.
	 * @param pattern the pattern you want to check
	 * @return true if the instances are equal
	 */
	//@ requires pattern != null;
	/*@pure */ public boolean equals(Pattern pattern);
	
	/**
	 * Merges the given pattern with the current pattern.
	 * @param pattern has to be merged
	 */
	//@ requires pattern != null;
	public void merge(Pattern pattern);
	
	/**
	 * Adds the tile to the this pattern.
	 * @param tile The tile you want to add
	 */
	//@ requires tile != null;
	public void addTile(Tile tile);

}
