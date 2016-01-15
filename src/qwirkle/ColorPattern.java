package qwirkle;

public class ColorPattern implements Pattern {

	
	
	public ColorPattern() {
		
	}
	
	
	
	
	
	
	/**
	 * Checks if the pattern can be merged into the current pattern.
	 * @return true if the pattern can be merged into the current pattern.
	 */
	@Override
	public boolean canMerge(Pattern pattern) {
		
		return false;
	}

	/**
	 * Checks if the tile can be added to the Color Pattern.
	 * @return true if the tile can be added to the Color Pattern.
	 */
	@Override
	public boolean canAdd(Tile tile) {
		// TODO Auto-generated method stub
		return false;
	}

	/**
	 * Retrieves the amount of points for doing the move.
	 * @return the amount of points.
	 */
	@Override
	public int getPoints() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean equals(Pattern pattern) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void merge(Pattern pattern) {
		// TODO Auto-generated method stub
		
	}
}
