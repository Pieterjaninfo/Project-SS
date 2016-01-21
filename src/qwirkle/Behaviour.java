package qwirkle;

import java.util.List;

public interface Behaviour {

	/**
	 * Determines the move that can be taken.
	 * @param b The board on which the move could be taken
	 * @result returns a possible move, if there are no moves possible, it returns null
	 */
	public Move determineMove(Board b, List<Tile> hand);
	
	
	
	
	
	
	
}
