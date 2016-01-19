package qwirkle;

import java.util.List;

public interface Behaviour {

	/**
	 * Determines the move that can be taken.
	 * @param b the board on which the move could be taken
	 * @result returns the Move that can be taken
	 */
	public Move determineMove(Board b, List<Tile> hand);
	
	
	
	
	
	
	
}
