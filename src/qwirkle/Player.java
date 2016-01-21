package qwirkle;

import java.util.List;

public interface Player {

	/**
	 * Returns the name of the player.
	 */
	public String getName();
		
	/**
	 * Returns the tiles in the hand.
	 */
	public List<Tile> getHand();
	
	/**
	 * Returns the move that the player wants to make.
	 */
	public Move determineMove();
	
	
	
}
