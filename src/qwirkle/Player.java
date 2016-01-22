package qwirkle;

import java.util.List;

public interface Player {

	/**
	 * Returns the name of the player or if it's a AIPlayer, the name of the behaviour.
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
	
	/**
	 * Returns the score that the player has.
	 * @return the score of the player
	 */
	public int getScore();
}
