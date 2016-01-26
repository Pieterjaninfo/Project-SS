package qwirkle;

import java.util.List;

public interface Player {

	/**
	 * Returns the name of the player or if it's a AIPlayer, the name of the behaviour.
	 */
	//@ ensures \result != null;
	public String getName();
		
	/**
	 * Returns the tiles in the hand.
	 */
	//@ ensures \result != null;
	public List<Tile> getHand();
	
	/**
	 * Returns the move that the player wants to make.
	 */
	public Move determineMove();
	
	/**
	 * Returns the score that the player has.
	 * @return the score of the player
	 */
	//@ ensures \result >= 0;
	public int getScore();
	
	/**
	 * Adds the amount of points gained from the move to the total score.
	 * @param move The move you did
	 */
	//@ requires move != null;
	public void addScore(Move move);
	
	/**
	 * Sets the starting hand of the player.
	 * @param startingHand The tile list you want the hand to become
	 */
	//@ requires startingHand != null;
	public void setStartingHand(List<Tile> startingHand);
	
	/**
	 * Returns the largest row that can be created with the tiles in the hand.
	 * @return the integer value of the largest possible row
	 */
	//@ ensures \result >= 0;
	public int largestStartSize();
	
	/**
	 * Checks if the player has all the tiles from the move in his hand.
	 * @param move The tiles from the move you want to check
	 * @return true if the player has all the tiles from his hand
	 */
	//@ requires move != null;
	public boolean tilesInHand(Move move);
	
	/**
	 * adds the tiles to the hand.
	 */
	public void addTile(List<Tile> tiles);
	
	/**
	 * 
	 */
	public void removeTile(List<Tile> tiles);
}
