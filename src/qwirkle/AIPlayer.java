package qwirkle;

import java.util.ArrayList;
import java.util.List;

public class AIPlayer implements Player {

	private Behaviour behaviour;
	//private String name;
	private List<Tile> hand;
	private Board board;
	//@ private invariant score >= 0;
	private int score;
	
	public AIPlayer(Behaviour behaviour, Board b) {
		this.behaviour = behaviour;
		this.board = b;
		this.hand = new ArrayList<Tile>();
		this.score = 0;
	}
	
	/**
	 * Returns the name of the behaviour.
	 */
	@Override
	public String getName() {
		return behaviour.getName();
	}

	/**
	 * Returns the tiles of the hand of the AI Player.
	 * @return a list of tiles with type Tile
	 */
	@Override
	public List<Tile> getHand() {
		return hand;
	}

	/**
	 * Determines a move to be taken done by the corresponding behaviour.
	 * @return a move that can be taken
	 */
	@Override
	public Move determineMove() {
		return behaviour.determineMove(board, hand);
	}
	
	@Override
	public int getScore() {
		return score;
	}
	
	// TODO method for trading cards

}
