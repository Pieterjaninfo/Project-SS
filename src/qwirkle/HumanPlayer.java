package qwirkle;

import java.util.ArrayList;
import java.util.List;

public class HumanPlayer implements Player {
	
	private String name;
	private Qwirkle game;
	protected List<Tile> hand;
	private int score;

	public HumanPlayer(String name, Qwirkle game) {
		this.name = name;
		this.game = game;
		this.score = 0;
		this.hand = new ArrayList<Tile>();
	}
	
	@Override
	public String getName() {
		return name;
	}

	@Override
	public List<Tile> getHand() {
		return hand;
	}

	@Override
	public Move determineMove() {
		// TODO ask user what he wants to do, trade or do a move
		
		// TODO do move
		// TODO do trade
		return null;
	}

	@Override
	public int getScore() {
		return score;
	}
	

	/*
	 * Niet lezen en schrijven naar system.output maar de Qwirkle.java aanroepen
	 * dezelfde game van Qwirkle krijgen
	 * 
	 * Zodra move is aangemaakt, dan 
	 * 
	 * 
	 * dDtermine move vraagt wat keuze is
	 * make move -> geef aan move -> 
	 */
}
