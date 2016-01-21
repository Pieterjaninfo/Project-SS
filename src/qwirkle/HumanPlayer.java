package qwirkle;

import java.util.List;

public class HumanPlayer implements Player {
	
	private String name;
	private Qwirkle game;

	public HumanPlayer(String name, Qwirkle game) {
		this.name = name;
		this.game = game;
	}
	
	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return name;
	}

	@Override
	public List<Tile> getHand() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Move determineMove() {
		// TODO Auto-generated method stub
		return null;
	}
	

	/*
	 * niet lezen en schrijven naar system.output maar de Qwirkle.java aanropen
	 * dezelfde game van Qwirkle krijgen
	 * 
	 * zodra move is aangemaakt, dan 
	 * 
	 * 
	 * determine move vraag wat keuze is
	 * make move -> geef aan move -> 
	 */
}
