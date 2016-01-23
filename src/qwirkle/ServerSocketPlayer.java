package qwirkle;

import java.util.ArrayList;
import java.util.List;

public class ServerSocketPlayer implements Player{
	
	private Qwirkle game;
	private String playerName;
	private List<Tile> hand;
	
	public ServerSocketPlayer(String name, Qwirkle game) {
		this.game = game;
		this.playerName = name;
	}

	@Override
	public String getName() {
		return playerName;
	}

	@Override
	public List<Tile> getHand() {
		return hand;
	}

	@Override
	public Move determineMove() {
		return null;
	}

	@Override
	public int getScore() {
		return 0;
	}

	@Override
	public void setStartingHand(List<Tile> startingHand) {
		hand = startingHand;
	}

	@Override
	public int largestStartSize() {
		List<Tile> list = new ArrayList<Tile>();
		list.addAll(this.getHand());
		for (int i = 0; i < getHand().size(); i++) {
			for (int j = 0; j < getHand().size(); j++) {
				if (i != j && hand.get(i).equals(hand.get(j)) && list.contains(hand.get(i))){
					list.remove(hand.get(j));					
				}
			}
		}
		
		return list.size();
	}

}
