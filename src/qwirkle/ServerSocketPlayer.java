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
		List<Tile> list1 = new ArrayList<Tile>();
		list.add(hand.get(0));
		for (Tile tile : hand) {
			for (Tile tile1 : list) {
				if (!tile.equals(tile1)){
					//list.add(tile1);
					System.out.println(tile1.toString());
					
				}
			}
			
		}
		
		return list.size();
	}

}
