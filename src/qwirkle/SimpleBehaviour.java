package qwirkle;
//import java.util.Random;

//import java.util.ArrayList;
//import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Pieter Jan
 *
 */
public class SimpleBehaviour implements Behaviour {

	
	/**
	 * Returns a move that is valid, or returns null if there are no possible moves.
	 * @param b The board
	 * @param hand The tiles in the hand
	 * @return Returns a move if there is a possible move, else returns null
	 */
	@Override
	public Move determineMove(Board b, List<Tile> hand) {
		Move moves = new Move();
		
		/*Map<Integer, Map<Integer, Tile>> possibleSpots = 
		 *	  new HashMap<Integer, Map<Integer, Tile>>();
		 */
		
		Map<Integer, Map<Integer, Tile>> boardTiles = b.getAllTiles();
		
		for (int x : boardTiles.keySet()) {
			for (int y : boardTiles.get(x).keySet()) {
				if (b.containsTile(x, y)) {
					
					if (b.getTile(x - 1, y) == null) {
						for (Tile handTile : hand) {
							if (b.canPlaceTile(handTile, x - 1, y)) {
								moves.addTile(handTile, x - 1, y);
								return moves;
							}
						}
					}
					
					if (b.getTile(x + 1, y) == null) {
						for (Tile handTile : hand) {
							if (b.canPlaceTile(handTile, x + 1, y)) {
								moves.addTile(handTile, x + 1, y);
								return moves;
							}
						}
					}
					
					if (b.getTile(x, y - 1) == null) {
						for (Tile handTile : hand) {
							if (b.canPlaceTile(handTile, x, y - 1)) {
								moves.addTile(handTile, x, y - 1);
								return moves;
							}
						}
					}
					
					if (b.getTile(x, y + 1) == null) {
						for (Tile handTile : hand) {
							if (b.canPlaceTile(handTile, x, y + 1)) {
								moves.addTile(handTile, x, y + 1);
								return moves;
							}
						}
					}
				}	
			}	
		}
		return null;
	}
	
	/**
	 * Returns the behaviour name "Simple Behaviour".
	 */
	@Override
	public String getName() {
		return "Simple Behaviour";
	}

}
