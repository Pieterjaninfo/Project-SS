package test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import qwirkle.Color;
import qwirkle.Move;
import qwirkle.Player;
import qwirkle.Qwirkle;
import qwirkle.ServerSocketPlayer;
import qwirkle.Shape;
import qwirkle.Tile;

public class PlayerTest {

	private Move move1;
	private Move move2;
	private Move move3;
	private Tile tile1;
	private Tile tile2;
	private Tile tile3;
	private Tile tile4;
	private Tile tile5;
	private Tile tile6;
	private Tile tile7;
	private List<Tile> startingHand = new ArrayList<Tile>();
	private Player player;
	
	@Before
	public void setUp() {
		Qwirkle game = new Qwirkle();
		move1 = new Move();
		move2 = new Move();
		move3 = new Move();
		tile1 = new Tile(Color.BLUE, Shape.CLOVER);
		tile2 = new Tile(Color.GREEN, Shape.CLOVER);
		tile3 = new Tile(Color.BLUE, Shape.CIRCLE);
		tile4 = new Tile(Color.BLUE, Shape.CLOVER);
		tile5 = new Tile(Color.RED, Shape.SQUARE);
		tile6 = new Tile(Color.PURPLE, Shape.DIAMOND);
		tile7 = new Tile(Color.YELLOW, Shape.CROSS);
		move1.addTile(tile1, 0, 0);
		move1.addTile(tile2, 1, 0);
		move1.addTile(tile3, 0, 1);
		move1.addTile(tile4, 2, 0);
		move2.addTile(tile1, 0, 0);
		move2.addTile(tile7, 2, 0);
		move3.addTile(tile2, 1, 0);
		move3.addTile(tile2, 2, 0);
		player = new ServerSocketPlayer("Test", game);
		startingHand.add(tile1);
		startingHand.add(tile2);
		startingHand.add(tile3);
		startingHand.add(tile4);
		startingHand.add(tile5);
		startingHand.add(tile6);
		player.setStartingHand(startingHand);
	}
	
	@Test
	public void startingHand() {
		assertEquals(6, player.getHand().size());
	}
	
	@Test
	public void getCorrectTileListTest() {
		assertTrue(player.tilesInHand(move1));
	}
	
	@Test
	public void getIncorrectTileListHandTest() {
		assertFalse(player.tilesInHand(move2));
	}
	
	@Test
	public void getDoubleTileListHandTest() {
		assertFalse(player.tilesInHand(move3));
	}
}
