package test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import qwirkle.Color;
import qwirkle.Move;
import qwirkle.Shape;
import qwirkle.Tile;

public class MoveTest {
	
	private Move move;
	private Tile tile1;
	private Tile tile2;
	private Tile tile3;
	private Tile tile4;
	
	@Before
	public void setUp() {
		move = new Move();
		tile1 = new Tile(Color.BLUE, Shape.CLOVER);
		tile2 = new Tile(Color.GREEN, Shape.CLOVER);
		tile3 = new Tile(Color.BLUE, Shape.CIRCLE);
		tile4 = new Tile(Color.BLUE, Shape.CLOVER);
		move.addTile(tile1, 0, 0);
		move.addTile(tile2, 1, 0);
		move.addTile(tile3, 0, 1);
		move.addTile(tile4, 2, 0);		
	}
	
	@Test
	public void getTileListTest() {
		assertEquals(4, move.getTileList().size());
		assertTrue(move.getTileList().contains(tile1));
		assertTrue(move.getTileList().contains(tile2));
		assertTrue(move.getTileList().contains(tile3));
		assertTrue(move.getTileList().contains(tile4));
	}
	

}
