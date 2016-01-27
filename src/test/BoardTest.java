package test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import qwirkle.Board;
import qwirkle.Color;
import qwirkle.Move;
import qwirkle.Shape;
import qwirkle.Tile;

public class BoardTest {

	private Board b;
	private Board b3;
	private Map<Integer, Map<Integer, Tile>> boardMap;
	private Tile tile1;
	private Tile tile2;
	private Tile tile3;
	private Tile tile4;
	private Tile tile5;
	private Tile tile6;
	private Tile tile7;
	private Tile tile8;
	private Tile tile9;
	private Tile tile10;
	private Tile tile11;
	private List<Tile> tilesList;
	private List<Tile> tilesList2;
	private Move move;
	
	
	private Tile t1;
	private Tile t2;
	private Tile t3;
	private Tile t4;
	private Tile t5;
	private Tile t6;
	private Tile t7;
	private Tile t8;
	private Tile t9;
	private Tile t10;
	private Tile t11;
	private Tile t12;
	private Tile t13;
	private Tile t14;
	
	
	@Before
	public void setUp() {
		
		tile1 = new Tile(Color.BLUE, Shape.CLOVER);
		tile2 = new Tile(Color.GREEN, Shape.CLOVER);
		tile3 = new Tile(Color.BLUE, Shape.CIRCLE);
		tile4 = new Tile(Color.BLUE, Shape.SQUARE);
		tile5 = new Tile(Color.RED, Shape.SQUARE);
		tile6 = new Tile(Color.BLUE, Shape.CLOVER);
		tile7 = new Tile(Color.RED, Shape.CLOVER);
		tile8 = new Tile(Color.PURPLE, Shape.CLOVER);
		tile9 = new Tile(Color.BLUE, Shape.CLOVER);
		tile10 = new Tile(Color.YELLOW, Shape.DIAMOND);
		tile11 = new Tile(Color.BLUE, Shape.STAR);
		
		tilesList = new ArrayList<Tile>();
		tilesList2 = new ArrayList<Tile>();
		
		tilesList.add(tile1);
		tilesList.add(tile2);
		tilesList.add(tile3);
		tilesList.add(tile4);
		tilesList.add(tile5);
		tilesList2.add(tile10);
		
		boardMap = new HashMap<Integer, Map<Integer, Tile>>();
		boardMap.put(0, new HashMap<Integer, Tile>());
		boardMap.put(1, new HashMap<Integer, Tile>());
		boardMap.put(2, new HashMap<Integer, Tile>());
		boardMap.get(0).put(0, tile1);
		boardMap.get(0).put(1, tile2);
		boardMap.get(1).put(0, tile3);
		boardMap.get(2).put(0, tile4);
		boardMap.get(2).put(-1, tile5);
		
		b = new Board(boardMap);
		
		move = new Move();
		move.addTile(tile1, 0, 0);
		move.addTile(tile2, 0, 1);
		
	
		b3 = new Board();
		
		
		b3.placeTile(tile1, 0, 0);
		b3.placeTile(tile2, 0, 1);
		b3.placeTile(tile3, 1, 0);
		b3.placeTile(tile4, 2, 0);
		b3.placeTile(tile5, 2, -1);
	
		
		
		t1 = new Tile(Color.RED, Shape.CLOVER);
		t2 = new Tile(Color.BLUE, Shape.CLOVER);
		t3 = new Tile(Color.PURPLE, Shape.CLOVER);
		t4 = new Tile(Color.ORANGE, Shape.CLOVER);
		t5 = new Tile(Color.YELLOW, Shape.CLOVER);
		t6 = new Tile(Color.GREEN, Shape.CLOVER);
		t7 = new Tile(Color.RED, Shape.SQUARE);
		t8 = new Tile(Color.RED, Shape.STAR);
		t9 = new Tile(Color.PURPLE, Shape.STAR);
		t10 = new Tile(Color.BLUE, Shape.SQUARE);
		t11 = new Tile(Color.BLUE, Shape.DIAMOND);
		t12 = new Tile(Color.RED, Shape.DIAMOND);
		t13 = new Tile(Color.ORANGE, Shape.CROSS);
		t14 = new Tile(Color.ORANGE, Shape.STAR);
	}
	
	@Test
	public void testContainsTile() {
		assertFalse(b.containsTile(-5, 3));
		assertFalse(b.containsTile(-100, 24));
		assertTrue(b.containsTile(0, 0));
		assertTrue(b.containsTile(1, 0));
		assertTrue(b.containsTile(0, 1));
		assertTrue(b.containsTile(2, -1));
		
		
	}
	
	@Test
	public void placeTile() {
		b.placeTile(tile7, 0, -1);
		
		assertTrue(b.containsTile(0, -1));
		assertEquals(tile7, b.getAllTiles().get(0).get(-1));

	}
	
	@Test
	public void getAllTiles() {
		assertEquals(boardMap, b.getAllTiles());
	}
	
	@Test
	public void isPlaceFree() {
		Move move2 = new Move();
		move2.addTile(tile6, 10, 10);
		move2.addTile(tile7, 10, 12);
		
		assertTrue(b.isPlaceFree(move2));
		
		move2.addTile(tile9, 0, 0);
		assertFalse(b.isPlaceFree(move2));
	}
	
	@Test 
	public void getTile() {
		assertEquals(tile4, b.getTile(2, 0));
		assertEquals(tile5, b.getTile(2, -1));
		assertNotEquals(tile4, b.getTile(2, -1));
		assertNotEquals(tile5, b.getTile(2, 0));
		assertEquals(null, b.getTile(100, 1));
		
	}
	
	@Test
	public void getBoardSize() {
		assertEquals(5, b.getBoardSize());
	}
	
	@Test
	public void getTileList() {
		assertEquals(tilesList, b.getTileList());
	}
	
	@Test
	public void canPlaceATile() {
		Board b2 = new Board();
		assertTrue(b2.canPlaceATile(tilesList));
		
		
		
		tilesList2.add(tile11);
		
		assertTrue(b3.canPlaceATile(tilesList2));
		
	}
	
	@Test
	public void isMoveConnected() {
		Board b4 = new Board();
		b4.doMove(move);
		
		Move move2 = new Move();
		move2.addTile(tile8, 0, 3);
		assertFalse(b4.isMoveConnected(move2));
		
		move2.addTile(tile7, 0, 2);
	
		assertTrue(b4.isMoveConnected(move2));
	
	
	
	}
	
	@Test
	public void doMove() {
		Board b4 = new Board();
		b4.doMove(move);
		assertEquals(tile1, b4.getTile(0, 0));
		assertEquals(tile2, b4.getTile(0, 1));
		
		//prepare the board
		Board b5 = new Board();
		
		Move move1 = new Move();
		move1.addTile(t1, 0, 2);
		move1.addTile(t2, 0, 1);
		move1.addTile(t3, 0, 0);
		move1.addTile(t4, 0, -1);
		move1.addTile(t5, 0, -2);
		move1.addTile(t6, 0, -3);
		b5.doMove(move1);
		
		Move move2 = new Move();
		move2.addTile(t7, -1, 2);
		move2.addTile(t8, -2, 2);
		b5.doMove(move2);
		
		Move move3 = new Move();
		move3.addTile(t9, -2, 1);
		b5.doMove(move3);
		
		Move move4 = new Move();
		move4.addTile(t10, 1, 1);
		move4.addTile(t11, 2, 1);
		b5.doMove(move4);
		
		Move move5 = new Move();
		move5.addTile(t12, 2, 2);
		b5.doMove(move5);
		
		Move move6 = new Move();
		move6.addTile(t13, -1, -1);
		move6.addTile(t14, -2, -1);
		b5.doMove(move6);
		
		//test the board
		
		assertEquals(t1, b5.getTile(0, 2));

		assertEquals(t9, b5.getTile(-2, 1));
		assertEquals(t10, b5.getTile(1, 1));
		
	}
	
	@Test
	public void checkMove() {
		
	}
	
	@Test
	public void canPlaceTile() {
		Board b4 = new Board();
		
		assertTrue(b4.canPlaceTile(tile1, 0, 0));
		
		
		Move move2 = new Move();
		move2.addTile(tile1, 0, 0);
		b4.doMove(move2);
		
		
		assertFalse(b4.canPlaceTile(tile2, 0, 0));
		assertFalse(b4.canPlaceTile(tile1, 0, 1));
		
		assertTrue(b4.canPlaceTile(tile2, 0, 1));
		assertTrue(b4.canPlaceTile(tile2, 0, -1));
		assertTrue(b4.canPlaceTile(tile2, 1, 0));
		assertTrue(b4.canPlaceTile(tile2, -1, 0));
		
		assertFalse(b4.canPlaceTile(tile5, 0, 1));
		assertFalse(b4.canPlaceTile(tile5, 0, -1));
		assertFalse(b4.canPlaceTile(tile5, 1, 0));
		assertFalse(b4.canPlaceTile(tile5, -1, 0));
		
		
		
		assertFalse(b4.canPlaceTile(tile5, 0, 1));
		
	
		
	}
	
	
	
}
