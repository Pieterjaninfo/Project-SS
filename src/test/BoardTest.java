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
		
		Move move = new Move();
		
	
		b3 = new Board();
		
		
		b3.placeTile(tile1, 0, 0);
		b3.placeTile(tile2, 0, 1);
		b3.placeTile(tile3, 1, 0);
		b3.placeTile(tile4, 2, 0);
		b3.placeTile(tile5, 2, -1);
	
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
		Move move = new Move();
		move.addTile(tile6, 10, 10);
		move.addTile(tile7, 10, 12);
		
		assertTrue(b.isPlaceFree(move));
		
		move.addTile(tile9, 0, 0);
		assertFalse(b.isPlaceFree(move));
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
		
	}
	
	@Test
	public void doMove() {
		
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
		
	//yay
		
	}
	
	
	
}
