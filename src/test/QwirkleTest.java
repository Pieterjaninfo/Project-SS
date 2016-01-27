package test;

//import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import qwirkle.Color;
import qwirkle.HumanPlayer;
import qwirkle.Player;
import qwirkle.Qwirkle;
import qwirkle.Shape;
import qwirkle.Tile;


public class QwirkleTest {

	Qwirkle game;
	Player a;
	Player b;
	Tile tile1;
	Tile tile2;
	
	@Before
	public void setUp() {
		game = new Qwirkle();
		a = new HumanPlayer("a", game);
		b = new HumanPlayer("b", game);
		tile1 = new Tile(Color.BLUE, Shape.CIRCLE);
		tile2 = new Tile(Color.GREEN, Shape.CIRCLE);
		List<Tile> tiles1 = new ArrayList<Tile>();
		List<Tile> tiles2 = new ArrayList<Tile>();
		tiles1.add(tile1);
		tiles2.add(tile2);
		a.addTile(tiles1);
		b.addTile(tiles2);

	}
	
	@Test
	public void makeStringMoveTest() {
		String testString = game.tileToCode(tile1) + "@0,0";
		game.makeMove(testString);
	}
	
}
