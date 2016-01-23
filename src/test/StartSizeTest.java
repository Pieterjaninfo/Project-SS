package test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import qwirkle.Color;
import qwirkle.Player;
import qwirkle.Qwirkle;
import qwirkle.ServerSocketPlayer;
import qwirkle.Shape;
import qwirkle.Tile;

public class StartSizeTest {
	
	private Player a;
	
	@Before
	public void setUp() {
		List<Tile> list = new ArrayList<Tile>();
		list.add(new Tile(Color.BLUE, Shape.CIRCLE));
		list.add(new Tile(Color.GREEN, Shape.CIRCLE));
		list.add(new Tile(Color.BLUE, Shape.CIRCLE));
		list.add(new Tile(Color.RED, Shape.CIRCLE));
		list.add(new Tile(Color.BLUE, Shape.CIRCLE));
		list.add(new Tile(Color.GREEN, Shape.SQUARE));
		Qwirkle game = new Qwirkle();
		 a = new ServerSocketPlayer("Test", game);
		 a.setStartingHand(list);
 	}
	
	@Test
	public void Testduplicate() {
		assertEquals(4, a.largestStartSize());
	}
	
}
