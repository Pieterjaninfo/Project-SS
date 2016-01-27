package test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;
import qwirkle.Bag;
import qwirkle.Tile;

public class BagTest {
	private Bag bag;
	
	@Before
	public void setUp() {
		bag = new Bag();
	}
	
	@Test
	public void startSize() {
		assertEquals(108, bag.getSize());
	}	
	
	@Test
	public void sizeAfterStart() {
		assertEquals(6, bag.giveStartingHand().size());
		assertEquals(102, bag.getSize());
	}
	
	@Test
	public void getTilesAmountTest() {
		int amount = 4;
		assertEquals(amount, bag.getTiles(amount).size());
	}
	
	@Test
	public void tradeTilesTest() {
		List<Tile> hand = new ArrayList<Tile>();
		hand = bag.giveStartingHand();
		assertEquals(hand.size(), bag.tradeTiles(hand).size());
		assertEquals(6, hand.size());
	}
	
	@Test
	public void getTilesTest() {
		assertEquals(bag.getSize(), bag.getTiles().size());
	}

}
