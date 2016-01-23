package test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import qwirkle.Bag;

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

}
