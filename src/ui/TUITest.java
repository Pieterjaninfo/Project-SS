package ui;

import java.util.ArrayList;
import java.util.List;

import qwirkle.*;

public class TUITest {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		Qwirkle game = new Qwirkle();
		UI ui = new TUI(game);
		List<Tile> testList = new ArrayList<Tile>();
		Tile tile1 = new Tile(Color.GREEN, Shape.STAR);
		Tile tile2 = new Tile(Color.BLUE, Shape.CIRCLE);
		testList.add(tile1);
		testList.add(tile2);
		testList.add(tile1);
		testList.add(tile1);
		testList.add(tile1);
		testList.add(tile1);

		ui.showHand(testList);

	}

}
