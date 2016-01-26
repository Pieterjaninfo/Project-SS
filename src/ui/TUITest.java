package ui;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
		Map<Integer, Tile> y1 = new HashMap<Integer, Tile>();
		Map<Integer, Tile> y2 = new HashMap<Integer, Tile>();
		Map<Integer, Tile> y3 = new HashMap<Integer, Tile>();

		Map<Integer, Map<Integer, Tile>> res = new HashMap<Integer, Map<Integer, Tile>>();
		y1.put(0, tile1);
		y1.put(1, tile2);
		y1.put(2, tile2);
		y1.put(-2, tile2);
		res.put(0, y1);
		y2.put(0, tile2);
		res.put(-1, y2);
		

		ui.showHand(testList);
		
		
		System.out.printf("%s\n", res);

		ui.showBoard(res);
		
		y3.put(0, tile1);
		y3.put(-1, tile1);
		res.put(-3, y3);
		ui.showHand(testList);

		ui.showBoard(res);
	}

}
