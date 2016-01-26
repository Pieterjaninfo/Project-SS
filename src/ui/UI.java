package ui;

import java.net.InetAddress;
import java.util.List;
import java.util.Map;

import qwirkle.Tile;

public interface UI {
	
	// TODO more methods may be needed.
	
	/**
	 * Shows the hand on the standard system output.
	 */
	public void showBoard(Map<Integer, Map<Integer, Tile>> tileMap);
	
	/**
	 * Shows the hand on the standard system output.
	 * @param tiles
	 */
	public void showHand(List<Tile> tiles);
	
	/**
	 * Asks the user what type of game he wants to play.
	 * Choice of:
	 * <ul>
	 * 		<li>Singleplayer</li>
	 * 		<li>Multiplayer</li>
	 * </ul>
	 */
	public void startup();
	
	/**
	 * Shows the message on the standard system output.
	 * @param msg Message printed to the standard system output
	 */
	public void showMessage(String msg);	
	
	/**
	 * Asks the user for the host address to connect to.
	 * @return the InetAddress
	 */
	public InetAddress getHost();
	
	/**
	 * Asks the user for the port to connect to
	 * @return the port as integer
	 */
	public int getPort();
	
	/**
	 * Asks for the name of a player.
	 * @param number Player number
	 * @return the name of the player
	 */
	public String getPlayer(int number);
	
	/**
	 * Asks for the amount of players.
	 * @return the amount of players
	 */
	public int getPlayerCount();
	
	/**
	 * Reads from standard system input after the message is shown.
	 * @param msg
	 * @return
	 */
	public String readLine(String msg);
	
	
}