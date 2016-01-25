package ui;

import java.net.InetAddress;
import java.util.List;

import qwirkle.Tile;

public interface UI {
	
	// TODO more methods may be needed.
	
	public void showBoard();
	public void showHand(List<Tile> tiles);
	public void startup();
	public void showMessage(String msg);	
	public InetAddress getHost();
	public int getPort();
	public String getPlayer(int number);
	public int getPlayerCount();
	
	
}