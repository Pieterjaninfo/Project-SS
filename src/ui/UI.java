package ui;

import java.net.InetAddress;

public interface UI {
	
	// TODO more methods may be needed.
	
	public void showBoard();
	public void showHand();
	public void startup();
	public void showError(String msg);	
	public InetAddress getHost();
	public int getPort();
	public String getPlayer(int number);
	public int getPlayerCount();
	
	
}