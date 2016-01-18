package networking;

import java.util.ArrayList;
import java.util.List;

/**
 * Class to check the queue for games.
 * @author Bart Meyers
 *
 */

public class ServerQueue implements Runnable{
	
	private List<ClientHandler> twoPlayer;
    private List<ClientHandler> threePlayer;
    private List<ClientHandler> fourPlayer;
    
    ServerQueue() {
    	twoPlayer = new ArrayList();
    	threePlayer = new ArrayList();
    	fourPlayer = new ArrayList();
    }

	
	public void addToQueue(ClientHandler client, String n) {
    	if (n == "1") {
    		twoPlayer.add(client);
    	} else if (n == "2") {
    		threePlayer.add(client);
    	} else {
    		fourPlayer.add(client);
    	}
    }
		
	@Override
	public void run() {
		while (true) {
			if (fourPlayer.size() > 4) {
				// TODO start a game with four of the players (first four in the list)
			} else if (threePlayer.size() > 3) {
				// TODO start a game with three of the players (first three in the list)
			} else if (twoPlayer.size() > 2) {
				// TODO start a game with two of the players (first two in the list)
			}
		}
	}

}
