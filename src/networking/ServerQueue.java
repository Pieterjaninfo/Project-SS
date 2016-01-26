package networking;

import java.util.ArrayList;
import java.util.List;

import qwirkle.Qwirkle;

/**
 * Class to check the queue for games.
 * @author Bart Meyers
 *
 */

public class ServerQueue implements Runnable {
	
	private List<ClientHandler> twoPlayer;
    private List<ClientHandler> threePlayer;
    private List<ClientHandler> fourPlayer;
    
    ServerQueue() {
    	twoPlayer = new ArrayList<ClientHandler>();
    	threePlayer = new ArrayList<ClientHandler>();
    	fourPlayer = new ArrayList<ClientHandler>();
    }

	/**
	 * Adds the client to the specified queue.
	 * @param client
	 * @param n
	 */
	public void addToQueue(ClientHandler client, String n) {
    	if (n == "1") {
    		twoPlayer.add(client);
    	} else if (n == "2") {
    		threePlayer.add(client);
    	} else if (n == "3") {
    		fourPlayer.add(client);
    	} else {
    		client.error(Error.QUEUE_INVALID);
    	}
    }
		
	/**
	 * Starts a game of x players when the queue for x players has x players.
	 */
	@Override
	public void run() {
		Qwirkle game = null;
		while (true) {
			List<ClientHandler> players = null;
			if (fourPlayer.size() > 4) {
				players = fourPlayer.subList(0, 3);
				game = new Qwirkle(players);
				(new Thread(game)).start();
			} else if (threePlayer.size() > 3) {
				players = fourPlayer.subList(0, 2);
				game = new Qwirkle(players);
				(new Thread(game)).start();
			} else if (twoPlayer.size() > 2) {
				players = fourPlayer.subList(0, 1);
				game = new Qwirkle(players);
				(new Thread(game)).start();
			}
			if (players != null && game != null) {
				String names = "";
				for (ClientHandler client : players) {
					names = String.format("%s %s", names, client.getName());
				}
				for (ClientHandler client : players) {
					client.gameStart(names, game);
				}
			}
		}
	}
}
