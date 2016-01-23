package networking;

import java.util.ArrayList;
import java.util.List;

import qwirkle.Qwirkle;

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
		while (true) {
			if (fourPlayer.size() > 4) {
				List<ClientHandler> players = fourPlayer.subList(0, 3);
				(new Thread(new Qwirkle(players))).start();
				// TODO start a game with four of the players (first four in the list)
			} else if (threePlayer.size() > 3) {
				List<ClientHandler> players = fourPlayer.subList(0, 2);
				(new Thread(new Qwirkle(players))).start();
				// TODO start a game with three of the players (first three in the list)
			} else if (twoPlayer.size() > 2) {
				List<ClientHandler> players = fourPlayer.subList(0, 1);
				(new Thread(new Qwirkle(players))).start();
				String names = "";
				for (ClientHandler client : players) {
					names.format("%s %s", names, client.getName());
				}
				for (ClientHandler client : players) {
					client.gameStart(names);
				}
				// TODO start a game with two of the players (first two in the list)
			}
		}
	}

}
