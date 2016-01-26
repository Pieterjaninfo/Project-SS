package networking;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

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
    	if (n.equals("2")) {
    		twoPlayer.add(client);
    	} else if (n.equals("3")) {
    		threePlayer.add(client);
    	} else if (n.equals("4")) {
    		fourPlayer.add(client);
    	}
    	System.out.println(fourPlayer.size() + "; " + threePlayer.size() + "; " + twoPlayer.size());
    }
		
	/**
	 * Starts a game of x players when the queue for x players has x players.
	 */
	@Override
	public void run() {
		Qwirkle game = null;
		while (true) {
			List<ClientHandler> players = null;
			if (fourPlayer.size() >= 4) {
				players = new Vector<ClientHandler>(fourPlayer.subList(0, 3));
				game = new Qwirkle(players);
				fourPlayer.removeAll(players);
				(new Thread(game)).start();
			} else if (threePlayer.size() >= 3) {
				players = new Vector<ClientHandler>(threePlayer.subList(0, 2));
				
				game = new Qwirkle(players);
				threePlayer.removeAll(players);
				(new Thread(game)).start();
			} else if (twoPlayer.size() >= 2) {
				players = new Vector<ClientHandler>(twoPlayer.subList(0, 1));
				game = new Qwirkle(players);
				twoPlayer.removeAll(players);
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
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
}
