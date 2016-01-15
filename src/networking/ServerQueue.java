package networking;

import java.util.ArrayList;
import java.util.List;

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
		
	}

}
