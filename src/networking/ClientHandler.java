package networking;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ClientHandler implements Runnable {
	private Server server;
    private BufferedReader in;
    private BufferedWriter out;
    private String clientName;
    
    // List of protocol commands.
    private static final String CLIENT_IDENTIFY = "IDENTIFY";
    private static final String CLIENT_QUIT = "QUIT";
    private static final String CLIENT_QUEUE = "QUEUE";
    private static final String CLIENT_MOVE_PUT = "MOVE_PUT";
    private static final String CLIENT_MOVE_TRADE = "MOVE_TRADE";
    private static final String SERVER_IDENITFY = "IDENTIFYOK";
    private static final String SERVER_GAMESTART = "GAMESTART";
    private static final String SERVER_GAMEEND = "GAMEEND";
    private static final String SERVER_TURN = "TURN";
    private static final String SERVER_PASS = "PASS";
    private static final String SERVER_DRAWTILE = "DRAWTILE";
    private static final String SERVER_MOVE_PUT = "MOVEOK_PUT";
    private static final String SERVER_MOVE_TRADE = "MOVEOK_TRADE";
    private static final String SERVER_ERROR = "ERROR";
    /*private static final String CLIENT_CHAT = "CHAT";
    private static final String SERVER_CHAT = "CHATOK";
    private static final String CLIENT_CHALLENGE = "CHALLENGE";
    private static final String CLIENT_CHALLENGE_ACCEPT = "CHALLENGE_ACCEPT";
    private static final String CLIENT_CHALLENGE_DECLINE = "CHALLENGE_DECLINE";
    private static final String CLIENT_LEADERBOARD = "LEADERBOARD";
    private static final String SERVER_LEADERBOARD = "LEADERBOARDOK";
    private static final String CLIENT_LOBBY = "LOBBY";
    private static final String SERVER_LOBBY = "LOBBYOK";*/
    
    public ClientHandler(Server serverArg, Socket socketArg) throws IOException {
    	this.in = new BufferedReader(new InputStreamReader(socketArg.getInputStream()));
    	this.out = new BufferedWriter(new OutputStreamWriter(socketArg.getOutputStream()));
    	this.server = serverArg;    	
    }

	public void run() {
		try {
			while (true) {
				String input = in.readLine();
				if (input.startsWith(CLIENT_QUIT)) {
					break;
				} else if (input.startsWith(CLIENT_IDENTIFY)) {
					identification(input.substring(CLIENT_IDENTIFY.length()));
				} else if (input.startsWith(CLIENT_QUEUE)) {
					queue(input.substring(CLIENT_QUEUE.length()));
				}
			}
			
			
			
			
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public void sendMessage(String msg) {
    	try {
			out.write(msg + "\n");
			out.flush();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	private void shutdown() {
        server.removeHandler(this);
        //server.broadcast("[" + clientName + " has left]");
        try {
			in.close();
	        out.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }
    
    public void serverDisconnect() {
    	sendMessage("Server eshut down");
    }
    
    public String getName() {
    	return clientName;
    }
    
    public void identification(String input) {
    	clientName = input;
    	if (server.nameExists(clientName)) {
    		
    	}
    }
    
    public void queue(String input) {
    	String[] n = input.split(",");
    	for (String a : n) {
    		if (a == "1" || a == "2" || a == "3") {
    			server.addToQueue(this, a);
    		} else {
    			//throw new Error.QUEUE_INVALID;
    		}
    	}
    }
	
}
