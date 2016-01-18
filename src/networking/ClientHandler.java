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
	private static final String SERVER_IDENTIFY = null;
    
    public ClientHandler(Server serverArg, Socket socketArg) throws IOException {
    	this.in = new BufferedReader(new InputStreamReader(socketArg.getInputStream()));
    	this.out = new BufferedWriter(new OutputStreamWriter(socketArg.getOutputStream()));
    	this.server = serverArg;    	
    }

    /**
     * Will read the input from the client and starts the operation according to the protocol.
     */
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
				} else if (input.startsWith(CLIENT_MOVE_PUT)) {
					
				} else if (input.startsWith(CLIENT_MOVE_TRADE)) {
					
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	/**
	 * Sends the message to the client.
	 * @param msg message to be send to the client
	 */
	public void sendMessage(String msg) {
    	try {
			out.write(msg);
			out.newLine();
			out.flush();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	/**
	 * Shuts down the connection with this client and shuts down this ClientHandler.
	 */
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
    
	/**
	 * Sends a message to the clients if the server is disconnected.
	 */
    public void serverDisconnect() {
    	sendMessage("Server shut down");
    }
    
    /**
     * Returns the name of the client that belongs to the ClientHandler.
     * @return
     */
    public String getName() {
    	return clientName;
    }
    
    /**
     * Sets the input to be the clientName.
     * @param input
     */
    public void identification(String input) {
    	if (input.matches("[a-zA-Z0-9-_]{2,16}")) {
    		sendMessage(SERVER_ERROR + " " + Error.NAME_INVALID);
    	} else {
    		if (server.nameExists(clientName)) {
        		sendMessage(SERVER_ERROR + " " + Error.NAME_USED);
        	} else {
            	clientName = input;
            	sendMessage(SERVER_IDENTIFY);
        	}
    	} 
    }
    
    /**
     * adds the client from this ClientHandler to the queues that are given as input.
     * @param input The queues the client wants to enter, comma separated values
     */
    public void queue(String input) {
    	String[] n = input.split(",");
    	for (String a : n) {
    		if (a == "1" || a == "2" || a == "3") {
    			server.addToQueue(this, a);
    		} else {
    			sendMessage(SERVER_ERROR + " " + Error.QUEUE_INVALID);
    		}
    	}
    }
	
}
