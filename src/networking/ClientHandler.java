package networking;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.List;

import qwirkle.Qwirkle;

public class ClientHandler implements Runnable {
	private Server server;
    private BufferedReader in;
    private BufferedWriter out;
    private String clientName = null;
    
    // List of protocol commands.
    private static final String CLIENT_IDENTIFY = "IDENTIFY";
    private static final String CLIENT_QUIT = "QUIT";
    private static final String CLIENT_QUEUE = "QUEUE";
    private static final String CLIENT_MOVE_PUT = "MOVE_PUT";
    private static final String CLIENT_MOVE_TRADE = "MOVE_TRADE";
    private static final String SERVER_IDENITFY = "IDENTIFYOK";
    private static final String SERVER_QUEUE = "QUEUEOK";
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
	private static final String NAME_REGEX = "^[A-Za-z0-9-_]{2,16}$";
    private static final String LIST_REGEX = "^\\w+(,\\w+)*$";
    
    private Boolean moveExpected = false;
    private Qwirkle game;
    
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
				} else if (input.startsWith(CLIENT_IDENTIFY) && clientName == null) {
					identification(input.substring(CLIENT_IDENTIFY.length()) + 1);
				} else if (clientName == null) {
					error(Error.ILLEGAL_STATE);
				} else if (input.startsWith(CLIENT_QUEUE)) {
					queue(input.substring(CLIENT_QUEUE.length()));
				} else if (input.startsWith(CLIENT_MOVE_PUT) && moveExpected) {
					game.makeMove(input.substring(CLIENT_MOVE_PUT.length()));
				} else if (input.startsWith(CLIENT_MOVE_TRADE) && moveExpected) {
					game.tradeMove(input.substring(CLIENT_MOVE_TRADE.length()));
				} else {
					error(Error.ILLEGAL_STATE);
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		shutdown();
	}
	
	/**
	 * Sends the message to the client.
	 * @param msg Message to be send to the client
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
    /* pure */ public String getName() {
    	return clientName;
    }
    
    /**
     * Sets the input to be the clientName.
     * @param input
     */
    //@ requires input != null; input.matches("[a-zA-Z0-9-_]{2,16}")
    public void identification(String input) {
    	if (input.matches(NAME_REGEX)) {
    		error(Error.NAME_INVALID);
    	} else {
    		if (server.nameExists(clientName)) {
        		error(Error.NAME_USED);
        	} else {
            	clientName = input;
            	sendMessage(SERVER_IDENITFY);
        	}
    	} 
    }
    
    /**
     * adds the client from this ClientHandler to the queues that are given as input.
     * @param input The queues the client wants to enter, comma separated values
     */
    // requires input != null;
    public void queue(String input) {
    	String[] n = input.split(",");
    	Boolean goodQueue = true;
    	for (String a : n) {
    		if (a == "1" || a == "2" || a == "3") {
    			
    		} else {
    			error(Error.QUEUE_INVALID);
    			goodQueue = false;
    			break;
    		}
    	}
    	if (goodQueue) {
    		for (String a : n) {
            	server.addToQueue(this, a);
        	}
    		sendMessage(SERVER_QUEUE);
    	}
    }
    
    public void error(Error error) {
    	sendMessage(SERVER_ERROR + " " + error);
    }
	
    public void gameStart(String msg, Qwirkle game) {
    	sendMessage(SERVER_GAMESTART + " " + msg);
    	this.game = game;
    }
    
    public void gameBroadcast(List<ClientHandler> gameClients, String msg) {
    	server.gameBroadcast(gameClients, msg);
    }
    
    public void turn(List<ClientHandler> gameClients, String playerName) {
    	gameBroadcast(gameClients, SERVER_TURN + " " + playerName);
    	moveExpected = true;
    }
}
