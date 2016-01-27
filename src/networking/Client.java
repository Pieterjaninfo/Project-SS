package networking;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import qwirkle.Player;
import qwirkle.Qwirkle;
import qwirkle.SocketPlayer;

import ui.UI;

/**
 * Client class for the Quirkle game.
 * @author Bart Meyers
 */

public class Client implements Runnable {
	
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
	
    private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private boolean running = true;
	private String clientName;
	private UI ui;
	private List<Player> players = new ArrayList<Player>();
	private Player currentPlayer;
	private Boolean firstMove = true;
    
    public Client(InetAddress host, int port)
			throws IOException {
        try {
        	this.socket = new Socket(host, port);
            this.in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        	this.out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        } catch (java.net.ConnectException e) {
        	System.out.println("Couldn't connect to server");
        	e.printStackTrace();
        }
	}
    
    /**
     * Method to start the client.
     */
    public void begin(UI uiA) {
    	this.ui = uiA;
    	try {
			(new Thread(this)).start();
			do {
				Thread.sleep(500);
			} while (this.isRunning());
			this.shutdown();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}   	
    }
    
    
    
    @Override
	public void run() {
    	// TODO implement protocol and game.
		identify();  
		do {
			queue();
			gameStart();
			moves();
			
		} while (running);
		
	}
    
    /**
     * Print a message to the standard output.
     * @param message Message to be printed
     */
    private void print(String message) {
		ui.showMessage(message);
    	// TODO print to the UI.
	}
    
    /**
     * Send message to the ClientHandler from the server.
     * @param msg The message to be send
     */
    public void sendMessage(String msg) {
		try {
    		out.write(msg + "\n");
    		out.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
		}	
	}
    
    /**
     * Shuts down the server.
     */
    public void shutdown() {
		print("Closing socket connection...");
		try {
			running = false;
			out.close();
			in.close();
			socket.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
    
    /**
     * Returns if the server is running.
     * @return
     */
    public boolean isRunning() {
		return running;
	}
    
    /**
     * Quits the client.
     */
    public void quitClient() {
    	running = false;
    }
    
    /**
     * Reads from the socket and returns the input.
     * @return input string
     */
    public String readLine() {
		return clientName;
    	
    }
    
    public void identify() {
    	try {
			String response = "";
			String player = ui.getPlayer(5);
			do {
		    	out.write(CLIENT_IDENTIFY + " " + player);
		    	while (!in.ready()) {
        			// Wait for an input from the server
		    	}
		    	response = in.readLine();
		    	if (player.startsWith("AI") && response.startsWith(SERVER_ERROR)) {
		    		int i = 0;
		    		player = String.format("%s%s", player, i);
		    		i++;
		    	} else {
		    		ui.showMessage("Name incorrect or already taken.");
		    		player = ui.getPlayer(5);
		    	}
			} while (!response.equals(SERVER_IDENITFY));
			clientName = player;
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
    }
    
    public void queue() {
    	try {
    		String response = "";
        	do {
        		String queue = ui.readLine("Pleas enter the ques you want to enter." +
          			  "\nPossible queues: 2, 3 and 4.");
        		if (queue.matches(LIST_REGEX)) {
            		out.write(CLIENT_QUEUE + " " + queue);
            		while (!in.ready()) {
            			// Wait for an input from the server
            		}
            		response = in.readLine();
        		} else {
        			ui.showMessage("Incorrect queue format");
        		}
        	} while (!response.startsWith(SERVER_QUEUE));
        } catch (IOException e) {
        	e.printStackTrace();
        	//TODO exception catch
        }
    }
    
    public void moves() {
    	String input;
    	try {
			input = in.readLine();
			if (input.startsWith(SERVER_MOVE_PUT)) {
				
			} else if (input.startsWith(SERVER_PASS)) {
				
			} else if (input.startsWith(SERVER_MOVE_TRADE)) {
				
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	
    }
    
    public void error(Error error) {
    	sendMessage(SERVER_ERROR + " " + error);
    }
    
    public void gameStart() {
    	String input = "";
		try {
			input = in.readLine();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    	if (input.startsWith(SERVER_GAMESTART)) {
    		String[] in = input.substring(SERVER_GAMESTART.length() + 1).split(" ");
    		for (String playerName : in) {
    			Player player = new SocketPlayer(playerName, this);
    			
    		}
    	} else {
    		error(Error.INVALID_COMMAND);
    	}
    }
}
