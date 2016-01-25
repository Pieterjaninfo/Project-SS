package networking;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;

import ui.UI;

/**
 * Client class for the Quirkle game.
 * @author Bart Meyers
 */

public class Client implements Runnable{
	
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
    public void begin(UI ui) {
    	this.ui = ui;
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
		try {
	    	out.write(CLIENT_IDENTIFY + ui.getPlayer(1)); // TODO if name AI is already in use add a number to the end...
	    	
			in.readLine();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}    	
		
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
    
    public void quitClient() {
    	running = false;
    }
    
    
}
