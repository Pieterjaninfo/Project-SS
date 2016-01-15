package networking;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import util.*;

public class Server implements Runnable {

	private static final String USAGE
		   = "usage: " + Server.class.getName() + " <port>";

	/** Start the Server-application. */
	public static void main(String[] args) {
		if (args.length != 1) {
			System.out.println(USAGE);
			System.exit(0);
		}
		try {
			Server server = new Server(Integer.parseInt(args[0]));	
			(new Thread(server)).start();
			server.exit();
			server.shutdown();
		} catch (NumberFormatException e) {
			System.out.println(USAGE);
			System.out.println("ERROR: port " + args[1]
				 	  + " is not an integer");
			e.printStackTrace();

			System.exit(0);
		}
	}

	private int port;
    private List<ClientHandler> threads;
    private ServerSocket ssock = null;
    private Socket sock = null;
    private static boolean running = true;
	    
    /** Constructs a new Server object. */
    public Server(int portArg) {
    	this.port = portArg;
    	threads = new ArrayList();

    	
    	try {
			ssock = new ServerSocket(port);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }
	    
	    /**
	     * if 'exit' is entered in the standard input the server will exit.
	     */
    public void exit() {
    	System.out.println("to exit server type 'exit'");
        String antw = null;
        while (running) {
        	try {
                BufferedReader in = new BufferedReader(new InputStreamReader(
	                        System.in));
                antw = in.readLine();
            } catch (IOException e) {
				e.printStackTrace();
            }
        }
        if (antw.equals("exit")) {
        	running = false;
        }
    }
    
    /**
     * Shuts down the server.
     */
    public void shutdown() {
    	try {
    		for (ClientHandler a : threads) {
        		a.serverDisconnect();
        	}
			ssock.close();
	    	sock.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NullPointerException e) {
			e.printStackTrace();

		}
    	System.exit(0);
    }
	    
    /**
     * Waits for clients to connect until the server is closed.
     */
    public void run() {
        try {
        	while (running) {
    			sock = ssock.accept();
    			ClientHandler client = new ClientHandler(this, sock);
    			this.addHandler(client);   
    			(new Thread(client)).start();
        	}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }
	    
	    /**
	     * Prints the message to the standard output.
	     * @param message
	     */
    public void print(String message) {
        System.out.println(message);
    }
	    
	public void addHandler(ClientHandler handler) {
    	threads.add(handler);
    } 
	    
    public void removeHandler(ClientHandler handler) {
    	threads.remove(handler);
    }
    
    public boolean nameExists(String name) {
    	Vector<ClientHandler> threadsCopy = new Vector(threads);
    	for (ClientHandler a : threadsCopy) {
    		if (a.getName().equals(name)) {
    			return true;
    		}
    	}
    	return false;
    }
    
    addToQueue() {
    	
    }
    
}
