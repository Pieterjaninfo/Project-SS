package networking;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

/**
 * Server class that will run the server for Quirkle games.
 * @author Bart Meyers
 *
 */

public class Server implements Runnable {

	private static final String USAGE
		   = "usage: " + Server.class.getName() + " <port>";
	private static ServerQueue queue = new ServerQueue();


	/**
	 * Start the server and ask the user for the port number.
	 * If the user types exit the server will exit.
	 * @param args
	 */
	public static void main(String[] args) {
    	System.out.println("to exit server type 'exit'");
		String portnumber = "";
		do {
			try {
				System.out.println("Please enter port number:");
				BufferedReader in = new BufferedReader(new InputStreamReader(
		                System.in));
				portnumber = in.readLine();
				if (portnumber.matches("^[0-9]{0,4}$")) {
					try {
						Server server = new Server(Integer.parseInt(portnumber));
						(new Thread(queue)).start();
						(new Thread(server)).start();
						System.out.println("Server started");
						server.exit();
						server.shutdown();
					} catch (NumberFormatException e) {
						System.out.println(USAGE);
						System.out.println("ERROR: port " + portnumber
							 	  + " is not an invalid port");
						//e.printStackTrace();
					}
				} else if (portnumber.equals("exit")) {
					System.exit(0);
				} else {
					System.out.println(USAGE);
				}
				
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
		} while (true);
		
		/*
		if (args.length != 1) {
			System.out.println(USAGE);
			System.exit(0);
		}
		try {
			Server server = new Server(Integer.parseInt(args[0]));
			(new Thread(queue)).start();
			(new Thread(server)).start();
			server.exit();
			server.shutdown();
		} catch (NumberFormatException e) {
			System.out.println(USAGE);
			System.out.println("ERROR: port " + args[1]
				 	  + " is not an integer");
			//e.printStackTrace();

			System.exit(0);
		}*/
	}

	private int port;
    private List<ClientHandler> threads;
    private ServerSocket ssock = null;
    private Socket sock = null;
    private static boolean running = true;
	    
    /** 
     * Constructs a new Server object. 
     */
    public Server(int portArg) {
    	this.port = portArg;
    	threads = new ArrayList<ClientHandler>();

    	
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
    	//System.out.println("to exit server type 'exit'");
        String antw = null;
        while (running) {
        	try {
                BufferedReader in = new BufferedReader(new InputStreamReader(
	                        System.in));
                antw = in.readLine();
            } catch (IOException e) {
				e.printStackTrace();
            }
        	if (antw.equals("exit")) {
            	running = false;
            }
        }
        
        
        System.exit(0);
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
    
    /**
     * Adds a handler to the handlerlist.
     * @param handler
     */
	//@ requires handler != null;
	public void addHandler(ClientHandler handler) {
    	threads.add(handler);
    } 
	
	/**
	 * Removes handler from the handlerlist.
	 * @param handler
	 */
	//@ requires handler != null;
    public void removeHandler(ClientHandler handler) {
    	queue.removeClient(handler);
    	threads.remove(handler);
    }
    
    /**
     * Checks if the name is already in use on this server.
     * @param name
     * @return
     */
    //@ requires name != null;
    public boolean nameExists(String name, ClientHandler client) {
    	Vector<ClientHandler> threadsCopy = new Vector<ClientHandler>(threads);
    	threadsCopy.remove(client);
    	for (ClientHandler a : threadsCopy) {
    		if (threadsCopy.isEmpty()) {
    			return false;
    		} else if (name.equals(a.getName())) {
    			return true;
    		}
    		
    	}
    	return false;
    }
    
    /**
     * Adds the client in the specified queue.
     * @param client
     * @param n
     */
	public void addToQueue(ClientHandler client, String n) {
		queue.addToQueue(client, n);
    }
	
	public void gameBroadcast(List<ClientHandler> gameClients, String msg) {
		for (ClientHandler client : gameClients) {
			client.sendMessage(msg);
		}
	}
    
}
