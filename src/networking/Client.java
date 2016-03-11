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

import qwirkle.Tile;
import qwirkle.Board;
import qwirkle.Color;
import qwirkle.HumanPlayer;
import qwirkle.Player;
import qwirkle.Qwirkle;
import qwirkle.SocketPlayer;
import qwirkle.Move;
import qwirkle.Shape;
import ui.UI;

/**
 * Client class for the Quirkle game.
 * @author Bart Meyers
 */

public class Client extends Qwirkle implements Runnable {
	
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
	private HumanPlayer clientPlayer;
	private Board board;
    
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
			System.out.println("The connection has been lost.");
			shutdown();
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
		    	while (!in.ready()) {						//WHILE LOOP MAY NOT BE NEEDED
        			// Wait for an input from the server
		    		try {
						Thread.sleep(500);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
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
        		String queue = ui.readLine("Please enter the queues you want to enter." +
          			  "\nPossible queues: 2, 3 and 4.");
        		if (queue.matches(LIST_REGEX)) {
        			out.write(CLIENT_QUEUE + " " + queue);
            		while (!in.ready()) {
            			// Wait for an input from the server
            			try {
							Thread.sleep(500);
						} catch (InterruptedException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
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
    	String response;
    	String moveRegex = "^[mM][oO][vV][eE]\\s.+$";
    	String tradeRegex = "^[tT][rR][aA][dD][eE]\\s.+$";
    	
    	try {
			
    		while (running) {
    			
    			response = in.readLine();
    			
    			
				if (response.startsWith(SERVER_TURN) && response.endsWith(clientName)) {
					//it is my turn
					

					ui.showBoard(board.getAllTiles());
					ui.showHand(currentPlayer.getHand());
					//String move = ui.readLine("Make a move");
					Move moves = clientPlayer.determineMove();
					
					if (moves == null && firstMove) {
						//TRADE ON FIRST TURN EXCEPTION
					} else if (moves != null) {
						if (!clientPlayer.tilesInHand(moves) && bag.canTradeTiles.getTileList()) {
							
						}
					}
				}
					
					
					/*
					 * else if (!currentPlayer.tilesInHand(move) && bag.canTradeTiles(move.getTileList())) {
				ui.showMessage("You don't have some of the tiles you tried to place!");
					 */
					
					
					
					
					
					
					
					
					
					/*do {
						//check if user did a MOVE or TRADE
						moves = clientPlayer.determineMove();
						
						if (move.matches(moveRegex)) {
							//client move
							//String[] moves = move.substring(moveRegex.length() + 1).split(" ");
							
							out.write(CLIENT_MOVE_PUT + "move");
							
							
							
						} else if (move.matches(tradeRegex) && firstMove) {
							//THROW CAN'T TRADE ON TURN ONE EXCEPTION
							ui.showMessage("You can't trade on the first turn!");
						} else if (move.matches(tradeRegex)) {
							//client trade
							
						}
					} while (!move.matches(moveRegex) 
							  || !move.matches(tradeRegex) && !firstMove);
					

				} */	
				else {
					
					if (response.startsWith(SERVER_MOVE_PUT)) {
						firstMove = false;

						Move moves = stringToMove(response.substring(SERVER_MOVE_PUT.length() + 1));
						board.doMove(moves);
						
						
						
						
					}
					
					// wait until we can check again
				}
    		}

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
    	
    }
    
    /**
     * CHeck first move might be deleted tho.
     * @param move
     * @return
     */
    public boolean checkMoveClient(Move move) {		//TODO check if this guy's USELESS
    	if (move == null) {
    		return false;
    	}
    	

    	
    	return false;
    }
    
    
    public Move stringToMove(String move) {
    	Move moves = new Move();
		String[] moveArray = move.split(" ");
		for (String move1 : moveArray) {
			Tile tile = codeToTile(move1.split("@")[0]);
			int x = Integer.parseInt(move1.split("@")[1].split(",")[0]);
			int y = Integer.parseInt(move1.split("@")[1].split(",")[1]);
			moves.addTile(tile, x, y);
		}
    	return moves;
    }
    
    public void error(Error error) {
    	sendMessage(SERVER_ERROR + " " + error);
    }
    
    /**
     * Initiates all the players and gives the initial cards to the player.
     */
    public void gameStart() {
    	String input = "";
		
    	//Initiate all the players and add them to the players list
    	do {
			try {
				input = in.readLine();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} while (!input.startsWith(SERVER_GAMESTART));
		
		String[] inputArray = input.substring(SERVER_GAMESTART.length() + 1).split(" ");
		for (String playerName : inputArray) {
			Player player;
			if (playerName.equals(clientName)) {
				clientPlayer = new HumanPlayer(playerName, this);
				players.add(clientPlayer);
			} else {
				player = new SocketPlayer(playerName, this);
				players.add(player);
			}
		}
		
		//Give the tiles to player belonging to the client
		do {
			try {
				input = in.readLine();
				
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} while (!input.startsWith(SERVER_DRAWTILE));
		
		String[] inputTiles = input.substring(SERVER_DRAWTILE.length() + 1).split(" ");
		List<Tile> tilesList = new ArrayList<Tile>();
		
		for (String tileCode : inputTiles) {
			Tile tile = codeToTile(tileCode);
			tilesList.add(tile);
		}
		if (currentPlayer.getName().equals(clientName)) {
			currentPlayer.setStartingHand(tilesList);
		}
		
		firstMove = true;
		
    }
    

}
