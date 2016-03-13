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
		    	System.out.println(player);
				out.write(CLIENT_IDENTIFY + " " + player);
				out.newLine();
		    	out.flush();
		    	/*while (!in.ready()) {						//WHILE LOOP MAY NOT BE NEEDED
        			// Wait for an input from the server
		    		try {
						Thread.sleep(500);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
		    	}*/
		    	response = in.readLine();
		    	if (player.startsWith("AI") && response.startsWith(SERVER_ERROR)) {
		    		int i = 0;
		    		player = String.format("%s%s", player, i);
		    		i++;
		    	} else if (response.startsWith(SERVER_ERROR)) {
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
        			out.newLine();
        			out.flush();
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
        	ui.showMessage("Entered the queue correctly.");
        } catch (IOException e) {
        	e.printStackTrace();
        	//TODO exception catch
        }
    }
    
    /**
     * Asks the client user for input and executes it, and receives commands.
     */
    public void moves() {
    	String response = "";
    	//String moveRegex = "^[mM][oO][vV][eE]\\s.+$";
    	//String tradeRegex = "^[tT][rR][aA][dD][eE]\\s.+$";
    	String moves;
	
		while (running) {
			try {
				response = in.readLine();		//TODO only execute when something new is written
			} catch (IOException e1) {
				ui.showMessage("Connection has been lost.");
			}
			
			if (response.startsWith(SERVER_PASS)) {
				ui.showMessage("Passing turn");
			} else if (response.startsWith(SERVER_TURN) && response.endsWith(clientName)) {
				//it is my turn
				ui.showMessage("=====IT IS YOUR TURN=====");
				ui.showBoard(board.getAllTiles());
				ui.showHand(clientPlayer.getHand());
				//String move = ui.readLine("Make a move");
				
				while (true) {
					moves = clientPlayer.clientDetermineMove();
					if (moves.startsWith("move")) {
						//it was a move
						//check if move is valid and send to the client
						Move move = stringcodeToMove(moves.substring(5));
						if (!clientPlayer.tilesInHand(move)) {
							// ERROR TILES NOT OWNED
							error(Error.MOVE_TILES_UNOWNED);
						} else if (!board.checkMove(move)) {
							// ERROR MOVE NOT VALID
							error(Error.MOVE_INVALID);
						} else {
							// send the move to the server
							try {
								out.write(CLIENT_MOVE_PUT + stringToMoveString(moves.substring(4)));
								out.newLine();
								out.flush();
							} catch (IOException e) {
								e.printStackTrace();
							}
							clientPlayer.removeTile(move.getTileList());	  //TODO not correct fix
							break;
						}
					} else if (moves.startsWith("trade")) {
						//it was a trade
						List<Tile> handTiles = inputTileToCode(moves.substring(6));
						if (!clientPlayer.tilesInHand(handTiles)) {
							// ERROR TILES NOT OWNED
							error(Error.MOVE_TILES_UNOWNED);	
						} else if (board.getBoardSize() == 0) {
							error(Error.TRADE_FIRST_TURN);
						} else {
							try {
								out.write(CLIENT_MOVE_TRADE + " " + tilelistToCode(handTiles));
								out.newLine();
								out.flush();
							} catch (IOException e) {
								e.printStackTrace();
							}
							String tradeResponse = "";
							try {
								tradeResponse = in.readLine();
							} catch (IOException e) {
								e.printStackTrace();
							}
							
							if (tradeResponse.startsWith(SERVER_MOVE_TRADE)) {
								clientPlayer.removeTile(handTiles);
								break;
							}
						}
						
					} else {
						try {
							out.write(CLIENT_QUIT);
							out.newLine();
							out.flush();
						} catch (IOException e) {
							e.printStackTrace();
						}
						running = false;
					}
				}
			} else if (response.startsWith(SERVER_MOVE_PUT)) {
				// place the tiles on the board.
				Move move = stringToMove(response.substring(SERVER_MOVE_PUT.length() + 1));
				board.doMove(move);
				
			} else if (response.startsWith(SERVER_GAMEEND)) {
				running = false; // TODO ask for continuation
			} else if (response.startsWith(SERVER_DRAWTILE)) {
				List<Tile> tiles = stringToTiles(response.substring(SERVER_DRAWTILE.length() + 1));
				clientPlayer.addTile(tiles);
			}
		}
    }
    
    
    /*
     * Converts the raw input tile string into a list of tiles.
     */
    private List<Tile> inputTileToCode(String input) {
    	List<Tile> tileList = new ArrayList<Tile>();
		String[] tiles = input.split(" ");
		System.out.println(input);
		for (String tileString : tiles) {
			System.out.println(tileString);
			Shape shape = Shape.charToEnum(tileString.charAt(1));
			Color color = Color.toEnum(Character.digit(tileString.charAt(0), 10));
			Tile tile = new Tile(color, shape);
			tileList.add(tile);
		}
		return tileList;
    }
    
    /*
     * Converts all tiles in the list into a server code and puts it into one string.
     */
    private String tilelistToCode(List<Tile> tiles) {
    	String result = "";
    	for (Tile tile : tiles) {
    		result = String.format("%s %d", result,
    				tile.getColor().toInt() * 6 + tile.getShape().toInt());
    	}
    	System.out.println(result.trim());
		return result.trim();
	}
    
   /*
    * Converts the string of tiles codes into a list of tiles of type Tile.
    */
    private List<Tile> stringToTiles(String tileString) {			//TODO irrelevant?
    	List<Tile> tilesList = new ArrayList<Tile>();
		String[] tiles = tileString.split(" ");
		for (String aTile : tiles) {
			Tile tile = codeToTile(aTile);
			tilesList.add(tile);
		}
		return tilesList;
    }
    
    /*
     * Converts the string of move codes into a move with type Move.
     */
    private Move stringToMove(String move) {
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
    
    /*
     * Converts the string of move codes into a move with type String.
     */
    private String stringToMoveString(String move) {
		String result = "";
    	String[] moveArray = move.trim().split(" ");
    	System.out.println("move = " + move);
		for (String move1 : moveArray) {
			System.out.println("first move part = " + move1);
			String tile = tileToCode(codeToTile(tilelistToCode(inputTileToCode(move1.split("@")[0])).trim()));
			int x = Integer.parseInt(move1.split("@")[1].split(",")[0]);
			int y = Integer.parseInt(move1.split("@")[1].split(",")[1]);
			result = String.format("%s %s@%d,%d", result, tile, x, y);
		}
    	return result;
    }
    
    /*
     * Converts the raw string of move codes into a move with type Move.
     */
    private Move stringcodeToMove(String move) {
    	Move moves = new Move();
		String[] moveArray = move.split(" ");
		for (String move1 : moveArray) {
			Tile tile = codeToTile(tilelistToCode(inputTileToCode(move1.split("@")[0])).trim());
			int x = Integer.parseInt(move1.split("@")[1].split(",")[0]);
			int y = Integer.parseInt(move1.split("@")[1].split(",")[1]);
			moves.addTile(tile, x, y);
		}
    	return moves;
    }
    
    /**
     * Displays the given error to the user.
     * @param error The error which needs to be displayed
     */
    public void error(Error error) {
    	ui.showMessage(error.toString());
    }
    
    /**
     * Initiates all the players and gives the initial cards to the player.
     */
    public void gameStart() {
    	board = new Board();
    	String input = "";
		
    	//Initiate all the players and add them to the players list
    	do {
			try {
				input = in.readLine();
			} catch (IOException e) {
				ui.showMessage("The server disconnected.");
				this.shutdown();
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
		
		System.out.println(input.substring(SERVER_DRAWTILE.length() + 1));		//TODO remove

		List<Tile> tilesList = stringToTiles(input.substring(SERVER_DRAWTILE.length() + 1));
		System.out.println("finished making tiles list");						//TODO remove
		clientPlayer.setStartingHand(tilesList);
		System.out.printf("Player: %s with hand: %s ", clientPlayer.getName(), 	//TODO remove
				  input.substring(SERVER_DRAWTILE.length() + 1));
		firstMove = true;
		
    }
    

}





