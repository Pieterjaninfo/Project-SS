package ui;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Scanner;

import qwirkle.Qwirkle;
import qwirkle.Tile;

/**
 * Textual user interface for the Qwirkle game.
 * @author Bart Meyers
 *
 */
public class TUI implements UI {
	
	private static final String HORIZONTAL_SEPERATOR = "+----";

	private Scanner input; 
	private Qwirkle game;
	private InetAddress host;

	
	public TUI(Qwirkle game) {
		this.game = game;
	}
	
	/**
	 * Shows the current board.
	 */
	@Override
	public void showBoard() {
		// TODO Auto-generated method stub
		
	}

	/**
	 * Ask user for the type of game. Choice from:
	 * 1. Singleplayer
	 * 2. Multiplayer
	 */
	@Override
	public void startup() {
		input = new Scanner(System.in);
		System.out.printf("Enter number for choice:\n1. Singleplayer\n2. Multiplayer\n");
		while (true) {
			String command = input.nextLine();
			if (command.equals("1")) {
				game.startSingleplayer();
				break;
			} else if (command.equals("2")) {
				game.startMultiplayer();
				break;
			} else if (command.equals("exit")) {
				System.exit(0);
			} else {
				System.out.println("invalid choice");
			}
		}
		// TODO startup prints and reads, simple implementation needs improvement?
	}

	/**
	 * Print the error message to the output.
	 */
	@Override
	public void showMessage(String msg) {
		System.out.println(msg);
	}
	
	//TODO javadoc if it is determined where to use this!
	public void showHelp() {
		String exit = "EXIT, exitst application.";
		System.out.printf("Commands:\n%s", exit);
		// TODO implement
	}

	/**
	 * Shows the hand of the player.
	 */
	@Override
	public void showHand(List<Tile> tiles) {
		
		// TODO Auto-generated method stub
		
	}

	/**
	 * Asks the user for the internet address to connect to in case of a multiplayer game.
	 */
	@Override
	public InetAddress getHost() {
		System.out.println("Enter internet address");
		try {
			host = InetAddress.getByName(input.nextLine());
		} catch (UnknownHostException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			getHost();
		}
		return host;
	}

	/**
	 * Asks the user for a port number.
	 */
	@Override
	public int getPort() {
		// TODO Auto-generated method stub
		System.out.println("Enter the port");
		int in = input.nextInt();
		input.nextLine();
		return in;
	}
	
	/**
	 * Asks the names of a player.
	 * @param number The player number from whom to get the name
	 */
	@Override
	public String getPlayer(int number) {
		String result = "";
		System.out.println("For AI players use: AI 'StrategyName'");
		if (number == 1) {
			do {
				System.out.printf("Enter name:\n");
				result = input.nextLine();
				if (!result.matches("[a-zA-Z0-9-_]{2,16}")) {
					System.out.println("Name not supported, please choose a different name.");
				}
			} while (!result.matches("[a-zA-Z0-9-_]{2,16}"));
		} else {
			System.out.printf("Enter player %d:\n", number + 1);
			result = input.nextLine();
		}
		
		//System.out.println("result: " + result[0] + result[1]);
		return result;
	}
	
	/**
	 * Asks the amount of players.
	 */
	public int getPlayerCount() {
		System.out.println("How many players (2-4)?");
		int in = input.nextInt();		// TODO catch error if isn't int
		input.nextLine();
		return in;
	}

}
