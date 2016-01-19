package ui;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

import qwirkle.Qwirkle;

/**
 * Textual user interface for the Qwirkle game.
 * @author Bart Meyers
 *
 */
public class TUI implements UI {

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
		// TODO startup prints and reads, simple implementation needs improvement.
	}

	/**
	 * Print the error message to the output.
	 */
	@Override
	public void showError(String msg) {
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
	public void showHand() {
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
		return input.nextInt();
	}
	
	/**
	 * Gets the names of the players.
	 */
	@Override
	public String[] getPlayers() { // TODO change such that it can be used by the multiplayer
		System.out.println("How many players (2-4)?");
		int in = input.nextInt();
		String[] result = new String[in];
		input.nextLine();
		System.out.println("For AI players use: AI 'StrategyName'");
		for (int i = 0; i < in; i++) {
			System.out.printf("Enter player %d:\n", i + 1);
			result[i] = input.nextLine();
		}
		//System.out.println("result: " + result[0] + result[1]);
		return result;
	}
}
