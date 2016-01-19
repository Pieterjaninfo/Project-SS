package ui;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

import qwirkle.Qwirkle;

public class TUI implements UI {

	private Scanner input; 
	private Qwirkle game;
	private InetAddress host;

	
	public TUI(Qwirkle game) {
		this.game = game;
	}
	
	@Override
	public void showBoard() {
		// TODO Auto-generated method stub
		
	}

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

	@Override
	public void showError(String msg) {
		System.out.println(msg);
	}
	
	public void showHelp() {
		String exit = "EXIT, exitst application.";
		System.out.printf("Commands:\n%s", exit);
		// TODO implement
	}

	@Override
	public void showHand() {
		// TODO Auto-generated method stub
		
	}

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

	@Override
	public int getPort() {
		// TODO Auto-generated method stub
		System.out.println("Enter the port");
		return input.nextInt();
	}
}
