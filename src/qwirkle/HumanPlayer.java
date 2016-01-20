package qwirkle;

public class HumanPlayer implements Player{
	
	private String name;

	public HumanPlayer(String name) {
		this.name = name;
	}
	
	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return name;
	}

}
