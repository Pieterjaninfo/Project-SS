package testPlatform;

import java.util.HashMap;
import java.util.Map;

public class Test {

    private static final String CLIENT_IDENTIFY = "IDENTIFY";
	private static final String NAME_REGEX = "^[A-Za-z0-9-_]{2,16}$";

	
	public static void main(String[] args) {
		//System.out.printf("Enter number for choice:\n1. Singleplayer\n2. Multiplayer");
		//String input = CLIENT_IDENTIFY + " Bart";
		//System.out.printf("Name:\n%s\nRegex match:\n%s\n", input.substring(CLIENT_IDENTIFY.length()+1), input.substring(CLIENT_IDENTIFY.length()+1).matches(NAME_REGEX));

		/*
		String input = " a b c";
		String[] test = input.split(" ");
		for (int i = 0; i < test.length; i++) {
			System.out.printf("%s\n", test[i]);
		}*/
		
		/*
		Map<Integer, String> test = new HashMap<Integer, String>();
		test.put(1, "een");
		test.put(-5, "negatief 5");
		test.put(6, "zes");
		test.put(-2, "negatief 2");


		for(Integer a : test.keySet()) {
			System.out.println(test.get(a));
		}
*/
 	}

}
