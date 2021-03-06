package qwirkle;

public enum Shape {
	CROSS, SQUARE, CIRCLE, DIAMOND, STAR, CLOVER;
	
	public int toInt() {
		switch (this) {
			case CROSS: return 1;
			case SQUARE: return 2;
			case CIRCLE: return 3;
			case DIAMOND: return 4;
			case STAR: return 5;
			case CLOVER: return 0;
		}
		
		return 0;
	}
	
	public static Shape toEnum(int code) {
		switch (code) {
			case 0: return CLOVER;
			case 1: return CROSS;
			case 2: return SQUARE;
			case 3: return CIRCLE;
			case 4: return DIAMOND;
			case 5: return STAR;
		}
		return null;
	}
	
	public String toString() {
		switch (this) {
			case CROSS: return "x";
			case SQUARE: return "s";
			case CIRCLE: return "o";
			case DIAMOND: return "d";
			case STAR: return "*";
			case CLOVER: return "c";
		}
		return null;
	}
	
	public static Shape charToEnum(char character) {
		switch (character) {
			case 'x' : return CROSS;
			case 's' : return SQUARE;
			case 'o' : return CIRCLE;
			case 'd' : return DIAMOND;
			case '*' : return STAR;
			case 'c' : return CLOVER;
		}
		return null;
	}
}
