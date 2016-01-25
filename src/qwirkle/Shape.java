package qwirkle;

public enum Shape {
	CROSS, SQUARE, CIRCLE, DIAMOND, STAR, CLOVER;
	
	public int toInt() {
		switch(this) {
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
}
