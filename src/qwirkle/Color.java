package qwirkle;

/**
 * All the Colors enumerated.
 * @author Pieter Jan
 *
 */
public enum Color {
	RED, ORANGE, YELLOW, GREEN, BLUE, PURPLE;
	
	public int toInt() {
		switch (this) {
			case RED: return 1;
			case ORANGE: return 2;
			case YELLOW: return 3;
			case GREEN: return 4;
			case BLUE: return 5;
			case PURPLE: return 0;
		}
		return 0;
	}
	
	public static Color toEnum(int code) {
		switch (code) {
			case 0: return PURPLE;
			case 1: return RED;
			case 2: return ORANGE;
			case 3: return YELLOW;
			case 4: return GREEN;
			case 5: return BLUE;
		}
		return null;
	}
}

