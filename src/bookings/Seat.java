package bookings;

public class Seat {

    public static final char MIN_ROW = 'A';
    public static final char MAX_ROW = 'G';
    public static final int MIN_NUMBER = 1;
    public static final int MAX_NUMBER = 20;

    //@ invariant row >= MIN_ROW;
    private final char row;
    //@ invariant number >= MIN_NUMBER;
    private final int number;
    
    //@ requires row >= MIN_ROW;
    //@ requires number >= MIN_NUMBER;
    public Seat(char row, int number) {
        this.row = row;
        this.number = number;
    }

    public /*@ helper */  final char getRow() {
        return row;
    }
    
    public /*@ helper */ final int getNumber() {
        return number;
    }

}
