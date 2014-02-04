package bookings;

public class Seat {

    public static final char MIN_ROW = 'A';
    public static final char MAX_ROW = 'G';
    public static final int MIN_NUMBER = 1;
    public static final int MAX_NUMBER = 20;

    private final char row;
    private final int number;

    //@ invariant row>= MIN_ROW & row <=MAX_ROW
    //@ invariant MIN_NUMBER<=number & number<=MAX_NUMBER

    //@ requires row>= MIN_ROW & row <=MAX_ROW
    //@ requires MIN_NUMBER<=number & number<=MAX_NUMBER
    //@ ensures this.row>= MIN_ROW & this.row <=MAX_ROW
    //@ ensures MIN_NUMBER<=this.number & this.number<=MAX_NUMBER
    public Seat(char row, int number) {
        this.row = row;
        this.number = number;
    }


    //@ requires row>= MIN_ROW && row <=MAX_ROW
    //@ ensures \result>= MIN_ROW && \result <=MAX_ROW
    public final char getRow() {
        return row;
    }

    //@ requires MIN_NUMBER<=number && number<=MAX_NUMBER
    //@ ensures MIN_NUMBER<=\result && \result<=MAX_NUMBER
    public final int getNumber() {
        return number;
    }

}