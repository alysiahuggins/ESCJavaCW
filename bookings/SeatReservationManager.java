package bookings;

public class SeatReservationManager {

    private final /*non_null*/Customer[][] seatReservations;


    public SeatReservationManager() {
        seatReservations = new Customer[rowToIndex(Seat.MAX_ROW) + 1]
                [numberToIndex(Seat.MAX_NUMBER) + 1];
    }

    //@ requires \nonnullelements(seatReservations);


    public boolean isReserved(/*@ non_null */Seat s) {
        return seatReservations[rowToIndex(s.getRow())]
                [numberToIndex(s.getNumber())] != null;
    }


    //@ requires \nonnullelements(seatReservations);
    //@ requires \typeof(c)<: \elemtype(\typeof(seatReservations));
    public void reserve(/*@ non_null*/Seat  s, /*@ non_null*/Customer c)
            throws ReservationException {
        if(isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                [numberToIndex(s.getNumber())] = c;
    }

    //@ requires \nonnullelements(seatReservations);
    public void unreserve(/*@ non_null*/Seat s)
            throws ReservationException {
        if(!isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                [numberToIndex(s.getNumber())] = null;
    }

    //@ requires \nonnullelements(seatReservations);
    //@ requires \typeof(c)<: \elemtype(\typeof(seatReservations));
    //@ requires c!=null

    public void reserveNextFree(/* non_null */Customer c) throws ReservationException {
        for(int rowIndex = 0; rowIndex < seatReservations.length; rowIndex++) {
            for(int numberIndex = 0;
                numberIndex < seatReservations[rowIndex].length;
                numberIndex++) {
                Seat current = new Seat(indexToRow(rowIndex),
                        indexToNumber(numberIndex));
                if(!isReserved(current)) {
                    reserve(current, c);
                    return;
                }
            }
        }

        throw new ReservationException();
    }//@ nowarn Exception

    
    /*@ ghost String toStringResult; in privateState;
        represents theString <- toStringResult;
@*/


    //@ requires \nonnullelements(seatReservations)
    //@ invariant (\forall int i; i>=0 && i<= seatReservations.length ==> \nonnullelements(seatReservations[i]))

    public String toString() {

        String result = " ";


        for(int numberIndex = 0; numberIndex < seatReservations[0].length;
            numberIndex++) {

            result += " " + indexToNumber(numberIndex);
        }
        result += "\n";

        for(int rowIndex = 0;
            rowIndex < seatReservations.length;
            rowIndex++) {
            result += indexToRow(rowIndex);
            for(int numberIndex = 0; numberIndex <
                    seatReservations[rowIndex].length; numberIndex++) {
                for(int j = numberIndex; j >= 10; j /= 10) {
                    result += " ";
                }

                result += " " + (isReserved(new Seat(indexToRow(rowIndex),
                        indexToNumber(numberIndex))) ? "X" : " ");
            }
            result += "\n";
        }

        //@ set toStringResult = result;
        return result;
    }
    //@ requires row>=Seat.MIN_ROW & row<=Seat.MAX_ROW
    //@ ensures \result>=0 & \result<= Seat.MAX_ROW-Seat.MIN_ROW
    private static int rowToIndex(char row) {
        return row - Seat.MIN_ROW;
    }
    //@ requires number>=Seat.MIN_NUMBER & number<=Seat.MAX_NUMBER
    //@ ensures \result>=0 & \result<= Seat.MAX_NUMBER-Seat.MIN_NUMBER
    private static int numberToIndex(int number) {
        return number - Seat.MIN_NUMBER;
    }

    //@ requires index>=0 & index<Seat.MAX_ROW-Seat.MIN_ROW;
    //@ ensures \result>=Seat.MIN_ROW & \result<=Seat.MAX_ROW
    private static char indexToRow(int index) {
        return (char)(Seat.MIN_ROW + index);
    }

    //@ requires index>=0 & index<Seat.MAX_NUMBER-Seat.MIN_NUMBER;
    //@ ensures Seat.MIN_NUMBER<=\result & \result<=Seat.MAX_NUMBER
    private static int indexToNumber(int index) {
        return index + Seat.MIN_NUMBER;
    }

}
