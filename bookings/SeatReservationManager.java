package bookings;

public class SeatReservationManager {

    private final Customer[][] seatReservations;

    //@ ghost public boolean init= true;
    //@ invariant init ==> (seatReservations.length==Seat.MAX_ROW-Seat.MIN_ROW+1 && (\forall int i; 0<=i && i<Seat.MAX_ROW-Seat.MIN_ROW+1 ==> seatReservations[i].length==Seat.MAX_NUMBER-Seat.MIN_NUMBER+1))
    //@ invariant \nonnullelements(seatReservations);



    public SeatReservationManager() {
        //@ assume (init== false);

        seatReservations = new Customer[rowToIndex(Seat.MAX_ROW) + 1]
                [numberToIndex(Seat.MAX_NUMBER) + 1];

    }



    public boolean isReserved(/*@ non_null */Seat s) {
        //@ assume (init== true);
        return seatReservations[rowToIndex(s.getRow())]
                [numberToIndex(s.getNumber())] != null;
    }



    //@ requires \typeof(c)<: \elemtype(\typeof(seatReservations));
    public void reserve(/*@ non_null*/Seat  s, /*@ non_null*/Customer c)
            throws ReservationException {
        //@ assume (init== true);
        if(isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                [numberToIndex(s.getNumber())] = c;
    }


    public void unreserve(/*@ non_null*/Seat s)
            throws ReservationException {
        //@ assume (init== true);
        if(!isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                [numberToIndex(s.getNumber())] = null;
    }

    //@ requires \typeof(c)<: \elemtype(\typeof(seatReservations));
    //@ requires c!=null
    public void reserveNextFree(/* non_null */Customer c) throws ReservationException {
        //@ assume (init== true);
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


    public String toString() {
        //@ assume (init== true);

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

    //@ requires row>=Seat.MIN_ROW && row<=Seat.MAX_ROW
    //@ ensures \result>=0 && \result<= Seat.MAX_ROW-Seat.MIN_ROW

    private static int rowToIndex(char row) {
        return row - Seat.MIN_ROW;
    }
    //@ requires number>=Seat.MIN_NUMBER && number<=Seat.MAX_NUMBER
    //@ ensures \result>=0 && \result<= Seat.MAX_NUMBER-Seat.MIN_NUMBER

    private static int numberToIndex(int number) {
        return number - Seat.MIN_NUMBER;
    }

    //@ requires index>=0 && index<Seat.MAX_ROW-Seat.MIN_ROW;
    //@ ensures \result>=Seat.MIN_ROW && \result<=Seat.MAX_ROW
    //@ pure
    private static char indexToRow(int index) {
        return (char)(Seat.MIN_ROW + index);
    }

    //@ requires index>=0 && index<Seat.MAX_NUMBER-Seat.MIN_NUMBER;
    //@ ensures Seat.MIN_NUMBER<=\result && \result<=Seat.MAX_NUMBER
    //@ pure
    private static int indexToNumber(int index) {
        return index + Seat.MIN_NUMBER;
    }

}
