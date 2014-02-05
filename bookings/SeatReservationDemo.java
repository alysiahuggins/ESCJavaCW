package bookings;

public class SeatReservationDemo {

    public static void main(String[] args) throws ReservationException {

        SeatReservationManager manager= new SeatReservationManager();
        Customer samantha= new Customer();
        Customer alysia= new Customer();
        Customer soukaina= new Customer();
        Customer sue= new Customer();
        Seat souSeat= new Seat('A', 1); // add min value for row and number
        Seat samSeat= new Seat('A', 11);
        Seat alSeat= new Seat('B', 10);
        Seat sueSeat= new Seat('G', 20); // add max value for row and number
        manager.reserve(samSeat,samantha);
        manager.reserve(souSeat,soukaina);
        manager.reserve(sueSeat,alysia);

        int i=0;
        while(i<42){

            manager.reserveNextFree(sue);
            i++;
        }


        System.out.println(manager);

    }

}