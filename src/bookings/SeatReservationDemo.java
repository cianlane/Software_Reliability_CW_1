package bookings;

public class SeatReservationDemo {

    public static void main(String[] args) throws ReservationException {
    	
    	SeatReservationManager srm = new SeatReservationManager();
    	
    	srm.reserve(new Seat('D', 5) ,new Customer());
    	
    	srm.reserve(new Seat('E', 6) ,new Customer());
    	
    	srm.reserve(new Seat('F', 7) ,new Customer());
    }
    
}
