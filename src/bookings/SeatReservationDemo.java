package bookings;

public class SeatReservationDemo {

    public static void main(String[] args) throws ReservationException {

        SeatReservationManager mgr = new SeatReservationManager();
        Customer[] customers = new Customer[140];
        String str;

        // Instantiate the customers (otherwise they stay null and cannot be
        // used to reserve as mgr tests against null)
        for (int i=0; i<customers.length; i++) {
            customers[i] = new Customer();
        }

        // Reserve targets seats while letting some free
        char[] rows = {'A', 'B', 'D' ,'E', 'G'};
        int[] nums = {
            1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17, 18
        };

        int current = 0;
        for(char row: rows) {
            for (int n: nums) {
                Seat s = new Seat(row, n);
                mgr.reserve(s, customers[current]);
                current++;
            }
        }

        str = mgr.toString(); // Use toString

        // Reserve using nextFree
        for(int i = current; i < customers.length; i++) {
            mgr.reserveNextFree(customers[i]);
        }

        str = mgr.toString(); // Use toString

        // Use unreserve
        for(char row: rows) {
            for (int n: nums) {
                Seat s = new Seat(row, n);
                mgr.unreserve(s);
            }
        }

        str = mgr.toString(); // Use toString

        // Run into failing (ReservationExcception) code path
        try {
            mgr.reserve(new Seat('A', 20), customers[0]);
        } catch(ReservationException exc) {} finally {}

    }

}
