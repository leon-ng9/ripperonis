import java.util.concurrent.TimeUnit;
import java.text.*;
import java.util.*;

public class Blood {
	public Donor donor;
	public Hospital hospital;
	public Batmobile batmobile;
	public int amount;
	public long arrival_date;
	public long used_by_date;
	public boolean used;

	public Blood(int amount, Donor donor, Batmobile bm){
		this.amount = amount;
		this.arrival_date = (long) System.currentTimeMillis();
		this.used_by_date = (long) (arrival_date + 7 * TimeUnit.MILLISECONDS.convert(1, TimeUnit.DAYS));;
		this.donor = donor;
		this.batmobile = bm;
	}

	public String printDetails(){
		String expire = new SimpleDateFormat("yyyy-MM-dd")
                          .format(new Date(used_by_date));
		return Util.toHTML(("Blood type: " + this.donor.blood_type + "\n Amount:" + this.amount + "\n Expiration date: " + expire));
	}
}
