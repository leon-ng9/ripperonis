import java.util.concurrent.TimeUnit;

public class Blood {
	public Donor donor;
	public Hospital hospital;
	public Batmobile batmobile;
	public int amount;
	public int arrival_date;
	public int used_by_date;
	public boolean used;

	public Blood(int amount, Donor donor, Batmobile bm){
		this.amount = amount;
		this.arrival_date = (int) System.currentTimeMillis();
		this.used_by_date = (int) ((int) System.currentTimeMillis() + 7 * TimeUnit.MILLISECONDS.convert(1, TimeUnit.DAYS));;
		this.donor = donor;
		this.batmobile = bm;
	}

	public String printDetails(){
		return Util.toHTML(("Blood type: " + this.donor.blood_type + "\n Amount:" + this.amount + "\n Expiration date: " + this.used_by_date));
	}
}