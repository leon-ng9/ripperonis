import java.util.*;
import java.text.*;
public class Record {
	public Donor donor;
	public String cityname;
	public int state;
	public long creationDate;
	public long updateDate;
	public Blood blood;
	// 0 --> waiting batmobile to come and pick up
	// 1 --> waiting hospital to verify
	// 2 --> added
	// 3 --> used

	public Record(Donor donor, String cityName){
		this.cityname = cityName;
		this.donor = donor;
		this.creationDate = this.updateDate = (long) System.currentTimeMillis();
		this.state = 0;
		donor.records.add(this);
		Util.records.add(this);
	}

	public String getDetails() {
		String update = new SimpleDateFormat("yyyy-MM-dd")
                          .format(new Date(updateDate));
													String creation = new SimpleDateFormat("yyyy-MM-dd")
											                          .format(new Date(creationDate));
		return Util.toHTML("City: " + cityname + "\nCreation date: " + creation + "\nUpdate date: " + update + "\nBlood Type: " + donor.blood_type);
	}

	public void donate(int amount, Batmobile bm) {
		blood = new Blood(amount,donor, bm);
		state = 1;
	}
}
