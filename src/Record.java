
public class Record {
	public Donor donor;
	public String cityname;
	public int state;
	public int creationDate;
	public int updateDate;
	public Blood blood;
	// 0 --> waiting batmobile to come and pick up
	// 1 --> waiting hospital to verify
	// 2 --> added
	// 3 --> used
	
	public Record(Donor donor, String cityName){
		this.cityname = cityName;
		this.donor = donor;
		this.creationDate = this.updateDate = (int) System.currentTimeMillis();
		this.state = 0;
	}
	
	public String getDetails() {
		return Util.toHTML("City: " + cityname + "\nCreation date: " + creationDate + "\nUpdate date: " + updateDate);
	}
}
