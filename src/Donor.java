import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import javax.swing.JLabel;

public class Donor {
	public String username;
	public String password;
	public String gender;
	public String blood_type;
	public int YOB; // year of birth
	public String phone;
	public String cityName;
	public List<Record> records;

	public Donor(String username, String password, String gender, String blood_type, int YOB, String phone){
		this.username = username;
		this.password = password;
		this.gender = gender;
		this.blood_type = blood_type;
		this.YOB = YOB;
		this.phone = phone;
		this.records = new ArrayList<>();
		this.cityName = "London"; // default
	}

	public void addRecord(Record r){
		records.add(r);
		Util.records.add(r);
	}

	public void sortRecordByUpdateDate(){
		Collections.sort(records, new Comparator<Record>() {
			public int compare(Record self, Record other) {
				Long i = self.updateDate;
				Long j = other.updateDate;
				return i.compareTo(j);
			}
		});
	}

	public void groupByStatus(){
		int one = 0;
		int three = this.records.size();
		int next = 0;

		while(next != three){
			switch(this.records.get(next).state){
			case 1: next ++;break;
			case 2: next ++; break;
			case 3: three --;
			Collections.swap(this.records,next, three);
			break;
			default: Collections.swap(this.records,next, one);
			next ++;
			one ++;
			}
		}

		next = one;
		int two = one;

		while(next != three){
			switch(this.records.get(next).state){
			case 2: next ++;break;
			case 1: Collections.swap(this.records,next, two);
			next ++;
			two ++;
			break;
			}
		}
	}

	public String getDetails() {
		return Util.toHTML(("Username: " + this.username + "\nGender: " + this.gender + "\nBlood Type: " + this.blood_type
				+ "\nYear of birth: " + this.YOB +"\nPhone: " + this.phone + "\nCity Name: " + this.cityName));
	}
}
