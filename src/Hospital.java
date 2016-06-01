import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.List;

public class Hospital {
	public String name;
	public List<Blood> bloods;

	public Hospital(String name){
		this.name = name;
		this.bloods = new ArrayList<Blood>();
		// add(new Record(new Donor("Leon", "password", "Male", "AB-", 1996, "0400000000"), "London"));
		// add(new Record(new Donor("Leon", "password", "Male", "AB-", 1996, "0400000000"), "London"));
		// add(new Record(new Donor("Leon", "password", "Male", "AB-", 1996, "0400000000"), "London"));
		// add(new Record(new Donor("Leon", "password", "Male", "AB-", 1996, "0400000000"), "London"));
	}

	public void add(Record r){
		r.state = 1;
	}

	public void update(Record r){
		if(r.state == 1){
			r.blood.hospital = this;
			r.state = 2;
			r.updateDate = (int) System.currentTimeMillis();
			bloods.add(r.blood);
		}
	}

	public void remove(Record r){
		r.state = -1;
	}

	public ArrayList<Blood> getAvailableBlood(){
		ArrayList<Blood>  result = new ArrayList<>();
		for(Record r: Util.records){
			if(r.state != 2){
				continue;
			}
			Blood b = r.blood;
			if(b.used_by_date >= (int) System.currentTimeMillis() && !b.used){
				result.add(b);
			}
		}
		return result;
	}

	public List<Record> getPendingRecords(){
		ArrayList<Record> result = new ArrayList<>();
    for(Record r: Util.records){
      if(r.state == 1){
        result.add(r);
      }
    }
    return result;
	}

	public Hashtable<String, Integer> summary(){
		ArrayList<Blood> allBlood = getAvailableBlood();
		Hashtable<String, Integer> result = new Hashtable<>();
		for(Blood b: allBlood){
			if(result.containsKey(b.donor.blood_type)){
				result.put(b.donor.blood_type,result.get(b.donor.blood_type) + b.amount);
			}else{
				result.put(b.donor.blood_type,b.amount);
			}
		}
		System.out.println(result);
		return result;
	}

	public List<Record> requestBlood(int amount, String type){
		sortRecordByUsedByDate();
		ArrayList<Record> result = new ArrayList<>();
		int i = 0;
		for(Record curr: Util.records){
			if(amount <= 0){
				break;
			}
			if(curr.state != 2){
				continue;
			}
			System.out.println(curr.donor.blood_type +" " + type);
			if(curr.donor.blood_type.equals(type)){
				result.add(curr);
				amount -= curr.blood.amount;
			}
			i ++;
		}
		if(amount > 0){
			System.out.println("DS");
			return null;
		}else{
			return result;
		}
	}

	public void sortRecordByUsedByDate(){
		Collections.sort(bloods, new Comparator<Blood>() {
			public int compare(Blood self, Blood other) {
				Long i = self.used_by_date;
				Long j = other.used_by_date;
				return i.compareTo(j);
			}
		});
	}
}
