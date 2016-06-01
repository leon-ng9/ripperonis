import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

// list of donors ( 5 closest to donors & the paths to go to them )
// take off the list
public class Batmobile {
	public String name;
	public String cityName;
	
	public Batmobile(String name, String cityName){
		this.name = name;
		this.cityName = cityName;
	}

	public Hashtable<Record, String> closestRequest(){
		TripPlanner map = Util.map;
		Hashtable<String, ArrayList<Record>> records = new Hashtable<>();
		for(Record r: Util.records){
			if(records.containsKey(r.cityname)){
				records.get(r.cityname).add(r);
			}else{
				ArrayList<Record> ar = new ArrayList<>();
				ar.add(r);
				records.put(r.cityname, ar);
			}
		}
		Hashtable<Record, String> preresult = map.closestCity(cityName, 5, records);
		return preresult;
	}

	public void add(Record r){
		r.state = 0;
	}

	public void update(Record r){
		r.state = 1;
		r.updateDate = (int) System.currentTimeMillis();
	}
	
	public List<Record> getPendingRecords(){
		ArrayList<Record> result = new ArrayList<>();
		for(Record r: Util.records){
			if(r.state == 0){
				result.add(r);
			}
		}
		return result;
	}
	
	public void remove(Record r){
		r.state = -1;
	}
}
