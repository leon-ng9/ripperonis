import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import org.omg.CORBA.Request;

public class Batmobile {
  public String name;
  public String cityName;
  public Batmobile(String name, String cityName){
    this.name = name;
    this.cityName = cityName;
  }

  public Hashtable<Request, String> closestRequest(){
    Map map = Util.map;
    Hashtable<Request, String> preresult = map.closestCity(cityName, 5);
    return preresult;
  }

  public void add(Record r){
    r.state = 0;
  }

  public void update(Record r){
    r.state = 1;
    r.UpdateDate = currentTime;
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
