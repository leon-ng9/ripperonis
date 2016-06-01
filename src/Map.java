import java.util.LinkedList;
import java.util.List;
import java.util.Random;

public class Map {

	public Map() {
		this.cities = new LinkedList<City>();
	}

	public City getCity(String cityName) {
		for (City c : this.cities) {
			if (c.getName().equals(cityName)) {
				return c;
			}
		}

		return null;
	}

	public void addCity(int transferTime, String cityName) {
		this.cities.add(new City(cityName, transferTime));
	}

	public void addConnection(int travelTime, String cityNameA, String cityNameB) {
		City cityA = getCity(cityNameA);
		City cityB = getCity(cityNameB);

		cityA.addConnection(cityB, travelTime);
		cityB.addConnection(cityA, travelTime);
	}

	public City getRandCity(){
		Random r = new Random();
		return cities.get(r.nextInt(cities.size()));
	}

	private List<City> cities;
}
