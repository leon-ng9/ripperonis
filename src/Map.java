import java.util.LinkedList;
import java.util.List;
import java.util.Random;

public class Map {

	/**
	 * Creates a Map with no cities
	 */
	public Map() {
		this.cities = new LinkedList<City>();
	}

	/**
	 * Return the City object corresponding to the given name
	 * @param cityName the name of the City
	 * @return the City object with the given name
	 */
	public City getCity(String cityName) {
		for (City c : this.cities) {
			if (c.getName().equals(cityName)) {
				return c;
			}
		}

		return null;
	}

	/**
	 * Adds a City to the Map
	 * @param transferTime the transfer time for the City
	 * @param cityName the name of the City
	 */
	public void addCity(int transferTime, String cityName) {
		this.cities.add(new City(cityName, transferTime));
	}

	/**
	 * Adds a connection between two cities on the Map
	 * @param travelTime the travel time between the two cities
	 * @param cityNameA the name of the first City
	 * @param cityNameB the name of the second City
	 */
	public void addConnection(int travelTime, String cityNameA, String cityNameB) {
		City cityA = getCity(cityNameA);
		City cityB = getCity(cityNameB);

		cityA.addConnection(cityB, travelTime);
		cityB.addConnection(cityA, travelTime);
	}

	public City getRandCity(){
		Random r = new Random();
		// System.out.println(cities);
		return cities.get(r.nextInt(cities.size()));
	}

	private List<City> cities;
}
