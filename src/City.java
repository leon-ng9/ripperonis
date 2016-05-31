import java.util.HashMap;

public class City {

	/**
	 * Creates a City with a name, a transfer time, and no neighbours
	 * @param name the name of the City
	 * @param transferTime the transfer time of the City
	 */
	public City(String name, int transferTime) {
		this.name = name;
		this.transferTime = transferTime;
		this.connections = new HashMap<City, Integer>();
	}

	/**
	 * @return the name of the City
	 */
	public String getName() {
		return this.name;
	}
	
	/**
	 * @return the transfer time of the City
	 */
	public int getTransferTime() {
		return this.transferTime;
	}
	
	/**
	 * @return the neighbours of the City as a HashMap<City, Integer>
	 * which maps neighbouring cities to their travel time
	 */
	public HashMap<City, Integer> getConnections() {
		return this.connections;
	}
	
	/**
	 * Adds a neighbour to the City
	 * @param city a neighbouring City
	 * @param travelTime the travel time to the neighbouring City
	 */
	public void addConnection(City city, int travelTime) {
		this.connections.put(city, travelTime);
	}
	
	/**
	 * Two cities are equal if their names are equal
	 */
	@Override
	public boolean equals(Object o) {
		if (o == null) {
			return false;
		}
		
		if (o instanceof City) {
			City other = (City) o;
			return this.name.equals(other.name);
		}
		
		return false;
	}
	
	@Override
	public int hashCode() {
		return name.hashCode();
	}
	
	private String name;
	private int transferTime;
	private HashMap<City, Integer> connections;
}
