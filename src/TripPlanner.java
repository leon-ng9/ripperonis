import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.Scanner;


public class TripPlanner {

	/**
	 * Constructs a TripPlanner with a Map and no required trips
	 */
	public TripPlanner() {
		this.map = new Map();
		this.requiredTrips = new LinkedList<Trip>();
		this.init();
	}

	/**
	 * Reads and processes input from a file to form the map and required trips
	 * @param args Command-line arguments (only first argument, name of the input file, is used)
	 */
	public void init() {
		Scanner sc = null;
		try {
			sc = new Scanner(new FileReader("cityConnections.txt"));
			while (sc.hasNext()) {
				String[] commandArgs = sc.nextLine().split(" ");

				if (commandArgs[0].equals("Transfer")) {
					addCity(Integer.parseInt(commandArgs[1]), commandArgs[2]);
				} else if (commandArgs[0].equals("Time")) {
					this.addConnection(Integer.parseInt(commandArgs[1]), commandArgs[2], commandArgs[3]);
				}
			}

		} catch (FileNotFoundException e) {
			System.err.println("Could not find file");
		} finally {
			if (sc != null) sc.close();
		}
	}

	/**
	 * Adds a new City to the Map
	 * @param transferTime transfer time of the City
	 * @param cityName name of the City
	 */
	public void addCity(int transferTime, String cityName) {
		this.map.addCity(transferTime, cityName);
	}

	/**
	 * Adds a connection between two cities on the Map
	 * @param travelTime travel time between the two cities
	 * @param cityNameA name of the first city
	 * @param cityNameB name of the second city
	 */
	public void addConnection(int travelTime, String cityNameA, String cityNameB) {
		this.map.addConnection(travelTime, cityNameA, cityNameB);
	}


	/**
	 * Prints out a minimum-cost path starting from the City "London" containing all of the required
	 * Trips as well as the nodes expanded during the search and the total cost of the path
	 */
	public Hashtable<Record, String> closestCity(String from, int number, Hashtable<String, ArrayList< Record >> list) {
		StateComparator stateComparator = new StateComparator();
		PriorityQueue<State> toVisit = new PriorityQueue<State>(11, stateComparator);
		HashMap<State, Integer> visited = new HashMap<State, Integer>();
		Hashtable<Record, String> result = new Hashtable<>();

		// initialisation
		City startCity = this.map.getCity(from);
		State initialState = new State(null, this.requiredTrips, new Trip(null, startCity), -startCity.getTransferTime());
		toVisit.add(initialState);

		while (!toVisit.isEmpty()) {
			State currState = toVisit.poll();
			if(list.containsKey(currState.getCurrCity())){
				ArrayList< Record> currList = list.get(currState.getCurrCity());
				for(Record s: currList){
					result.put(s, currState.toString());
				}
			}
			if(result.size() >= number){
				return result;
			}

			visited.put(currState, currState.getGCost());

			City currCity = currState.getCurrCity();
			HashMap<City, Integer> neighboursMap = currCity.getConnections();
			for (City neighbour : neighboursMap.keySet()) {
				int gCost = currState.getGCost() + currCity.getTransferTime() + neighboursMap.get(neighbour);
				Trip trip = new Trip(currCity, neighbour);
				List<Trip> remainingTrips = new LinkedList<Trip>(currState.getRemainingTrips());
				remainingTrips.remove(trip); // remove the trip from remainingTrips if possible

				State childState = new State(currState, remainingTrips, trip, gCost);
			}
		}

		return result;
	}

	public City getRandCity(){
		return map.getRandCity();
	}


	private Map map;
	private List<Trip> requiredTrips;
}
