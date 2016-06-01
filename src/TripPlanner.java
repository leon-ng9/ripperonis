import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.*;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.Scanner;


public class TripPlanner {

	public TripPlanner() {
		this.map = new Map();
		this.requiredTrips = new LinkedList<Trip>();
		this.init();
	}

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

	public void addCity(int transferTime, String cityName) {
		this.map.addCity(transferTime, cityName);
	}

	public void addConnection(int travelTime, String cityNameA, String cityNameB) {
		this.map.addConnection(travelTime, cityNameA, cityNameB);
	}


	public Hashtable<Record, String> closestCity(String from, int number, Hashtable<String, ArrayList< Record >> list) {
		StateComparator stateComparator = new StateComparator();
		PriorityQueue<State> toVisit = new PriorityQueue<State>(11, stateComparator);
		HashSet<City> visited = new HashSet<>();
		Hashtable<Record, String> result = new Hashtable<>();

		// initialisation
		City startCity = this.map.getCity(from);
		State initialState = new State(null, this.requiredTrips, new Trip(null, startCity), -startCity.getTransferTime());
		toVisit.add(initialState);

		while (!toVisit.isEmpty()) {
			State currState = toVisit.poll();
			if(list.containsKey(currState.getCurrCity().toString())){
				ArrayList< Record> currList = list.get(currState.getCurrCity().toString());
				for(Record s: currList){
					result.put(s, currState.toString());
				}
			}
			if(result.size() >= number){
				return result;
			}

			visited.add(currState.getCurrCity());

			City currCity = currState.getCurrCity();
			HashMap<City, Integer> neighboursMap = currCity.getConnections();
			for (City neighbour : neighboursMap.keySet()) {
				int gCost = currState.getGCost() + currCity.getTransferTime() + neighboursMap.get(neighbour);
				Trip trip = new Trip(currCity, neighbour);
				List<Trip> remainingTrips = new LinkedList<Trip>(currState.getRemainingTrips());

				State childState = new State(currState, remainingTrips, trip, gCost);
				if(! visited.contains(neighbour)){
					toVisit.add(childState);
				}
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
