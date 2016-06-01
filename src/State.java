import java.util.LinkedList;
import java.util.List;

public class State {

/**
 * Creates a State given the previous State, List of remaining Trips, last Trip, and gCost
 * @param prevState the previous State
 * @param remainingTrips the remaining required Trips
 * @param lastTrip the last Trip made from the previous State
 * @param gCost the cost to reach the State from the initial State
 */
public State(State prevState, List<Trip> remainingTrips, Trip lastTrip, int gCost) {
  this.prevState = prevState;
  this.remainingTrips = remainingTrips;
  this.lastTrip = lastTrip;
  this.gCost = gCost;
}

/**
 * Determines the Trips taken from the initial State to reach the current State
 * @return List containing the Trips taken from the initial State to the current State
 */
public List<Trip> getSchedule() {
  List<Trip> schedule = new LinkedList<Trip>();
  State currState = this;
  while (currState.prevState != null) {
    schedule.add(0, currState.lastTrip);
    currState = currState.prevState;
  }

  return schedule;
}

/**
 * @return the List of remaining required trips
 */
public List<Trip> getRemainingTrips() {
  return this.remainingTrips;
}

/**
 * @return the current City of this State
 */
public City getCurrCity() {
  return this.lastTrip.getDest();
}

/**
 * @return the cost to reach this State
 */
public int getGCost() {
  return this.gCost;
}
/**
 * Two States are equal if they have the same current city and remaining trips
 */
@Override
public boolean equals(Object o) {
  if (o == null) {
    return false;
  }

  if (o instanceof State) {
    State other = (State) o;
    return this.getCurrCity().equals(other.getCurrCity());
  }

  return false;
}

@Override
public int hashCode() {
  return getCurrCity().hashCode() + remainingTrips.hashCode();
}

public String toString(){
  if(this.prevState == null){
    return this.lastTrip.toString();
  }else{
    return prevState + "->" + this.lastTrip;
  }
}

private State prevState;
private List<Trip> remainingTrips;
private Trip lastTrip;
private int gCost;
}
