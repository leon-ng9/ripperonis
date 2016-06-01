import java.util.LinkedList;
import java.util.List;

public class State {

	public State(State prevState, List<Trip> remainingTrips, Trip lastTrip, int gCost) {
		this.prevState = prevState;
		this.remainingTrips = remainingTrips;
		this.lastTrip = lastTrip;
		this.gCost = gCost;
	}


	public List<Trip> getSchedule() {
		List<Trip> schedule = new LinkedList<Trip>();
		State currState = this;
		while (currState.prevState != null) {
			schedule.add(0, currState.lastTrip);
			currState = currState.prevState;
		}

		return schedule;
	}

	public List<Trip> getRemainingTrips() {
		return this.remainingTrips;
	}
	public City getCurrCity() {
		return this.lastTrip.getDest();
	}
	public int getGCost() {
		return this.gCost;
	}
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
