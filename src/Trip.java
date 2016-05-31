public class Trip implements Comparable<Trip>{

	/**
	 * Creates a Trip with a source City and a destination City
	 * @param source the source City of the Trip
	 * @param dest the destination City of the Trip
	 */
	public Trip(City source, City dest) {
		this.source = source;
		this.dest = dest;
	}

	/**
	 * @return the source City of the Trip
	 */
	public City getSource() {
		return this.source;
	}

	/**
	 * @return the destination City of the Trip
	 */
	public City getDest() {
		return this.dest;
	}
	
	/**
	 * Determines the travel time between the source City and the destination City
	 * @return the travel time from the source City to the destination City
	 */
	public int getTravelTime() {
		if (this.source.equals(this.dest)) {
			return 0;
		} else {
			return this.source.getConnections().get(this.dest);
		}
	}
	
	/**
	 * Two Trips are equal if their source City are equal and their destination
	 * City are equal
	 */
	@Override
	public boolean equals(Object o) {
		if (o == null) {
			return false;
		}
		
		if (o instanceof Trip) {
			Trip other = (Trip) o;
			return this.source.equals(other.source) && this.dest.equals(other.dest);
		}
		
		return false;
	}
	
	@Override
	public int hashCode() {
		return this.source.hashCode() + this.dest.hashCode();
	}
	
	@Override
	public int compareTo(Trip t) {
		return this.getTravelTime() - t.getTravelTime();
	}
	
	private City source;
	private City dest;
}
