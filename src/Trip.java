public class Trip implements Comparable<Trip>{

	public Trip(City source, City dest) {
		this.source = source;
		this.dest = dest;
	}

	public City getSource() {
		return this.source;
	}

	public City getDest() {
		return this.dest;
	}

	public int getTravelTime() {
		if (this.source.equals(this.dest)) {
			return 0;
		} else {
			return this.source.getConnections().get(this.dest);
		}
	}

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

	public String toString(){
		return this.dest.toString();
	}
	private City source;
	private City dest;
}
