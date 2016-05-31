import java.util.Comparator;

public class StateComparator implements Comparator<State> {
 @Override
 public int compare(State s1, State s2) {
   return (s1.getGCost()) - (s2.getGCost());
 }
}
