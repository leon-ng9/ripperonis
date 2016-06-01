import java.util.ArrayList;

public class Util {
	public static TripPlanner map = new TripPlanner();

	public static ArrayList<Record> records = new ArrayList<>();
	public static ArrayList<Donor> donors = new ArrayList<>();

	public static Hospital hospital = new Hospital("Albert");
	public static Batmobile batmobile = new Batmobile("Jas", "London") ;

	static public String toHTML(String s){
		String sub[] = s.split("\n");
		s = "<html>";
		for(String substr: sub){
			s += substr + "<br>";
		}
		return s + "</html>";
	}
}
