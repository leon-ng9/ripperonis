
public class Util {
	public static Map map = new Map();
	public static ArrayList<Record> allRequests= new ArrayList<>();
	static public String toHTML(String s){
		String sub[] = s.split("\n");
		s = "<html>";
		for(String substr: sub){
			s += substr + "<br>";
		}
		return s + "</html>";
	}
}
