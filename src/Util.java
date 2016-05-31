
public class Util {
	static public String toHTML(String s){
		String sub[] = s.split("\n");
		s = "<html>";
		for(String substr: sub){
			s += substr + "<br>";
		}
		return s + "</html>";
	}
}
